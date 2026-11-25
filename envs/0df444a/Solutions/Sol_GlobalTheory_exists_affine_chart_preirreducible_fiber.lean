-- Prove2me | solution 1 for GlobalTheory.exists_affine_chart_preirreducible_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:12.606021+00:00
-- url     : https://prove2.me/submissions/e3165afa-3a1e-4a4e-86e1-31c16c23b86c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiber
import Theorems.Thm_GlobalTheory_exists_open_inter_fiber_subset_sectionComponent
import Theorems.Thm_GlobalTheory_T_isOpen_isIrreducible_componentOfRationalPoint_smooth
import Theorems.Thm_GlobalTheory_T_preimage_section_connectedComponentIn_of_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  intro X S f e hf he s
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨W₁, hW₁, hW₁'⟩ := exists_open_inter_fiber_subset_sectionComponent X S f e hf he s
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hmem : e s ∈ ((W₁ ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) := ⟨hW₁, by
    change f (e s) ∈ (V : Set S)
    rw [hes]; exact hsV⟩
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hsW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hmem (W₁ ⊓ f ⁻¹ᵁ V).isOpen
  refine ⟨V, W, fun x hx => (hle hx).2, hV, hW, hsW, ?_⟩
  intro k _ p hp
  let e' : Spec (CommRingCat.of k) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'' : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  have h1 := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S _ _ f (pullback.snd f p) p (pullback.fst f p) e e' hf
    (IsPullback.of_hasPullback f p) he he' he''
  have h2 := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k _ (pullback.snd f p) e' inferInstance he').2
  rw [← h1] at h2
  let j : pullback (W.ι ≫ f) p ⟶ pullback f p :=
    pullback.map _ _ _ _ W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hj : IsOpenImmersion j := inferInstance
  have hjf : j ≫ pullback.fst f p = pullback.fst _ _ ≫ W.ι := pullback.lift_fst _ _ _
  have h3 := h2.isPreirreducible.preimage j.isOpenEmbedding
  constructor
  convert h3 using 1
  symm
  rw [Set.eq_univ_iff_forall]
  intro y
  have hx : f (pullback.fst f p (j y)) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hp]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  change pullback.fst f p (j y) ∈ connectedComponentIn (f ⁻¹' {f (pullback.fst f p (j y))})
    (e (f (pullback.fst f p (j y))))
  rw [hx]
  refine hW₁' _ ?_ hx
  rw [← Scheme.Hom.comp_apply, hjf, Scheme.Hom.comp_apply]
  exact (hle (pullback.fst (W.ι ≫ f) p y).2).1
end GlobalTheory
