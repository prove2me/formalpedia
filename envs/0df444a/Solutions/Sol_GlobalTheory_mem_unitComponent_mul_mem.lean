-- Prove2me | solution 1 for GlobalTheory.mem_unitComponent_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:18.902973+00:00
-- url     : https://prove2.me/submissions/a102ac1b-8409-4105-b175-b02fd76e1c16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMem
import Theorems.Thm_GlobalTheory_overPullback_unit_comp_fst
import Theorems.Thm_GlobalTheory_T_exists_mem_rightTranslate_mem_identityComponent
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
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left),
      (η[G]).left (G.hom y) ∈ U →
      y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} →
      y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hsm U y hU hy
  let K := ↑(G.left.residueField y)
  let ω : Spec (CommRingCat.of K) ⟶ G.left := G.left.fromSpecResidueField y
  have hω : ∀ t, ω t = y := fun t => Scheme.fromSpecResidueField_apply y t
  let p : Spec (CommRingCat.of K) ⟶ S := ω ≫ G.hom
  let P := Over.pullback p
  let G' : Over (Spec (CommRingCat.of K)) := P.obj G
  let q : G'.left ⟶ G.left := pullback.fst G.hom p
  have hsm' : Smooth G'.hom := by
    show Smooth (pullback.snd G.hom p); infer_instance
  let y' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G' :=
    Over.homMk (pullback.lift ω (𝟙 _) (by simp [p])) (pullback.lift_snd _ _ _)
  have hy'q : y'.left ≫ q = ω := pullback.lift_fst _ _ _
  have heq : (η[G']).left ≫ q = p ≫ (η[G]).left := overPullback_unit_comp_fst p G
  have hZ := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback G.left S G'.left (Spec (CommRingCat.of K)) G.hom G'.hom p q (η[G]).left (η[G']).left hsm
    (IsPullback.of_hasPullback G.hom p) (Over.w η[G]) (Over.w η[G']) heq
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hy'Z : y'.left pt ∈ connectedComponent ((η[G']).left pt) := by
    have h1 : y'.left pt ∈ q ⁻¹' {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hy'q, hω]; exact hy
    rw [hZ] at h1
    have h2 : G'.hom ⁻¹' {G'.hom (y'.left pt)} = Set.univ := by
      ext t; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    have h3 : G'.hom (y'.left pt) = pt := Subsingleton.elim _ _
    have h1' : y'.left pt ∈ connectedComponentIn (G'.hom ⁻¹' {G'.hom (y'.left pt)}) ((η[G']).left (G'.hom (y'.left pt))) := h1
    rwa [h2, h3, connectedComponentIn_univ] at h1'
  have hU' : (η[G']).left pt ∈ q ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
    have : p pt = G.hom y := by
      show G.hom (ω pt) = _
      rw [hω]
    rw [this]; exact hU
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent K G' hsm' (q ⁻¹ᵁ U) y' hU' hy'Z
  let L : G' ⟶ P.obj (G ⊗ G) := lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G
  have hmap : ∀ {A B : Over S} (f : A ⟶ B), (P.map f).left ≫ pullback.fst B.hom p = pullback.fst A.hom p ≫ f.left := by
    intro A B f; simp [P]; exact pullback.lift_fst _ _ _
  have key : ∀ (M : G' ⟶ P.obj (G ⊗ G)) {B : Over S} (f : G ⊗ G ⟶ B),
      f.left (pullback.fst (G ⊗ G).hom p (M.left z)) = pullback.fst B.hom p ((M ≫ P.map f).left z) := by
    intro M B f
    rw [Over.comp_left, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.fst B.hom p), hmap,
      Scheme.Hom.comp_apply]
  refine ⟨pullback.fst (G ⊗ G).hom p (L.left z), ?_, ?_, ?_⟩
  · rw [key L]
    have : L ≫ P.map (fst G G) = 𝟙 G' := by
      show (lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G) ≫ _ = _
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
    rw [this, Over.id_left]; exact (Scheme.Hom.mem_preimage _).1 hz1
  · rw [key L]
    have : L ≫ P.map μ[G] = 𝟙 G' * (toUnit G' ≫ y') := by
      show (lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G) ≫ _ = _
      rw [Category.assoc]; rfl
    rw [this]; exact (Scheme.Hom.mem_preimage _).1 hz2
  · rw [key L]
    have : L ≫ P.map (snd G G) = toUnit G' ≫ y' := by
      show (lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G) ≫ _ = _
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
    rw [this]
    rw [Over.comp_left, ← Scheme.Hom.comp_apply, Category.assoc]
    show ((toUnit G').left ≫ y'.left ≫ q) z = y
    rw [hy'q]; exact hω _
end GlobalTheory
