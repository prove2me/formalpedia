-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:58.756826+00:00
-- url     : https://prove2.me/submissions/2b95de43-2275-48ce-951f-7e93ea67bd92

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_affine_chart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_exists_openAction
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_hasAffineChart_of_open
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_baseChange_compare
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_baseChange_free
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory.AffineQuotient
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Chart
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X],
    IsFiniteLocallyFree G.hom → IsFreeAction G X → ∀ (V : X.left.Opens) (W : S.Opens),
    IsAffineOpen V → IsAffineOpen W → V ≤ X.hom ⁻¹ᵁ W →
    (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V →
    HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  intro S G X _ _ hG hf V W hV hW hVW hst
  obtain ⟨_, hm⟩ := exists_openAction G X V hst
  let j : Spec (CommRingCat.of Γ(S, W)) ⟶ S := hW.fromSpec
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let m : Z ⟶ X := Over.homMk V.ι rfl
  have : Mono m.left := inferInstanceAs (Mono V.ι)
  have : Mono m := Over.mono_of_mono_left m
  have hZ : Set.range Z.hom ⊆ Set.range j := by
    rintro _ ⟨v, rfl⟩
    rw [show Set.range j = W from hW.range_fromSpec]
    exact hVW v.2
  let z := IsOpenImmersion.lift j Z.hom hZ
  have hz : z ≫ j = Z.hom := IsOpenImmersion.lift_fac j Z.hom hZ
  have hfZ : IsFreeAction G Z := by
    intro T g x e
    refine hf T g (x ≫ m) ?_
    have e₁ : g • (x ≫ m) = (g • x) ≫ m := by
      rw [Hom.smul_def, Hom.smul_def, Category.assoc, hm, ← Category.assoc, lift_whiskerLeft]
    rw [e₁, e]
  letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
  letI := modObjObj (Over.pullback j) G Z
  obtain ⟨hi, e, he₁, he₂⟩ := baseChange_compare j G Z z hz
  have hfZ' := baseChange_free j G Z hfZ
  have hH : IsFiniteLocallyFree ((Over.pullback j).obj G).hom := by
    obtain ⟨a, b, c⟩ := hG
    exact ⟨inferInstanceAs (IsFinite (pullback.snd G.hom j)),
      inferInstanceAs (Flat (pullback.snd G.hom j)),
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.hom j))⟩
  have : IsAffine ((Over.pullback j).obj Z).left := by
    have : IsAffine Z.left := hV
    exact IsAffine.of_isIso (pullback.fst Z.hom j)
  obtain ⟨Y, q', a1, a2, a3, a4, a5, pb⟩ := affine_chart _ _ hH hfZ'
  refine hasAffineChart_of_open G X V hst hm Y (inv (pullback.fst Z.hom j) ≫ q') a1 (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance) ?_
  refine pb.of_iso e (asIso (pullback.fst Z.hom j)) (asIso (pullback.fst Z.hom j)) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact he₁.symm
  · exact he₂.symm
  · simp
  · simp
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
