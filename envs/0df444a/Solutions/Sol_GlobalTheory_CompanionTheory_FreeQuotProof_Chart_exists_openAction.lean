-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.exists_openAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:21.395805+00:00
-- url     : https://prove2.me/submissions/af90e26d-07b9-471d-a99c-3c0334411f6e

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
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
variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution (V : X.left.Opens)
    (hst : (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V) :
    ∃ _ : ModObj G (Over.mk (V.ι ≫ X.hom)),
      (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)) ≫
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) =
      G ◁ (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ γ[G, X] := by
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let m : Z ⟶ X := Over.homMk V.ι rfl
  have : Mono m.left := inferInstanceAs (Mono V.ι)
  have : Mono m := Over.mono_of_mono_left m
  let u : G ⊗ Z ⟶ X := G ◁ m ≫ γ[G, X]
  have hu : Set.range u.left ⊆ Set.range V.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h1 : (G ◁ m).left p ∈ (snd G X).left ⁻¹ᵁ V := by
      change (snd G X).left ((G ◁ m).left p) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerLeft_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact ((snd G Z).left p).2
    rw [← hst] at h1
    simpa [u, Scheme.Hom.comp_apply] using h1
  let t : G ⊗ Z ⟶ Z := Over.homMk (IsOpenImmersion.lift V.ι u.left hu) (by
    change IsOpenImmersion.lift V.ι u.left hu ≫ V.ι ≫ X.hom = _
    rw [IsOpenImmersion.lift_fac_assoc]
    exact Over.w u)
  have ht : t ≫ m = u := by
    ext1
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ smul := t, one_smul := ?_, mul_smul := ?_ }, ht⟩
  · apply (cancel_mono m).1
    change (η[G] ▷ Z ≫ t) ≫ m = (λ_ Z).hom ≫ m
    rw [Category.assoc, ht]
    simp only [u]
    rw [← whisker_exchange_assoc, ModObj.one_smul_self, leftUnitor_naturality]
  · apply (cancel_mono m).1
    change (μ[G] ▷ Z ≫ t) ≫ m = ((α_ G G Z).hom ≫ G ◁ t ≫ t) ≫ m
    simp only [Category.assoc, ht]
    simp only [u]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self, ← whiskerLeft_comp_assoc, ht]
    simp only [u, whiskerLeft_comp, Category.assoc]
    rw [associator_naturality_right_assoc]
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
