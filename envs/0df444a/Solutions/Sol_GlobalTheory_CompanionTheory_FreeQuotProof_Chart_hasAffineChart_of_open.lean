-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:24.71897+00:00
-- url     : https://prove2.me/submissions/e682c64a-7571-4cb2-9cd8-8e8ee59d690a

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
    (hst : (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V)
    [ModObj G (Over.mk (V.ι ≫ X.hom))]
    (hm : (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)) ≫
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) =
      G ◁ (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ γ[G, X])
    (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (hY : IsAffine Y) (h₁ : IsFinite q) (h₂ : Flat q)
    (h₃ : LocallyOfFinitePresentation q) (h₄ : Surjective q)
    (pb : IsPullback (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)).left
      (snd G (Over.mk (V.ι ≫ X.hom))).left q q) :
    HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let m : Z ⟶ X := Over.homMk V.ι rfl
  have P : IsPullback (G ◁ m) (snd G Z) (snd G X) m := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst G X) s.snd) ?_ ?_ ?_⟩⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using s.condition.symm
    · intro s
      simp
    · intro s t h1 h2
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, ← h1]; simp
      · rw [lift_snd, h2]
  have P' : IsPullback (G ◁ m).left (snd G Z).left (snd G X).left V.ι := P.map (Over.forget S)
  have Q := (isPullback_morphismRestrict (snd G X).left V).flip
  let ε := P'.isoIsPullback _ _ Q
  have hε₁ : ε.inv ≫ (G ◁ m).left = ((snd G X).left ⁻¹ᵁ V).ι := P'.isoIsPullback_inv_fst _ _ Q
  have hε₂ : ε.inv ≫ (snd G Z).left = (snd G X).left ∣_ V := P'.isoIsPullback_inv_snd _ _ Q
  refine ⟨hst, Y, q, ε.inv ≫ (γ[G, Z] : G ⊗ Z ⟶ Z).left, hY, h₁, h₂, h₃, h₄, ?_, ?_⟩
  · have h := congr(($hm).left)
    rw [Over.comp_left, Over.comp_left] at h
    rw [Category.assoc]
    refine (congrArg (ε.inv ≫ ·) h).trans ?_
    rw [← Category.assoc, hε₁]
  · refine pb.of_iso ε (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp
    · rw [← hε₂, ε.hom_inv_id_assoc]; exact Category.comp_id _
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
