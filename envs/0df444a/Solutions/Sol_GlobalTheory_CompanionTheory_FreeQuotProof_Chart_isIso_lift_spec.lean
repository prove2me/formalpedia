-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.isIso_lift_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:35:55.442114+00:00
-- url     : https://prove2.me/submissions/cb2a6142-febe-4c72-ad29-9dab76594b17

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
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution {Λ B : Type} [CommRing Λ] [Algebra R Λ] [CommRing B] [Algebra R B]
    {H Z : Over (Spec (CommRingCat.of R))} (e : specOver R Λ ≅ H) (v : specOver R B ≅ Z) :
    IsIso (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)) := by
  have P₂ : IsPullback (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ)).left
      (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ)).left (specOver R B).hom (specOver R Λ).hom :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B Λ)
  have P₃ : IsPullback (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom).left
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom).left H.hom Z.hom :=
    P₂.flip.of_iso (Iso.refl _) ((Over.forget _).mapIso e) ((Over.forget _).mapIso v) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have P₄ : IsPullback (fst H Z).left (snd H Z).left H.hom Z.hom :=
    IsPullback.of_hasPullback H.hom Z.hom
  have e₁ : (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)).left = (P₃.isoIsPullback _ _ P₄).hom := by
    apply P₄.hom_ext
    · rw [IsPullback.isoIsPullback_hom_fst, ← Over.comp_left, lift_fst]
    · rw [IsPullback.isoIsPullback_hom_snd, ← Over.comp_left, lift_snd]
  have : IsIso (Over.forget _ |>.map (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom))) := by
    have hl : IsIso (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)).left := by
      rw [e₁]; infer_instance
    exact hl
  exact isIso_of_reflects_iso _ (Over.forget _)
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
