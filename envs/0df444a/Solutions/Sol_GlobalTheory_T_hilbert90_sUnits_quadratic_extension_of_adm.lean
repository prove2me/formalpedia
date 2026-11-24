-- Prove2me | solution 1 for GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:39.458738+00:00
-- url     : https://prove2.me/submissions/26f3cd53-015d-4fa0-af6d-2eb6c5f1c613

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtensionStatement
import Theorems.Thm_GlobalTheory_QNorm_hilbert90_sUnits_quadratic_extension_qnorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → admitted F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → (u : E) * σ u = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = y / σ y := by
  first | exact @GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm | exact GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm | (intros; apply GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm <;> assumption)
end _root_.GlobalTheory.T
