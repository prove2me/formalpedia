-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.proj_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:06.961968+00:00
-- url     : https://prove2.me/submissions/520bfc81-cc7a-4ca0-8e8e-5c06b9325910

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_gau_zero
import Theorems.Thm_GlobalTheory_RealWeil_proj_heis_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) : proj h (proj h f) = proj h f := by
  have := proj_heis_proj hJ h 0 f
  rwa [h.1, gau_zero, one_smul] at this
end GlobalTheory.RealWeil.Osc
