-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.sm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:26.545959+00:00
-- url     : https://prove2.me/submissions/07874b0d-2531-4c30-8236-ae41237dfce5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings

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
theorem _root_.solution (a : ℂ) {f : B} (hf : Sm ρ f) : Sm ρ (a • f) := by
  simpa only [Sm, map_smul] using ContDiff.const_smul a hf
end GlobalTheory.RealWeil.Osc
