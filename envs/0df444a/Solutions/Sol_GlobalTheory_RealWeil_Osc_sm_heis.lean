-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.sm_heis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:10.134097+00:00
-- url     : https://prove2.me/submissions/f2d067f8-c4b0-4e6b-af74-286ba7002faa

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
theorem _root_.solution (h : IsHeis (omJ J) ρ) (a : V) {f : B} (hf : Sm ρ f) : Sm ρ (ρ a f) := by
  unfold Sm
  simp only [h.2.1]
  refine ContDiff.smul (Complex.contDiff_exp.comp (contDiff_const.mul ?_)) (ContDiff.comp hf (contDiff_id.add contDiff_const))
  exact Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)
end GlobalTheory.RealWeil.Osc
