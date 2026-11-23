-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.k_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:52.872809+00:00
-- url     : https://prove2.me/submissions/01ed7d4b-c7b0-4f8b-8e10-3036f9ad3eec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_k_mul

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
variable {T : B →L[ℂ] B}
variable {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (k : G →* (V →L[ℝ] V)) (g : G) (v : V) : k g (k g⁻¹ v) = v := by
  rw [← k_mul, mul_inv_cancel, map_one]; rfl
end GlobalTheory.RealWeil.Osc
