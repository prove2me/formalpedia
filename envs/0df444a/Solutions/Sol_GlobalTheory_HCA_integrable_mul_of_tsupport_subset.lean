-- Prove2me | solution 1 for GlobalTheory.HCA.integrable_mul_of_tsupport_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:37.445678+00:00
-- url     : https://prove2.me/submissions/3c13ad25-c311-4c2e-904f-977408f52d2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hc : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hs h)
      have h0 : (fun x => f x * g x) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).1 hx'] with y hy
        simp [hy]
      exact (continuousAt_congr h0).2 continuousAt_const
  exact hc.integrable_of_hasCompactSupport hgc.mul_left
end GlobalTheory.HCA
