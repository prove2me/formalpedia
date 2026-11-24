-- Prove2me | solution 1 for GlobalTheory.HCA.integrable_mul_of_continuousOn_of_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:36.673518+00:00
-- url     : https://prove2.me/submissions/d2be4703-05c6-4e9a-aa0d-a0e3cf1b033c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hcont : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hgU h)
      have h0 : (fun x => f x * g x) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact continuousAt_const.congr h0.symm
  exact hcont.integrable_of_hasCompactSupport (hgc.mul_left)
end GlobalTheory.HCA
