-- Prove2me | solution 1 for GlobalTheory.HCA.SolSub.contDiff_mul_of_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:05.966931+00:00
-- url     : https://prove2.me/submissions/349325cd-bac4-4f7c-add5-9d0412798736

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset

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
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolSub
variable {d : ℕ}
namespace GlobalTheory.HCA.SolSub
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) {b φ : E d → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : φ =ᶠ[nhds x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have : (fun y => b y * φ y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this
end GlobalTheory.HCA.SolSub
