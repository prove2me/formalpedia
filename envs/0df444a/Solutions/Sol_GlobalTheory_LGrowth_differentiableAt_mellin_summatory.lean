-- Prove2me | solution 1 for GlobalTheory.LGrowth.differentiableAt_mellin_summatory
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:05.137148+00:00
-- url     : https://prove2.me/submissions/cfbda15f-ff4c-4d35-9498-776aa8b5ba82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
import Theorems.Thm_GlobalTheory_LGrowth_measurable_summatory
import Theorems.Thm_GlobalTheory_LGrowth_summatory_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LGrowth
open Filter Topology Asymptotics
variable {f : ℕ → ℂ} {C : ℝ}
namespace GlobalTheory.LGrowth
theorem _root_.solution (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (summatory f) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (summatory f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)
    · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
      simpa [summatory] using hC ⌊t⌋₊
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      simp [summatory_eq_zero ht]
    · simp
  exact h.comp s differentiableAt_id.neg
end GlobalTheory.LGrowth
