-- Prove2me | solution 1 for GlobalTheory.UnitaryCayley.trace_Hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:11.411723+00:00
-- url     : https://prove2.me/submissions/69e420d0-337f-4dbd-a9e9-e6fde585736b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley
namespace GlobalTheory.UnitaryCayley
theorem _root_.solution (k r : ℕ) : (Hpk k r).trace = (k : ℂ) - 1 := by
  unfold Matrix.trace
  have h : ∀ i : Fin (2 * r + k + 1), Matrix.diag (Hpk k r) i =
      (fun m : ℕ => (if r ≤ m ∧ m < r + k then (1 : ℂ) else 0) - (if m = r + k then 1 else 0)) i.val := by
    intro i
    have := i.isLt
    simp only [Matrix.diag, Hpk, and_true]
    split_ifs <;> first | omega | simp
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => (if r ≤ m ∧ m < r + k then (1 : ℂ) else 0) -
    (if m = r + k then 1 else 0)), Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_boole]
  have : (range (2 * r + k + 1)).filter (fun m => r ≤ m ∧ m < r + k) = Finset.Ico r (r + k) := by
    ext m; simp only [mem_filter, mem_range, Finset.mem_Ico]; omega
  rw [this, if_pos (by simp only [mem_range]; omega)]
  simp
end GlobalTheory.UnitaryCayley
