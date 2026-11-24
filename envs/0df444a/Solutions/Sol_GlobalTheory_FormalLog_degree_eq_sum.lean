-- Prove2me | solution 1 for GlobalTheory.FormalLog.degree_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:10.22595+00:00
-- url     : https://prove2.me/submissions/c0519601-90b4-4030-ac66-a30e488389b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]
namespace GlobalTheory.FormalLog
theorem _root_.solution (n : τ →₀ ℕ) : n.degree = ∑ w, n w := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => by simpa using hw)
end GlobalTheory.FormalLog
