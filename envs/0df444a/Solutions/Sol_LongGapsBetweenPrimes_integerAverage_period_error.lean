-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_period_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:45.382009+00:00
-- url     : https://prove2.me/submissions/cfcb160e-17ab-4d5f-b38e-19582406d3a2

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_residue_average_bounded_error
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_complete_residues

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m q T : ℕ} (hm : 0 < m) (hq : 0 < q) (hT : 0 < T)
    (hmq : m ∣ q) (f : ℕ → ℝ) (hperiod : ∀ n, f (n % m) = f n) (hf : ∀ n, |f n| ≤ 1) :
    |integerAverage T f - integerAverage q f| ≤ (m : ℝ) / T := by
  simpa only [← integerAverage_complete_residues hm hq hmq, hperiod] using
    residue_average_bounded_error hm hT (fun a => f a) (fun a => hf a)
end LongGapsBetweenPrimes
