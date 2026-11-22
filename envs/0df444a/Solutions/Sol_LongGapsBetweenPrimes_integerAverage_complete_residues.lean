-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_complete_residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:05.180373+00:00
-- url     : https://prove2.me/submissions/8c3363fd-30ff-471b-8aac-52181a8538b8

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_residue_expansion

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hmq : m ∣ q) (g : Fin m → ℝ) :
    integerAverage q (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) = Finset.expect Finset.univ g := by
  rw [integerAverage_residue_expansion hm, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hcount : ((Finset.range q).filter fun n => n % m = a.val).card = q / m := by
    simpa [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_zero_of_dvd hmq] using Nat.count_modEq_card q hm a.val
  simp only [residueIndicator, Finset.sum_boole, hcount,
    Nat.cast_div hmq (by positivity : (m : ℝ) ≠ 0)]
  field_simp
end LongGapsBetweenPrimes
