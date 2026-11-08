-- Prove2me | solution 1 for NestedLogitNBR.prefix_average_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:03:18.778217+00:00
-- url     : https://prove2.me/submissions/604420d4-09b5-4ca6-8645-b42c8776bfeb

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_revSum

open NestedLogitNBR in
theorem solution {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hord : Antitone (r i)) (k : Fin n)
    (hq : 0 < prefWeight v i (nbr k.val)) :
    AntitoneOn (fun ρ : ℝ => (revSum r v i k.val + r i k * v i k * ρ) /
      (prefWeight v i (nbr k.val) + v i k * ρ)) (Set.Icc 0 1) := by
  have hA : r i k * prefWeight v i (nbr k.val) ≤ revSum r v i k.val := by
    unfold prefWeight revSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hlk : l < k := Fin.lt_iff_val_lt_val.mpr (Finset.mem_filter.mp hl).2
    exact mul_le_mul_of_nonneg_right (hord hlk.le) (hv l)
  intro ρ1 h1 ρ2 h2 h12
  have hd1 : 0 < prefWeight v i (nbr k.val) + v i k * ρ1 := by
    have := mul_nonneg (hv k) h1.1; linarith
  have hd2 : 0 < prefWeight v i (nbr k.val) + v i k * ρ2 := by
    have := mul_nonneg (hv k) h2.1; linarith
  show (revSum r v i k.val + r i k * v i k * ρ2) / (prefWeight v i (nbr k.val) + v i k * ρ2) ≤
    (revSum r v i k.val + r i k * v i k * ρ1) / (prefWeight v i (nbr k.val) + v i k * ρ1)
  rw [div_le_div_iff₀ hd2 hd1]
  nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg (sub_nonneg.mpr h12) (hv k))]
