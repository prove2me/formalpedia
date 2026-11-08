-- Prove2me | solution 1 for ImpatientQPTAS.rRound_band
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:07:21.046978+00:00
-- url     : https://prove2.me/submissions/79542bf5-920e-49c6-99f9-dbf144cc29ed

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

open ImpatientQPTAS in
theorem solution {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (i : Fin n) :
    0 ≤ rRound ε n (rmax r) (r i) ∧ rRound ε n (rmax r) (r i) ≤ r i ∧
      r i / (1 + ε) - ε / (n : ℝ) * rmax r ≤ rRound ε n (rmax r) (r i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have hrm : rmax r = Finset.univ.sup' hne r := by
    unfold rmax ImpatientQPTAS.maxOn
    rw [dif_pos hne]
  have hle : r i ≤ rmax r := by
    rw [hrm]; exact Finset.le_sup' r (Finset.mem_univ i)
  have hx0 := hr i
  have hrm0 : 0 ≤ rmax r := le_trans hx0 hle
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hthr0 : 0 ≤ ε / (n : ℝ) * rmax r := mul_nonneg (div_nonneg h0.le hn) hrm0
  unfold rRound
  split_ifs with hcase
  · refine ⟨le_refl 0, hx0, ?_⟩
    have : r i / (1 + ε) ≤ r i := div_le_self hx0 (by linarith)
    linarith
  · push_neg at hcase
    set x := r i with hxdef
    set rm := rmax r with hrmdef
    have hxpos : 0 < x := lt_of_le_of_lt hthr0 hcase
    have hrmpos : 0 < rm := lt_of_lt_of_le hxpos hle
    have hb : 1 < 1 + ε := by linarith
    set L := Real.logb (1 + ε) (rm / x) with hL
    have hpowL : (1 + ε) ^ (-L) = x / rm := by
      rw [Real.rpow_neg (by linarith), hL, Real.rpow_logb (by linarith) hb.ne' (by positivity),
        inv_div]
    have hz : (1 + ε) ^ (-⌈L⌉) = (1 + ε) ^ ((-⌈L⌉ : ℤ) : ℝ) := (Real.rpow_intCast _ _).symm
    have hup : (1 + ε) ^ ((-⌈L⌉ : ℤ) : ℝ) ≤ (1 + ε) ^ (-L) := by
      apply Real.rpow_le_rpow_of_exponent_le hb.le
      push_cast
      linarith [Int.le_ceil L]
    have hlow : (1 + ε) ^ (-L - 1) ≤ (1 + ε) ^ ((-⌈L⌉ : ℤ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hb.le
      push_cast
      linarith [Int.ceil_lt_add_one L]
    have hlow' : (1 + ε) ^ (-L - 1) = x / rm / (1 + ε) := by
      rw [Real.rpow_sub_one (by linarith), hpowL]
    rw [hz]
    have hpos : 0 < (1 + ε) ^ ((-⌈L⌉ : ℤ) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    refine ⟨by positivity, ?_, ?_⟩
    · calc rm * (1 + ε) ^ ((-⌈L⌉ : ℤ) : ℝ) ≤ rm * (x / rm) := by
            rw [← hpowL]; exact mul_le_mul_of_nonneg_left hup hrmpos.le
        _ = x := by field_simp
    · have h1 : rm * (x / rm / (1 + ε)) ≤ rm * (1 + ε) ^ ((-⌈L⌉ : ℤ) : ℝ) := by
        rw [← hlow']; exact mul_le_mul_of_nonneg_left hlow hrmpos.le
      have h2 : rm * (x / rm / (1 + ε)) = x / (1 + ε) := by field_simp
      linarith
