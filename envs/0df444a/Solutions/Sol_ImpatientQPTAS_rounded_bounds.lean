-- Prove2me | solution 1 for ImpatientQPTAS.rounded_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:32:38.78455+00:00
-- url     : https://prove2.me/submissions/2d6beabc-b60a-4d82-ae19-afba0318a2b1

import Mathlib
import Definitions.Def_ImpatientQPTAS_Rounding

open ImpatientQPTAS in
theorem solution {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n) (i : Fin n)
    (hi : i ∈ Caverage ε I) :
    0 < pDown ε (I.p i) ∧ pDown ε (I.p i) ≤ I.p i ∧ I.p i ≤ pUp ε (I.p i) ∧
      pUp ε (I.p i) < 1 := by
  have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast i.pos
  simp only [Caverage, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨hlo, hhi⟩ := hi
  have hp0 : 0 < I.p i := lt_of_lt_of_le (by positivity) hlo
  have hεn : 0 < ε / (n:ℝ) := by positivity
  have hp1 : I.p i < 1 := by linarith
  have hδ : 0 < ε ^ 2 / 16 := by positivity
  have hb1 : 1 < 1 + ε ^ 2 / 16 := by linarith
  have hb0 : 0 < 1 + ε ^ 2 / 16 := by linarith
  have hD : ∀ y : ℝ, 0 < y → D (ε ^ 2 / 16) y ≤ y ∧ y < (1 + ε ^ 2 / 16) * D (ε ^ 2 / 16) y := by
    intro y hy
    unfold D
    have hl := Real.rpow_logb hb0 hb1.ne' hy
    rw [← Real.rpow_intCast]
    constructor
    · calc (1 + ε ^ 2 / 16) ^ ((⌊Real.logb (1 + ε ^ 2 / 16) y⌋ : ℤ) : ℝ)
          ≤ (1 + ε ^ 2 / 16) ^ (Real.logb (1 + ε ^ 2 / 16) y) :=
            Real.rpow_le_rpow_of_exponent_le hb1.le (Int.floor_le _)
        _ = y := hl
    · calc y = (1 + ε ^ 2 / 16) ^ (Real.logb (1 + ε ^ 2 / 16) y) := hl.symm
        _ < (1 + ε ^ 2 / 16) ^ (((⌊Real.logb (1 + ε ^ 2 / 16) y⌋ : ℤ) : ℝ) + 1) :=
            Real.rpow_lt_rpow_of_exponent_lt hb1 (Int.lt_floor_add_one _)
        _ = (1 + ε ^ 2 / 16) * (1 + ε ^ 2 / 16) ^ ((⌊Real.logb (1 + ε ^ 2 / 16) y⌋ : ℤ) : ℝ) := by
            rw [Real.rpow_add_one hb0.ne', mul_comm]
  have hU : ∀ y : ℝ, 0 < y → y ≤ U (ε ^ 2 / 16) y ∧ U (ε ^ 2 / 16) y < (1 + ε ^ 2 / 16) * y := by
    intro y hy
    unfold U
    have hl := Real.rpow_logb hb0 hb1.ne' hy
    rw [← Real.rpow_intCast]
    constructor
    · calc y = (1 + ε ^ 2 / 16) ^ (Real.logb (1 + ε ^ 2 / 16) y) := hl.symm
        _ ≤ (1 + ε ^ 2 / 16) ^ ((⌈Real.logb (1 + ε ^ 2 / 16) y⌉ : ℤ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb1.le (Int.le_ceil _)
    · calc (1 + ε ^ 2 / 16) ^ ((⌈Real.logb (1 + ε ^ 2 / 16) y⌉ : ℤ) : ℝ)
          < (1 + ε ^ 2 / 16) ^ (Real.logb (1 + ε ^ 2 / 16) y + 1) :=
            Real.rpow_lt_rpow_of_exponent_lt hb1 (Int.ceil_lt_add_one _)
        _ = (1 + ε ^ 2 / 16) * y := by rw [Real.rpow_add_one hb0.ne', hl, mul_comm]
  have hDpos : ∀ y : ℝ, 0 < D (ε ^ 2 / 16) y := fun y => by unfold D; positivity
  unfold pUp pDown
  by_cases hc : I.p i ≤ ε / 4
  · rw [if_pos hc, if_pos hc]
    obtain ⟨u1, u2⟩ := hU (I.p i) hp0
    refine ⟨div_pos (by linarith) hb0, ?_, u1, ?_⟩
    · rw [div_le_iff₀ hb0]
      linarith
    · nlinarith
  · rw [if_neg hc, if_neg hc]
    push_neg at hc
    obtain ⟨d1, d2⟩ := hD (1 - I.p i) (by linarith)
    have hd := hDpos (1 - I.p i)
    refine ⟨?_, by linarith, by linarith, by linarith⟩
    have h3 : (1 + ε ^ 2 / 16) * D (ε ^ 2 / 16) (1 - I.p i) ≤ (1 + ε ^ 2 / 16) * (1 - ε / 4) := by
      apply mul_le_mul_of_nonneg_left _ hb0.le
      linarith
    nlinarith
