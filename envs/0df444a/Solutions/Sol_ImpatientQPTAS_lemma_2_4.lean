-- Prove2me | solution 1 for ImpatientQPTAS.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:48:04.205709+00:00
-- url     : https://prove2.me/submissions/9f6a8ead-a88f-4c5b-bee1-7ec5dbbce3f8

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS.Aux_L24

theorem U_le {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    0 < (1 + δ) ^ ⌈Real.logb (1 + δ) x⌉ ∧ (1 + δ) ^ ⌈Real.logb (1 + δ) x⌉ ≤ x * (1 + δ) := by
  have hb : 1 < 1 + δ := by linarith
  refine ⟨zpow_pos (by linarith) _, ?_⟩
  rw [← Real.rpow_intCast]
  calc (1 + δ) ^ ((⌈Real.logb (1 + δ) x⌉ : ℤ) : ℝ) ≤ (1 + δ) ^ (Real.logb (1 + δ) x + 1) :=
        Real.rpow_le_rpow_of_exponent_le hb.le (Int.ceil_lt_add_one _).le
    _ = x * (1 + δ) := by
        rw [Real.rpow_add_one (by linarith), Real.rpow_logb (by linarith) hb.ne' hx]

theorem D_le {δ y : ℝ} (hδ : 0 < δ) (hy : 0 < y) :
    0 < (1 + δ) ^ ⌊Real.logb (1 + δ) y⌋ ∧ (1 + δ) ^ ⌊Real.logb (1 + δ) y⌋ ≤ y := by
  have hb : 1 < 1 + δ := by linarith
  refine ⟨zpow_pos (by linarith) _, ?_⟩
  rw [← Real.rpow_intCast]
  calc (1 + δ) ^ ((⌊Real.logb (1 + δ) y⌋ : ℤ) : ℝ) ≤ (1 + δ) ^ (Real.logb (1 + δ) y) :=
        Real.rpow_le_rpow_of_exponent_le hb.le (Int.floor_le _)
    _ = y := Real.rpow_logb (by linarith) hb.ne' hy

/-- `b ^ (-ε) ≥ 1 + ε (1 - b)` for `0 < b`. -/
theorem rpow_neg_ge {b ε : ℝ} (hb : 0 < b) (hε : 0 ≤ ε) : 1 + ε * (1 - b) ≤ b ^ (-ε) := by
  rw [Real.rpow_def_of_pos hb]
  have h1 := Real.add_one_le_exp (Real.log b * (-ε))
  have h2 : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hb
  nlinarith

theorem pow_ge {y Δ ε : ℝ} (hy : 0 < y) (hΔ : 0 ≤ Δ) (h : Δ * (1 / y - 1) ≤ ε) :
    1 - ε ≤ y ^ Δ := by
  rw [Real.rpow_def_of_pos hy]
  have h1 := Real.add_one_le_exp (Real.log y * Δ)
  have h2 : 1 - 1 / y ≤ Real.log y := by
    have := Real.one_sub_inv_le_log_of_pos hy
    rwa [one_div]
  have h3 : -(Δ * (1 / y - 1)) ≤ Real.log y * Δ := by nlinarith
  linarith

end ImpatientQPTAS.Aux_L24

open ImpatientQPTAS ImpatientQPTAS.Aux_L24 in
theorem solution {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n) (i : Fin n)
    (hi : i ∈ Caverage ε I) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ < 1 / ε) :
    (1 - ε) * (1 - pDown ε (I.p i)) ^ Δ ≤ (1 - pUp ε (I.p i)) ^ Δ := by
  have hn : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
    exact_mod_cast this
  simp only [Caverage, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨hlo, hhi⟩ := hi
  set x := I.p i with hxdef
  set δ := ε ^ 2 / 16 with hδ
  have hδ0 : 0 < δ := by positivity
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hlo
  have hεn1 : ε / (n : ℝ) ≤ ε := div_le_self h0.le hn
  have hεn : 0 < ε / (n : ℝ) := by positivity
  have hΔε : Δ * ε ≤ 1 := by
    have := (lt_div_iff₀ h0).mp hΔ1
    linarith
  have hΔδ : Δ * δ ≤ ε := by
    rw [hδ]
    have : Δ * (ε ^ 2 / 16) = (Δ * ε) * (ε / 16) := by ring
    rw [this]
    have h16 : ε / 16 ≤ ε := by linarith
    nlinarith
  -- reduction
  suffices key : ∃ a y : ℝ, 0 < a ∧ 0 < y ∧ 1 - pDown ε x = a ∧ 1 - pUp ε x = a * y ∧
      Δ * (1 / y - 1) ≤ ε by
    obtain ⟨a, y, ha, hy, hA, hB, hyε⟩ := key
    rw [hA, hB, Real.mul_rpow ha.le hy.le]
    have := pow_ge hy hΔ0 hyε
    have hapos : 0 ≤ a ^ Δ := Real.rpow_nonneg ha.le _
    nlinarith
  by_cases hx4 : x ≤ ε / 4
  · simp only [pUp, pDown, if_pos hx4]
    unfold U
    obtain ⟨hu0, hu1⟩ := U_le hδ0 hxpos
    set u := (1 + ε ^ 2 / 16) ^ ⌈Real.logb (1 + ε ^ 2 / 16) x⌉ with hu
    rw [← hδ]
    have hδs : δ ≤ 1 / 256 := by rw [hδ]; nlinarith
    have hu2 : u ≤ 1 / 2 := by nlinarith
    have hapos : 0 < 1 - u / (1 + δ) := by
      have : u / (1 + δ) ≤ u := div_le_self hu0.le (by linarith)
      linarith
    refine ⟨1 - u / (1 + δ), (1 - u) / (1 - u / (1 + δ)), hapos, by
      apply div_pos (by linarith) hapos, rfl, by rw [mul_div_assoc', mul_div_cancel_left₀ _ hapos.ne'], ?_⟩
    have e : 1 / ((1 - u) / (1 - u / (1 + δ))) - 1 = u * δ / ((1 + δ) * (1 - u)) := by
      have : (1 - u) ≠ 0 := by linarith
      field_simp <;> ring
    rw [e]
    have hb : u * δ / ((1 + δ) * (1 - u)) ≤ δ := by
      have hpos1 : 0 < (1 + δ) * (1 - u) := by nlinarith
      rw [div_le_iff₀ hpos1]
      have h' : u ≤ (1 + δ) * (1 - u) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h' hδ0.le]
    have := mul_le_mul_of_nonneg_left hb hΔ0
    linarith
  · push_neg at hx4
    simp only [pUp, pDown, if_neg (not_le.mpr hx4)]
    unfold D
    have hy : 0 < 1 - x := by linarith
    obtain ⟨hd0, hd1⟩ := D_le hδ0 hy
    set d := (1 + ε ^ 2 / 16) ^ ⌊Real.logb (1 + ε ^ 2 / 16) (1 - x)⌋ with hd
    rw [← hδ]
    refine ⟨(1 + δ) * d, 1 / (1 + δ), by positivity, by positivity, by ring, by
      field_simp <;> ring, ?_⟩
    rw [one_div_one_div, add_sub_cancel_left]
    exact hΔδ
