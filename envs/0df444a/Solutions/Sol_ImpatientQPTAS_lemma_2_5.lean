-- Prove2me | solution 1 for ImpatientQPTAS.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:34:14.27805+00:00
-- url     : https://prove2.me/submissions/45c4fa2d-c2df-4672-a224-8e77b50eab4a

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS.Aux_L25

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

end ImpatientQPTAS.Aux_L25

open ImpatientQPTAS ImpatientQPTAS.Aux_L25 in
theorem solution {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n) (i : Fin n)
    (hi : i ∈ Caverage ε I) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (1 - pDown ε (I.p i)) ^ Δ ≤ (1 - pUp ε (I.p i)) ^ ((1 - ε) * Δ) := by
  have hn : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
    exact_mod_cast this
  simp only [Caverage, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨hlo, hhi⟩ := hi
  set x := I.p i with hxdef
  set δ := ε ^ 2 / 16 with hδ
  have hδ0 : 0 < δ := by positivity
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hlo
  have hεn : 0 < ε / (n : ℝ) := by positivity
  have hεn1 : ε / (n : ℝ) ≤ ε := div_le_self h0.le hn
  -- reduce to a statement about the bases
  suffices key : 0 ≤ 1 - pDown ε x ∧ 0 ≤ 1 - pUp ε x ∧
      1 - pDown ε x ≤ (1 - pUp ε x) ^ (1 - ε) by
    obtain ⟨ha, hb, hab⟩ := key
    rw [Real.rpow_mul hb]
    exact Real.rpow_le_rpow ha hab hΔ
  by_cases hx4 : x ≤ ε / 4
  · simp only [pUp, pDown, if_pos hx4]
    unfold U
    obtain ⟨hu0, hu1⟩ := U_le hδ0 hxpos
    set u := (1 + ε ^ 2 / 16) ^ ⌈Real.logb (1 + ε ^ 2 / 16) x⌉ with hu
    rw [← hδ]
    have hδs : δ ≤ 1 / 256 := by rw [hδ]; nlinarith
    have hu2 : u ≤ 1 / 2 := by nlinarith
    have hb : 0 < 1 - u := by linarith
    refine ⟨?_, hb.le, ?_⟩
    · have : u / (1 + δ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    · have hr := rpow_neg_ge hb h0.le
      have hsplit : (1 - u) ^ (1 - ε) = (1 - u) * (1 - u) ^ (-ε) := by
        rw [show (1 : ℝ) - ε = 1 + -ε by ring, Real.rpow_add hb, Real.rpow_one]
      rw [hsplit]
      have hstep : (1 - u) * (1 + ε * (1 - (1 - u))) ≤ (1 - u) * (1 - u) ^ (-ε) :=
        mul_le_mul_of_nonneg_left hr hb.le
      have hA : 1 / 2 ≤ 1 - u := by linarith
      have hB : ε * (1 / 2) ≤ ε * (1 - u) := mul_le_mul_of_nonneg_left hA h0.le
      have hC : ε * (1 - u) ≤ ε * (1 - u) * (1 + δ) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      have hD : δ ≤ ε * (1 / 2) := by rw [hδ]; nlinarith
      have hkey : (1 + δ) * (1 - ε + ε * u) ≤ 1 := by
        have e : (1 + δ) * (1 - ε + ε * u) = 1 + δ - ε * (1 - u) * (1 + δ) := by ring
        rw [e]; linarith
      have e : (1 - u) * (1 + ε * (1 - (1 - u))) - (1 - u / (1 + δ)) =
          u / (1 + δ) * (1 - (1 + δ) * (1 - ε + ε * u)) := by
        field_simp
        ring
      have hnn : 0 ≤ u / (1 + δ) * (1 - (1 + δ) * (1 - ε + ε * u)) :=
        mul_nonneg (div_nonneg hu0.le (by linarith)) (by linarith)
      linarith
  · push_neg at hx4
    simp only [pUp, pDown, if_neg (not_le.mpr hx4)]
    unfold D
    have hy : 0 < 1 - x := by linarith
    obtain ⟨hd0, hd1⟩ := D_le hδ0 hy
    set d := (1 + ε ^ 2 / 16) ^ ⌊Real.logb (1 + ε ^ 2 / 16) (1 - x)⌋ with hd
    rw [← hδ]
    have e1 : 1 - (1 - (1 + δ) * d) = (1 + δ) * d := by ring
    have e2 : 1 - (1 - d) = d := by ring
    rw [e1, e2]
    refine ⟨by positivity, hd0.le, ?_⟩
    have hr := rpow_neg_ge hd0 h0.le
    have hsplit : d ^ (1 - ε) = d * d ^ (-ε) := by
      rw [show (1 : ℝ) - ε = 1 + -ε by ring, Real.rpow_add hd0, Real.rpow_one]
    rw [hsplit]
    have h1d : ε / 4 < 1 - d := by linarith
    have hge : 1 + δ ≤ d ^ (-ε) := by
      have : δ ≤ ε * (1 - d) := by rw [hδ]; nlinarith
      linarith
    rw [mul_comm (1 + δ) d]
    exact mul_le_mul_of_nonneg_left hge hd0.le
