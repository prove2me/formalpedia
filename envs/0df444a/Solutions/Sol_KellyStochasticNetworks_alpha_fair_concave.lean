-- Prove2me | solution 1 for KellyStochasticNetworks.alpha_fair_concave
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:13:19.590862+00:00
-- url     : https://prove2.me/submissions/41550110-45f0-4fe1-a148-e2a9009c5faa

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

lemma af_bern {p y : ℝ} (hp0 : p ≠ 0) (hp1 : p < 1) (hy : 0 < y) (hy1 : y ≠ 1) :
    y ^ p / p < 1 / p + (y - 1) := by
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · have hlog : Real.log y < y - 1 := Real.log_lt_sub_one_of_pos hy hy1
    have h1 : 1 + Real.log y * p ≤ y ^ p := by
      rw [Real.rpow_def_of_pos hy]; linarith [Real.add_one_le_exp (Real.log y * p)]
    have h2 : 1 + p * (y - 1) < y ^ p := by nlinarith
    rw [div_lt_iff_of_neg hneg]
    have e : (1 / p + (y - 1)) * p = 1 + p * (y - 1) := by
      rw [add_mul, one_div, inv_mul_cancel₀ hp0]; ring
    rw [e]; exact h2
  · have hb := rpow_one_add_lt_one_add_mul_self (s := y - 1) (by linarith) (sub_ne_zero.mpr hy1)
      hpos hp1
    rw [add_sub_cancel] at hb
    rw [div_lt_iff₀ hpos]
    have e : (1 / p + (y - 1)) * p = 1 + p * (y - 1) := by
      rw [add_mul, one_div, inv_mul_cancel₀ hp0]; ring
    rw [e]; exact hb

lemma af_tan_lt {α u x : ℝ} (hα : 0 < α) (hu : 0 < u) (hx : 0 < x) (hne : x ≠ u) :
    (if α = 1 then Real.log x else x ^ (1 - α) / (1 - α)) <
      (if α = 1 then Real.log u else u ^ (1 - α) / (1 - α)) + u ^ (-α) * (x - u) := by
  have hu0 : u ≠ 0 := hu.ne'
  have hy : 0 < x / u := div_pos hx hu
  have hy1 : x / u ≠ 1 := by
    intro h; apply hne; rw [div_eq_one_iff_eq hu0] at h; exact h
  split_ifs with h1
  · subst h1
    rw [Real.rpow_neg_one]
    have := Real.log_lt_sub_one_of_pos hy hy1
    rw [Real.log_div hx.ne' hu0] at this
    have e : x / u - 1 = u⁻¹ * (x - u) := by field_simp
    linarith
  · have hp0 : (1 - α) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hp1 : 1 - α < 1 := by linarith
    have hb := af_bern hp0 hp1 hy hy1
    have hup : 0 < u ^ (1 - α) := Real.rpow_pos_of_pos hu _
    have hxe : x ^ (1 - α) = u ^ (1 - α) * (x / u) ^ (1 - α) := by
      rw [← Real.mul_rpow hu.le hy.le, mul_div_cancel₀ _ hu0]
    have hue : u ^ (-α) = u ^ (1 - α) / u := by
      rw [← Real.rpow_sub_one hu0]; congr 1; ring
    rw [hxe, hue]
    have hm := mul_lt_mul_of_pos_left hb hup
    have e1 : u ^ (1 - α) * ((x / u) ^ (1 - α) / (1 - α)) =
        u ^ (1 - α) * (x / u) ^ (1 - α) / (1 - α) := by ring
    have e2 : u ^ (1 - α) * (1 / (1 - α) + (x / u - 1)) =
        u ^ (1 - α) / (1 - α) + u ^ (1 - α) / u * (x - u) := by
      field_simp
    linarith

lemma af_tan_le {α u x : ℝ} (hα : 0 < α) (hu : 0 < u) (hx : 0 < x) :
    (if α = 1 then Real.log x else x ^ (1 - α) / (1 - α)) ≤
      (if α = 1 then Real.log u else u ^ (1 - α) / (1 - α)) + u ^ (-α) * (x - u) := by
  rcases eq_or_ne x u with rfl | hne
  · simp
  · exact (af_tan_lt hα hu hx hne).le

lemma af_obj_eq {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (X : Fin R → ℝ) :
    alphaFairObjective w n α X =
      ∑ r, w r * n r ^ α * (if α = 1 then Real.log (X r) else X r ^ (1 - α) / (1 - α)) := by
  by_cases h : α = 1
  · subst h; simp [alphaFairObjective]
  · simp [alphaFairObjective, h]

lemma af_comb {a b u v z P Q φu φv : ℝ} (hab : a + b = 1) (hz : z = a * u + b * v)
    (h1 : φu < P + Q * (u - z)) (h2 : φv ≤ P + Q * (v - z)) (ha : 0 < a) (hb : 0 < b) :
    a * φu + b * φv < P := by
  have e : a * (P + Q * (u - z)) + b * (P + Q * (v - z)) = P := by
    have hb' : b = 1 - a := by linarith
    subst hb'; rw [hz]; ring
  have m1 := mul_lt_mul_of_pos_left h1 ha
  have m2 := mul_le_mul_of_nonneg_left h2 hb.le
  linarith

lemma af_pt_lt {α a b u v : ℝ} (hα : 0 < α) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) (hne : u ≠ v) :
    a * (if α = 1 then Real.log u else u ^ (1 - α) / (1 - α)) +
      b * (if α = 1 then Real.log v else v ^ (1 - α) / (1 - α)) <
      (if α = 1 then Real.log (a * u + b * v) else (a * u + b * v) ^ (1 - α) / (1 - α)) := by
  have hz : 0 < a * u + b * v := by positivity
  have hzu : u ≠ a * u + b * v := by
    intro h; apply hne
    have hb' : b = 1 - a := by linarith
    subst hb'
    have : (1 - a) * (u - v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  exact af_comb hab rfl (af_tan_lt hα hz hu hzu) (af_tan_le hα hz hv) ha hb

lemma af_pt_le {α a b u v : ℝ} (hα : 0 < α) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) :
    a * (if α = 1 then Real.log u else u ^ (1 - α) / (1 - α)) +
      b * (if α = 1 then Real.log v else v ^ (1 - α) / (1 - α)) ≤
      (if α = 1 then Real.log (a * u + b * v) else (a * u + b * v) ^ (1 - α) / (1 - α)) := by
  rcases eq_or_ne u v with rfl | hne
  · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
  · exact (af_pt_lt hα hu hv ha hb hab hne).le

theorem af_concave {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) :
    StrictConcaveOn ℝ {X : Fin R → ℝ | ∀ r, 0 < X r} (alphaFairObjective w n α) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab
      have := hy r; simp only [zero_mul, zero_add, one_mul]; exact this
    · have := mul_pos ha' (hx r); have := mul_nonneg hb (hy r).le; linarith
  · intro x hx y hy hxy a b ha hb hab
    obtain ⟨r0, hr0⟩ := Function.ne_iff.mp hxy
    simp only [smul_eq_mul]
    rw [af_obj_eq, af_obj_eq, af_obj_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro r _
      have hc : 0 < w r * n r ^ α := mul_pos (hw r) (Real.rpow_pos_of_pos (hn r) α)
      have := mul_le_mul_of_nonneg_left (af_pt_le hα (hx r) (hy r) ha hb hab) hc.le
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · refine ⟨r0, Finset.mem_univ _, ?_⟩
      have hc : 0 < w r0 * n r0 ^ α := mul_pos (hw r0) (Real.rpow_pos_of_pos (hn r0) α)
      have := mul_lt_mul_of_pos_left (af_pt_lt hα (hx r0) (hy r0) ha hb hab hr0) hc
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) :
    StrictConcaveOn ℝ {X : Fin R → ℝ | ∀ r, 0 < X r} (alphaFairObjective w n α) := by
  exact af_concave w n α hα hw hn
