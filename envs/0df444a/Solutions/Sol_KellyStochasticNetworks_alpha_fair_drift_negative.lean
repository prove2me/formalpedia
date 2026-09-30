-- Prove2me | solution 1 for KellyStochasticNetworks.alpha_fair_drift_negative
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:13:21.687396+00:00
-- url     : https://prove2.me/submissions/e81e6896-b636-407a-90db-04d264d4e688

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

lemma af_obj_tangent {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) (X U : Fin R → ℝ) (hX : ∀ r, 0 < X r)
    (hU : ∀ r, 0 < U r) :
    alphaFairObjective w n α X ≤
      alphaFairObjective w n α U + ∑ r, w r * n r ^ α * U r ^ (-α) * (X r - U r) := by
  rw [af_obj_eq, af_obj_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  have hc : 0 < w r * n r ^ α := mul_pos (hw r) (Real.rpow_pos_of_pos (hn r) α)
  have hm := mul_le_mul_of_nonneg_left (af_tan_le hα (hU r) (hX r)) hc.le
  have e : w r * n r ^ α * ((if α = 1 then Real.log (U r) else U r ^ (1 - α) / (1 - α)) +
      U r ^ (-α) * (X r - U r)) =
      w r * n r ^ α * (if α = 1 then Real.log (U r) else U r ^ (1 - α) / (1 - α)) +
      w r * n r ^ α * U r ^ (-α) * (X r - U r) := by ring
  linarith

theorem af_tangent {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X U : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hUpos : ∀ r, 0 < U r)
    (hUfeas : U ∈ networkFeasible A C)
    (hmax : IsMaxOn (alphaFairObjective w n α)
      (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X) :
    (∑ r, w r * n r ^ α * U r ^ (-α) * (U r - X r)) ≤ 0 := by
  have h1 := af_obj_tangent w n α hα hw hn X U hXpos hUpos
  have h2 : alphaFairObjective w n α U ≤ alphaFairObjective w n α X := hmax ⟨hUfeas, hUpos⟩
  have e : ∑ r, w r * n r ^ α * U r ^ (-α) * (U r - X r) =
      -∑ r, w r * n r ^ α * U r ^ (-α) * (X r - U r) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
  linarith

theorem af_drift_negative {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w ρ : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r) (hρ : ∀ r, 0 < ρ r)
    (hstab : ∀ j, linkFlow A ρ j < C j) :
    ∃ ε > 0, ∀ n : Fin R → ℝ, (∀ r, 0 < n r) →
      ∀ X : Fin R → ℝ, (∀ r, 0 < X r) → X ∈ networkFeasible A C →
        IsMaxOn (alphaFairObjective w n α) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X →
        (∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - X r))
          ≤ -ε * ∑ r, w r * n r ^ α * ρ r ^ (1 - α) := by
  obtain ⟨ε, hε, hεC⟩ : ∃ ε > 0, ∀ j, (1 + ε) * linkFlow A ρ j ≤ C j := by
    have hev : ∀ᶠ ε in nhds (0:ℝ), ∀ j, (1 + ε) * linkFlow A ρ j < C j := by
      rw [Filter.eventually_all]
      intro j
      have hc : ContinuousAt (fun ε : ℝ => (1 + ε) * linkFlow A ρ j) 0 := by fun_prop
      exact Filter.Tendsto.eventually hc (gt_mem_nhds (by simpa using hstab j))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨δ / 2, by positivity, fun j => (hball ?_ j).le⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  refine ⟨ε, hε, fun n hn X hXpos hXfeas hmax => ?_⟩
  set U : Fin R → ℝ := fun r => (1 + ε) * ρ r with hU
  have h1ε : (0:ℝ) < 1 + ε := by linarith
  have hUpos : ∀ r, 0 < U r := fun r => mul_pos h1ε (hρ r)
  have hUfeas : U ∈ networkFeasible A C := by
    refine ⟨fun r => (hUpos r).le, fun j => ?_⟩
    have e : linkFlow A U j = (1 + ε) * linkFlow A ρ j := by
      simp only [linkFlow, hU, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [e]; exact hεC j
  have ht := af_tangent A C w n α hα hw hn X U hXpos hUpos hUfeas hmax
  have hUe : ∀ r, U r ^ (-α) = (1 + ε) ^ (-α) * ρ r ^ (-α) :=
    fun r => Real.mul_rpow h1ε.le (hρ r).le
  have hk : 0 < (1 + ε) ^ (-α) := Real.rpow_pos_of_pos h1ε _
  have h2 : ∑ r, w r * n r ^ α * U r ^ (-α) * (U r - X r) =
      (1 + ε) ^ (-α) * ∑ r, w r * ρ r ^ (-α) * n r ^ α * ((1 + ε) * ρ r - X r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hUe r]; simp only [hU]; ring
  have h3 : ∑ r, w r * ρ r ^ (-α) * n r ^ α * ((1 + ε) * ρ r - X r) ≤ 0 := by
    rw [h2] at ht
    by_contra hcon
    push Not at hcon
    have := mul_pos hk hcon
    linarith
  have hρe : ∀ r, ρ r ^ (1 - α) = ρ r * ρ r ^ (-α) := by
    intro r; rw [sub_eq_add_neg, Real.rpow_add (hρ r), Real.rpow_one]
  have h4 : ∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - X r) =
      ∑ r, w r * ρ r ^ (-α) * n r ^ α * ((1 + ε) * ρ r - X r) -
        ε * ∑ r, w r * n r ^ α * ρ r ^ (1 - α) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hρe r]; ring
  rw [h4]; linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w ρ : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r) (hρ : ∀ r, 0 < ρ r)
    (hstab : ∀ j, linkFlow A ρ j < C j) :
    ∃ ε > 0, ∀ n : Fin R → ℝ, (∀ r, 0 < n r) →
      ∀ X : Fin R → ℝ, (∀ r, 0 < X r) → X ∈ networkFeasible A C →
        IsMaxOn (alphaFairObjective w n α) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X →
        (∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - X r))
          ≤ -ε * ∑ r, w r * n r ^ α * ρ r ^ (1 - α) := by
  exact af_drift_negative A C w ρ α hα hA hw hρ hstab
