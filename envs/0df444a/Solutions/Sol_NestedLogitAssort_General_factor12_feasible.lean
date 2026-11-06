-- Prove2me | solution 1 for NestedLogitAssort.General.factor12_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T09:45:44.205973+00:00
-- url     : https://prove2.me/submissions/76e23ebe-aa94-4f1f-bb37-ad7641f3e1fd

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Feas3
import Definitions.Def_NestedLogitAssort_General_IsOpt4
import Definitions.Def_NestedLogitAssort_General_CandGen
import Definitions.Def_NestedLogitAssort_General_IsWeightOrder
import Definitions.Def_NestedLogitAssort_General_factor12

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NLAAux

/-- Segment bound, case `γ ≤ 1` (concavity of `t ↦ t ^ γ`). -/
lemma key_le_one {γ x β Va Vb w ρ Pa Pb V P : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hx : 0 ≤ x)
    (hβ : 1 ≤ β) (hVa : 0 < Va) (hw : 0 < w) (hPa : 0 ≤ Pa) (hρ : 0 ≤ ρ)
    (hVb : Vb = Va + w) (hPb : Pb = Pa + w * ρ)
    (hV1 : Va ≤ V) (hV2 : V ≤ Vb) (hP : P ≤ Pa + (V - Va) * ρ) (hratio : Vb ≤ β * Va) :
    V ^ γ * (P / V - β * x) ≤ β * max (Va ^ γ * (Pa / Va - x)) (Vb ^ γ * (Pb / Vb - x)) := by
  have hVpos : 0 < V := lt_of_lt_of_le hVa hV1
  have hVbpos : 0 < Vb := by rw [hVb]; linarith
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  set μ := (V - Va) / w with hμ
  set lam := (Vb - V) / w with hlam
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hw.le
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hw.le
  have hsum : lam + μ = 1 := by
    rw [hlam, hμ, ← add_div, div_eq_one_iff_eq hw.ne', hVb]; ring
  have hVcomb : lam * Va + μ * Vb = V := by
    rw [hlam, hμ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hw.ne', hVb]
    ring
  have hPcomb : P ≤ lam * Pa + μ * Pb := by
    have : lam * Pa + μ * Pb = Pa + (V - Va) * ρ := by
      rw [hlam, hμ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hw.ne', hPb,
        hVb]
      ring
    linarith
  have hconc : lam * Va ^ γ + μ * Vb ^ γ ≤ V ^ γ := by
    have := (Real.concaveOn_rpow hγ0 hγ1).2 (Set.mem_Ici.2 hVa.le) (Set.mem_Ici.2 hVbpos.le)
      hl0 hμ0 hsum
    simpa [smul_eq_mul, hVcomb] using this
  set g := V ^ γ / V with hg
  set ga := Va ^ γ / Va with hga
  set gb := Vb ^ γ / Vb with hgb
  have hg0 : 0 ≤ g := by positivity
  have hga0 : 0 ≤ ga := by positivity
  have hgb0 : 0 ≤ gb := by positivity
  have hg_a : g ≤ ga := by
    rw [hg, hga, ← Real.rpow_sub_one hVpos.ne', ← Real.rpow_sub_one hVa.ne']
    exact Real.rpow_le_rpow_of_nonpos hVa hV1 (by linarith)
  have hg_b : g ≤ β * gb := by
    have h1 : V ^ γ ≤ Vb ^ γ := Real.rpow_le_rpow hVpos.le hV2 hγ0
    have h2 : Vb ≤ β * V := by
      have := mul_le_mul_of_nonneg_left hV1 (by linarith : (0:ℝ) ≤ β); linarith
    rw [hg, hgb, div_le_iff₀ hVpos]
    have : β * (Vb ^ γ / Vb) * V = Vb ^ γ * (β * V / Vb) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [this]
    have h3 : 1 ≤ β * V / Vb := by rw [le_div_iff₀ hVbpos]; linarith
    have h4 : 0 ≤ Vb ^ γ := by positivity
    calc V ^ γ ≤ Vb ^ γ := h1
      _ = Vb ^ γ * 1 := (mul_one _).symm
      _ ≤ Vb ^ γ * (β * V / Vb) := mul_le_mul_of_nonneg_left h3 h4
  have eL : V ^ γ * (P / V - β * x) = g * P - β * x * V ^ γ := by
    rw [hg, div_eq_mul_inv, div_eq_mul_inv]; ring
  have eA : Va ^ γ * (Pa / Va - x) = ga * Pa - x * Va ^ γ := by
    rw [hga, div_eq_mul_inv, div_eq_mul_inv]; ring
  have eB : Vb ^ γ * (Pb / Vb - x) = gb * Pb - x * Vb ^ γ := by
    rw [hgb, div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [eL, eA, eB]
  set M := max (ga * Pa - x * Va ^ γ) (gb * Pb - x * Vb ^ γ) with hM
  have hMa : ga * Pa - x * Va ^ γ ≤ M := le_max_left _ _
  have hMb : gb * Pb - x * Vb ^ γ ≤ M := le_max_right _ _
  have h1 : g * P ≤ g * (lam * Pa + μ * Pb) := mul_le_mul_of_nonneg_left hPcomb hg0
  have h2 : g * Pa ≤ β * ga * Pa := by
    have : g * Pa ≤ ga * Pa := mul_le_mul_of_nonneg_right hg_a hPa
    have : ga * Pa ≤ β * ga * Pa := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ β - 1) (mul_nonneg hga0 hPa); linarith
    linarith
  have h3 : g * Pb ≤ β * gb * Pb := by
    have := mul_le_mul_of_nonneg_right hg_b hPb0; linarith
  have h2' := mul_le_mul_of_nonneg_left h2 hl0
  have h3' := mul_le_mul_of_nonneg_left h3 hμ0
  have hbx : 0 ≤ β * x := by positivity
  have h4 := mul_le_mul_of_nonneg_left hconc hbx
  have h5 := mul_le_mul_of_nonneg_left hMa hl0
  have h6 := mul_le_mul_of_nonneg_left hMb hμ0
  have h7 : β * (lam * (ga * Pa - x * Va ^ γ) + μ * (gb * Pb - x * Vb ^ γ)) ≤ β * (lam * M + μ * M) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h8 : lam * M + μ * M = M := by rw [← add_mul, hsum, one_mul]
  calc g * P - β * x * V ^ γ ≤ g * (lam * Pa + μ * Pb) - β * x * (lam * Va ^ γ + μ * Vb ^ γ) := by
        linarith
    _ = lam * (g * Pa) + μ * (g * Pb) - β * x * (lam * Va ^ γ + μ * Vb ^ γ) := by ring
    _ ≤ lam * (β * ga * Pa) + μ * (β * gb * Pb) - β * x * (lam * Va ^ γ + μ * Vb ^ γ) := by linarith
    _ = β * (lam * (ga * Pa - x * Va ^ γ) + μ * (gb * Pb - x * Vb ^ γ)) := by ring
    _ ≤ β * (lam * M + μ * M) := h7
    _ = β * M := by rw [h8]

/-- Segment bound, case `1 ≤ γ` (log-concavity via weighted AM-GM). -/
lemma key_ge_one {γ x β Va Vb w ρ Pa Pb V P : ℝ} (hγ1 : 1 ≤ γ) (hx : 0 ≤ x)
    (hβ : 1 ≤ β) (hVa : 0 < Va) (hw : 0 < w) (hPa : 0 ≤ Pa) (hρ : 0 ≤ ρ) (hP0 : 0 ≤ P)
    (hVb : Vb = Va + w) (hPb : Pb = Pa + w * ρ)
    (hV1 : Va ≤ V) (hV2 : V ≤ Vb) (hP : P ≤ Pa + (V - Va) * ρ) (hratio : Vb ≤ β * Va) :
    V ^ γ * (P / V - β * x) ≤ β * max (Va ^ γ * (Pa / Va - x)) (Vb ^ γ * (Pb / Vb - x)) := by
  have hVpos : 0 < V := lt_of_lt_of_le hVa hV1
  have hVbpos : 0 < Vb := by rw [hVb]; linarith
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  set g := V ^ γ / V with hg
  set ga := Va ^ γ / Va with hga
  set gb := Vb ^ γ / Vb with hgb
  have hg0 : 0 ≤ g := by positivity
  have hga0 : 0 ≤ ga := by positivity
  have hgb0 : 0 ≤ gb := by positivity
  have hVne : V ≠ 0 := hVpos.ne'
  have hVane : Va ≠ 0 := hVa.ne'
  have hVbne : Vb ≠ 0 := hVbpos.ne'
  have eL : V ^ γ * (P / V - β * x) = g * (P - β * x * V) := by
    rw [hg, div_eq_mul_inv, div_eq_mul_inv]
    have : V * V⁻¹ = 1 := mul_inv_cancel₀ hVne
    linear_combination (β * x * V ^ γ) * this
  have eA : Va ^ γ * (Pa / Va - x) = ga * (Pa - x * Va) := by
    rw [hga, div_eq_mul_inv, div_eq_mul_inv]
    have : Va * Va⁻¹ = 1 := mul_inv_cancel₀ hVane
    linear_combination (x * Va ^ γ) * this
  have eB : Vb ^ γ * (Pb / Vb - x) = gb * (Pb - x * Vb) := by
    rw [hgb, div_eq_mul_inv, div_eq_mul_inv]
    have : Vb * Vb⁻¹ = 1 := mul_inv_cancel₀ hVbne
    linear_combination (x * Vb ^ γ) * this
  rw [eL, eA, eB]
  have hPPb : P ≤ Pb := by
    rw [hPb]; have : (V - Va) * ρ ≤ w * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ
    linarith
  rcases le_or_gt 0 (P - β * x * V) with hA | hB
  · -- positive case: compare with the upper end
    have hgg : g ≤ gb := by
      rw [hg, hgb, ← Real.rpow_sub_one hVpos.ne', ← Real.rpow_sub_one hVbpos.ne']
      exact Real.rpow_le_rpow hVpos.le hV2 (by linarith)
    have hc : P - β * x * V ≤ Pb - x * Vb := by
      have : x * Vb ≤ β * x * V := by
        have h1 : Vb ≤ β * V := by
          have := mul_le_mul_of_nonneg_left hV1 (by linarith : (0:ℝ) ≤ β); linarith
        have := mul_le_mul_of_nonneg_left h1 hx; linarith
      linarith
    have hle : g * (P - β * x * V) ≤ gb * (Pb - x * Vb) := mul_le_mul hgg hc hA hgb0
    have hFb0 : 0 ≤ gb * (Pb - x * Vb) := le_trans (mul_nonneg hg0 hA) hle
    calc g * (P - β * x * V) ≤ gb * (Pb - x * Vb) := hle
      _ ≤ β * (gb * (Pb - x * Vb)) := by
          have := mul_nonneg (by linarith : (0:ℝ) ≤ β - 1) hFb0; linarith
      _ ≤ β * max (ga * (Pa - x * Va)) (gb * (Pb - x * Vb)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  · have hL : g * (P - β * x * V) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg0 hB.le
    by_cases hmax : 0 ≤ max (ga * (Pa - x * Va)) (gb * (Pb - x * Vb))
    · exact le_trans hL (mul_nonneg (by linarith) hmax)
    push Not at hmax
    have hFa : ga * (Pa - x * Va) < 0 := lt_of_le_of_lt (le_max_left _ _) hmax
    have hFb : gb * (Pb - x * Vb) < 0 := lt_of_le_of_lt (le_max_right _ _) hmax
    have hca : 0 < x * Va - Pa := by
      by_contra h; push Not at h
      have := mul_nonneg hga0 (by linarith : (0:ℝ) ≤ Pa - x * Va); linarith
    have hcb : 0 < x * Vb - Pb := by
      by_contra h; push Not at h
      have := mul_nonneg hgb0 (by linarith : (0:ℝ) ≤ Pb - x * Vb); linarith
    set ca := x * Va - Pa with hca_def
    set cb := x * Vb - Pb with hcb_def
    set μ := (V - Va) / w with hμ
    set lam := (Vb - V) / w with hlam
    have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hw.le
    have hl0 : 0 ≤ lam := div_nonneg (by linarith) hw.le
    have hsum : lam + μ = 1 := by
      rw [hlam, hμ, ← add_div, div_eq_one_iff_eq hw.ne', hVb]; ring
    have hVcomb : lam * Va + μ * Vb = V := by
      rw [hlam, hμ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hw.ne', hVb]
      ring
    have hPcomb : P ≤ lam * Pa + μ * Pb := by
      have : lam * Pa + μ * Pb = Pa + (V - Va) * ρ := by
        rw [hlam, hμ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hw.ne',
          hPb, hVb]
        ring
      linarith
    have hccomb : lam * ca + μ * cb ≤ x * V - P := by
      have : x * V = x * (lam * Va + μ * Vb) := by rw [hVcomb]
      rw [hca_def, hcb_def, this]; linarith
    -- AM-GM
    have hgV : g = V ^ (γ - 1) := by rw [hg, Real.rpow_sub_one hVpos.ne']
    have hgVa : ga = Va ^ (γ - 1) := by rw [hga, Real.rpow_sub_one hVa.ne']
    have hgVb : gb = Vb ^ (γ - 1) := by rw [hgb, Real.rpow_sub_one hVbpos.ne']
    have amV : Va ^ lam * Vb ^ μ ≤ V := by
      rw [← hVcomb]
      exact Real.geom_mean_le_arith_mean2_weighted hl0 hμ0 hVa.le hVbpos.le hsum
    have amc : ca ^ lam * cb ^ μ ≤ lam * ca + μ * cb :=
      Real.geom_mean_le_arith_mean2_weighted hl0 hμ0 hca.le hcb.le hsum
    have hprod : (ga * ca) ^ lam * (gb * cb) ^ μ ≤ g * (lam * ca + μ * cb) := by
      have e : (ga * ca) ^ lam * (gb * cb) ^ μ = (Va ^ lam * Vb ^ μ) ^ (γ - 1) * (ca ^ lam * cb ^ μ) := by
        rw [hgVa, hgVb, Real.mul_rpow (by positivity) hca.le, Real.mul_rpow (by positivity) hcb.le,
          ← Real.rpow_mul hVa.le, ← Real.rpow_mul hVbpos.le,
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hVa.le,
          ← Real.rpow_mul hVbpos.le]
        rw [mul_comm (γ - 1) lam, mul_comm (γ - 1) μ]; ring
      rw [e, hgV]
      apply mul_le_mul _ amc (by positivity) (by positivity)
      exact Real.rpow_le_rpow (by positivity) amV (by linarith)
    set m := min (ga * ca) (gb * cb) with hm
    have hm0 : 0 ≤ m := le_min (mul_nonneg hga0 hca.le) (mul_nonneg hgb0 hcb.le)
    have hmprod : m ≤ (ga * ca) ^ lam * (gb * cb) ^ μ := by
      have e : m = m ^ lam * m ^ μ := by
        rw [← Real.rpow_add' hm0 (by rw [hsum]; norm_num), hsum, Real.rpow_one]
      rw [e]
      apply mul_le_mul
      · exact Real.rpow_le_rpow hm0 (min_le_left _ _) hl0
      · exact Real.rpow_le_rpow hm0 (min_le_right _ _) hμ0
      · positivity
      · positivity
    have hmax_eq : max (ga * (Pa - x * Va)) (gb * (Pb - x * Vb)) = -m := by
      rw [hm, ← max_neg_neg]; congr 1 <;> ring
    rw [hmax_eq]
    have k1 : m ≤ g * (x * V - P) := by
      have := mul_le_mul_of_nonneg_left hccomb hg0
      linarith
    have k2 : β * (g * (x * V - P)) ≤ g * (β * x * V - P) := by
      have : 0 ≤ g * ((β - 1) * P) := mul_nonneg hg0 (mul_nonneg (by linarith) hP0)
      linarith
    have k3 : β * m ≤ β * (g * (x * V - P)) := mul_le_mul_of_nonneg_left k1 (by linarith)
    linarith

/-- Segment bound when the lower end has zero weight (`v_{i0} = 0`, empty prefix). -/
lemma key_zero {γ x β w ρ V P : ℝ} (hγ0 : 0 < γ) (hx : 0 ≤ x) (hβ : 1 ≤ β) (hw : 0 < w)
    (hV0 : 0 ≤ V) (hV2 : V ≤ w) (hP : P ≤ V * ρ) :
    V ^ γ * (P / V - β * x) ≤ β * max ((0 : ℝ) ^ γ * (0 / 0 - x)) (w ^ γ * (w * ρ / w - x)) := by
  have hz : (0 : ℝ) ^ γ = 0 := Real.zero_rpow hγ0.ne'
  rw [hz, zero_mul]
  have e : w * ρ / w = ρ := by field_simp
  rw [e]
  have hβ0 : 0 ≤ β := by linarith
  rcases hV0.lt_or_eq with hVpos | hV
  · have hPV : P / V ≤ ρ := by rw [div_le_iff₀ hVpos]; linarith
    have hVg : 0 < V ^ γ := Real.rpow_pos_of_pos hVpos γ
    have h1 : V ^ γ * (P / V - β * x) ≤ V ^ γ * (ρ - β * x) :=
      mul_le_mul_of_nonneg_left (by linarith) hVg.le
    rcases le_or_gt (ρ - β * x) 0 with hn | hp
    · have : V ^ γ * (ρ - β * x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hVg.le hn
      have : 0 ≤ β * max 0 (w ^ γ * (ρ - x)) := mul_nonneg hβ0 (le_max_left _ _)
      linarith
    · have hwV : V ^ γ ≤ w ^ γ := Real.rpow_le_rpow hV0 hV2 hγ0.le
      have hbx : x ≤ β * x := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ β - 1) hx; linarith
      have h2 : V ^ γ * (ρ - β * x) ≤ w ^ γ * (ρ - x) :=
        mul_le_mul hwV (by linarith) hp.le (by positivity)
      have h3 : 0 ≤ w ^ γ * (ρ - x) := le_trans (mul_nonneg hVg.le hp.le) h2
      have h4 : w ^ γ * (ρ - x) ≤ β * (w ^ γ * (ρ - x)) := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ β - 1) h3; linarith
      have h5 : β * (w ^ γ * (ρ - x)) ≤ β * max 0 (w ^ γ * (ρ - x)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0
      linarith
  · rw [← hV, hz, zero_mul]
    exact mul_nonneg hβ0 (le_max_left _ _)

/-- Segment bound for a zero-weight lower end, allowing `γ = 0`. -/
lemma key_zero' {γ x β w ρ V P : ℝ} (hγ0 : 0 ≤ γ) (hx : 0 ≤ x) (hβ : 1 ≤ β) (hw : 0 < w)
    (hρ : 0 ≤ ρ) (hV0 : 0 ≤ V) (hV2 : V ≤ w) (hP : P ≤ V * ρ) :
    V ^ γ * (P / V - β * x) ≤ β * max ((0 : ℝ) ^ γ * (0 / 0 - x)) (w ^ γ * (w * ρ / w - x)) := by
  rcases hγ0.lt_or_eq with hγ | hγ
  · exact key_zero hγ hx hβ hw hV0 hV2 hP
  · rw [← hγ, Real.rpow_zero, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul, one_mul]
    have e : w * ρ / w = ρ := by field_simp
    rw [e]
    have hPV : P / V ≤ ρ := by
      rcases hV0.lt_or_eq with hVpos | hV
      · rw [div_le_iff₀ hVpos]; linarith
      · rw [← hV, div_zero]; exact hρ
    have h1 : 0 ≤ (β - 1) * ρ := mul_nonneg (by linarith) hρ
    have h2 : β * (ρ - x) ≤ β * max (0 / 0 - x) (ρ - x) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    have h3 : β * (ρ - x) = ρ - β * x + (β - 1) * ρ := by ring
    linarith

/-- Degenerate segment: the upper end has the same weight as the lower end. -/
lemma key_flat {γ x β Va V P Pa : ℝ} (hβ : 1 ≤ β) (hVa : 0 ≤ Va)
    (hPa : 0 ≤ Pa) (hV : V = Va) (hP : P ≤ Pa) :
    V ^ γ * (P / V - β * x) ≤ β * (Va ^ γ * (Pa / Va - x)) := by
  rw [hV]
  have h1 : P / Va ≤ Pa / Va := div_le_div_of_nonneg_right hP hVa
  have h2 : 0 ≤ Va ^ γ := Real.rpow_nonneg hVa γ
  have h3 : 0 ≤ Pa / Va := div_nonneg hPa hVa
  have h4 : Va ^ γ * (P / Va - β * x) ≤ Va ^ γ * (Pa / Va - β * x) :=
    mul_le_mul_of_nonneg_left (by linarith) h2
  have h5 : 0 ≤ Va ^ γ * ((β - 1) * (Pa / Va)) := mul_nonneg h2 (mul_nonneg (by linarith) h3)
  have e : β * (Va ^ γ * (Pa / Va - x)) = Va ^ γ * (Pa / Va - β * x) + Va ^ γ * ((β - 1) * (Pa / Va)) := by
    ring
  linarith

open NestedLogitAssort.General

lemma mem_NBR {n k : ℕ} (j : Fin n) : j ∈ NBR n k ↔ j.val < k := by
  simp [NBR]

lemma exch {n : ℕ} (r v : Fin n → ℝ) (hr : Antitone r) (hv : ∀ j, 0 ≤ v j) (a : Fin n)
    (S : Finset (Fin n)) :
    ∑ j ∈ S, r j * v j ≤
      ∑ j ∈ NBR n a.val, r j * v j + (∑ j ∈ S, v j - ∑ j ∈ NBR n a.val, v j) * r a := by
  have key : ∑ j ∈ S, (r j - r a) * v j ≤ ∑ j ∈ NBR n a.val, (r j - r a) * v j := by
    rw [← Finset.sum_inter_add_sum_sdiff S (NBR n a.val)]
    have h1 : ∑ j ∈ S \ NBR n a.val, (r j - r a) * v j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      rw [Finset.mem_sdiff, mem_NBR] at hj
      have : a ≤ j := by rw [Fin.le_iff_val_le_val]; omega
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hr this]) (hv j)
    have h2 : ∑ j ∈ S ∩ NBR n a.val, (r j - r a) * v j ≤ ∑ j ∈ NBR n a.val, (r j - r a) * v j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro j hj _
      rw [mem_NBR] at hj
      have : j ≤ a := by rw [Fin.le_iff_val_le_val]; omega
      exact mul_nonneg (by linarith [hr this]) (hv j)
    linarith
  have e1 : ∑ j ∈ S, (r j - r a) * v j = ∑ j ∈ S, r j * v j - (∑ j ∈ S, v j) * r a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  have e2 : ∑ j ∈ NBR n a.val, (r j - r a) * v j =
      ∑ j ∈ NBR n a.val, r j * v j - (∑ j ∈ NBR n a.val, v j) * r a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  rw [e1, e2] at key
  linarith

lemma NBR_succ {n : ℕ} (a : Fin n) : NBR n (a.val + 1) = insert a (NBR n a.val) := by
  ext j; simp only [Finset.mem_insert, mem_NBR, Fin.ext_iff]; omega

lemma NBR_zero (n : ℕ) : NBR n 0 = ∅ := by
  ext j; simp [mem_NBR]

lemma NBR_n (n : ℕ) : NBR n n = Finset.univ := by
  ext j; simp [mem_NBR, j.isLt]

lemma card_filter_lt_fin {n : ℕ} (l : Fin n) [DecidablePred (fun l' : Fin n => l' < l)] :
    (Finset.univ.filter (fun l' : Fin n => l' < l)).card = l.val := by
  have : Finset.univ.filter (fun l' : Fin n => l' < l) = Finset.Iio l := by
    ext m; simp
  rw [this, Fin.card_Iio]

lemma Light_n {n : ℕ} (σ : Equiv.Perm (Fin n)) : Light σ n = Finset.univ := by
  ext l
  simp only [Light, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact ⟨σ.symm l, (σ.symm l).isLt, by simp⟩

lemma NK_n {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : ℕ) : NK σ n j = NBR n j := by
  ext l
  simp only [NK, Light_n, Finset.mem_filter, Finset.mem_univ, true_and, card_filter_lt_fin, mem_NBR]

lemma V_nonneg {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (hw0 : 0 ≤ I.w0 i)
    (hv : ∀ j, 0 ≤ I.v i j) (S : Finset (Fin n)) : 0 ≤ V I i S :=
  add_nonneg hw0 (Finset.sum_nonneg (fun j _ => hv j))

lemma R_nonneg {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (hw0 : 0 ≤ I.w0 i)
    (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j) (S : Finset (Fin n)) : 0 ≤ R I i S :=
  div_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hv j))) (V_nonneg I i hw0 hv S)

/-- Per-nest bound: every assortment, at `β x`, is dominated by `β` times a revenue-ordered prefix
at `x`. -/
theorem per_nest {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (hw0 : 0 ≤ I.w0 i)
    (hv0 : ∀ j, 0 ≤ I.v i j) (hrn : ∀ j, 0 ≤ I.r i j) (hanti : Antitone (I.r i))
    (hγ : 0 ≤ I.γ i) (x β : ℝ) (hx : 0 ≤ x) (hβ1 : 1 ≤ β)
    (hratio : ∀ a : ℕ, a < n → 0 < V I i (NBR n a) → V I i (NBR n (a + 1)) ≤ β * V I i (NBR n a))
    (S : Finset (Fin n)) :
    ∃ j ≤ n, T I i S (β * x) ≤ β * T I i (NBR n j) x := by
  have hn : 0 < n ∨ n = 0 := by omega
  rcases hn with hn | hn
  swap
  · subst hn
    have hS : S = ∅ := by ext j; exact j.elim0
    have hN : NBR 0 0 = ∅ := NBR_zero 0
    refine ⟨0, le_rfl, ?_⟩
    rw [hS, hN]
    have hR : R I i ∅ = 0 := by simp [R]
    unfold T
    rw [hR]
    have : 0 ≤ V I i ∅ ^ I.γ i := Real.rpow_nonneg (V_nonneg I i hw0 hv0 ∅) _
    exact le_of_eq (by ring)
  set W : ℕ → ℝ := fun k => ∑ j ∈ NBR n k, I.v i j with hW
  set WS := ∑ j ∈ S, I.v i j with hWS
  have hWS0 : 0 ≤ WS := Finset.sum_nonneg (fun j _ => hv0 j)
  have hex : ∃ k, WS ≤ W (k + 1) := by
    refine ⟨n - 1, ?_⟩
    have : n - 1 + 1 = n := by omega
    simp only [hW, this, NBR_n]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hv0 j)
  classical
  set a := Nat.find hex with ha
  have ha_spec : WS ≤ W (a + 1) := Nat.find_spec hex
  have ha_lt : a < n := by
    have := Nat.find_min' hex (show WS ≤ W (n - 1 + 1) by
      have : n - 1 + 1 = n := by omega
      simp only [hW, this, NBR_n]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hv0 j))
    omega
  have ha_lo : W a ≤ WS := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · simp only [hW, h0, NBR_zero, Finset.sum_empty]; exact hWS0
    · have := Nat.find_min hex (show a - 1 < a by omega)
      have e : a - 1 + 1 = a := by omega
      rw [e] at this; exact (not_le.1 this).le
  set a' : Fin n := ⟨a, ha_lt⟩ with ha'
  have hsucc : NBR n (a + 1) = insert a' (NBR n a) := NBR_succ a'
  have hnot : a' ∉ NBR n a := by rw [mem_NBR]; simp [ha']
  set Va := V I i (NBR n a) with hVa_def
  set Vb := V I i (NBR n (a + 1)) with hVb_def
  set Pa := ∑ j ∈ NBR n a, I.r i j * I.v i j with hPa_def
  set Pb := ∑ j ∈ NBR n (a + 1), I.r i j * I.v i j with hPb_def
  set VS := V I i S with hVS_def
  set PS := ∑ j ∈ S, I.r i j * I.v i j with hPS_def
  have hVb : Vb = Va + I.v i a' := by
    simp only [hVb_def, hVa_def, V, hsucc, Finset.sum_insert hnot]; ring
  have hPb : Pb = Pa + I.v i a' * I.r i a' := by
    simp only [hPb_def, hPa_def, hsucc, Finset.sum_insert hnot]; ring
  have hVaW : Va = I.w0 i + W a := rfl
  have hVSW : VS = I.w0 i + WS := rfl
  have hVbW : Vb = I.w0 i + W (a + 1) := rfl
  have hV1 : Va ≤ VS := by rw [hVaW, hVSW]; linarith
  have hV2 : VS ≤ Vb := by rw [hVbW, hVSW]; linarith
  have hexch := exch (I.r i) (I.v i) hanti hv0 a' S
  have hP : PS ≤ Pa + (VS - Va) * I.r i a' := by
    have : VS - Va = WS - W a := by rw [hVaW, hVSW]; ring
    rw [this]; exact hexch
  have hPa0 : 0 ≤ Pa := Finset.sum_nonneg (fun j _ => mul_nonneg (hrn j) (hv0 j))
  have hPS0 : 0 ≤ PS := Finset.sum_nonneg (fun j _ => mul_nonneg (hrn j) (hv0 j))
  have hρ := hrn a'
  have eS : T I i S (β * x) = VS ^ I.γ i * (PS / VS - β * x) := rfl
  have eA : T I i (NBR n a) x = Va ^ I.γ i * (Pa / Va - x) := rfl
  have eB : T I i (NBR n (a + 1)) x = Vb ^ I.γ i * (Pb / Vb - x) := rfl
  have hVa0 : 0 ≤ Va := V_nonneg I i hw0 hv0 _
  have hmain : VS ^ I.γ i * (PS / VS - β * x) ≤
      β * max (Va ^ I.γ i * (Pa / Va - x)) (Vb ^ I.γ i * (Pb / Vb - x)) := by
    rcases (hv0 a').eq_or_lt with hw | hw
    · -- zero weight on the next product: the segment is flat
      have hVbeq : Vb = Va := by rw [hVb, ← hw]; ring
      have hVSeq : VS = Va := le_antisymm (hVbeq ▸ hV2) hV1
      have hPS : PS ≤ Pa := by rw [hVSeq] at hP; linarith
      have := key_flat (γ := I.γ i) (x := x) hβ1 hVa0 hPa0 hVSeq hPS
      exact le_trans this (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
    rcases hVa0.lt_or_eq with hVapos | hVa0'
    · have hr := hratio a ha_lt hVapos
      rcases le_total (I.γ i) 1 with hle | hge
      · exact key_le_one hγ hle hx hβ1 hVapos hw hPa0 hρ hVb hPb hV1 hV2 hP hr
      · exact key_ge_one hge hx hβ1 hVapos hw hPa0 hρ hPS0 hVb hPb hV1 hV2 hP hr
    · -- Va = 0: every product of the prefix has zero weight
      have hW0 : 0 ≤ W a := Finset.sum_nonneg (fun j _ => hv0 j)
      have hWa0 : W a = 0 := by linarith
      have hz : ∀ j ∈ NBR n a, I.v i j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv0 j)).1 hWa0
      have hPa00 : Pa = 0 := Finset.sum_eq_zero (fun j hj => by rw [hz j hj, mul_zero])
      have hVb' : Vb = I.v i a' := by rw [hVb, ← hVa0']; ring
      have hPb' : Pb = I.v i a' * I.r i a' := by rw [hPb, hPa00]; ring
      have hP' : PS ≤ VS * I.r i a' := by rw [hPa00, ← hVa0'] at hP; linarith
      have hVS0 : 0 ≤ VS := le_trans hVa0 hV1
      have := key_zero' hγ hx hβ1 hw hρ hVS0 (hVb' ▸ hV2) hP'
      rw [← hVa0', hPa00, hVb', hPb']
      exact this
  rcases le_total (Va ^ I.γ i * (Pa / Va - x)) (Vb ^ I.γ i * (Pb / Vb - x)) with hab | hab
  · refine ⟨a + 1, ha_lt, ?_⟩
    rw [eS, eB]; rw [max_eq_right hab] at hmain; exact hmain
  · refine ⟨a, ha_lt.le, ?_⟩
    rw [eS, eA]; rw [max_eq_left hab] at hmain; exact hmain

theorem main {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγbar : ∃ i, 1 < I.γ i)
    (σ : M → Equiv.Perm (Fin n))
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (fun i => CandGen (σ i)) x y) :
    Feas3 I (factor12 I * x) (fun i => factor12 I * y i) := by
  obtain ⟨⟨hsum, hcand⟩, hmin⟩ := hopt
  obtain ⟨i0, _⟩ := hγbar
  have h2 : (2 : ℝ) ≤ factor12 I := by
    unfold factor12
    exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hβ0 : 0 ≤ factor12 I := by linarith
  -- n ≥ 1
  have hn : 1 ≤ n := by
    by_contra hn0
    have hn0 : n = 0 := by omega
    subst hn0
    have hfeas : Feas4 I (fun i => CandGen (σ i)) (x - 1) (fun i => y i - I.v0) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_sub_distrib]
        have hcard : (1 : ℝ) ≤ (Finset.univ : Finset M).card := by
          have : 0 < (Finset.univ : Finset M).card := Finset.card_pos.2 ⟨i0, Finset.mem_univ _⟩
          exact_mod_cast this
        simp only [Finset.sum_const, nsmul_eq_mul]
        have := mul_le_mul_of_nonneg_right hcard hv0
        linarith
      · intro i S hS
        rcases hS with ⟨k, j, hk1, hkn, _, _⟩ | ⟨j, _⟩
        · omega
        · exact j.elim0
    have := hmin _ _ hfeas
    linarith
  have hmemN : ∀ i, ∀ j ≤ n, NBR n j ∈ CandGen (σ i) := by
    intro i j hj
    exact Or.inl ⟨n, j, hn, le_rfl, hj, (NK_n (σ i) j).symm⟩
  have hT0 : x < 0 → ∀ i S, 0 ≤ T I i S x := by
    intro hneg i S
    unfold T
    exact mul_nonneg (Real.rpow_nonneg (V_nonneg I i (hw0 i) (hv i) S) _)
      (by linarith [R_nonneg I i (hw0 i) (hv i) (hr i) S])
  -- x ≥ 0
  have hx : 0 ≤ x := by
    by_contra hneg
    have hneg : x < 0 := not_le.1 hneg
    have hy0 : ∀ i, 0 ≤ y i := fun i =>
      le_trans (hT0 hneg i (NBR n 0)) (hcand i _ (hmemN i 0 (Nat.zero_le _)))
    have hs0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy0 i)
    have hv0x : I.v0 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hneg.le
    have hsumeq : ∑ i, y i = 0 := by linarith
    have hyz : ∀ i, y i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy0 i)).1 hsumeq i (Finset.mem_univ _)
    have hv0z : I.v0 = 0 := by
      have : I.v0 * x = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hneg.ne
    have hfeas : Feas4 I (fun i => CandGen (σ i)) (x - 1) y := by
      refine ⟨?_, ?_⟩
      · rw [hsumeq, hv0z, zero_mul]
      · intro i S hS
        have hTS := hcand i S hS
        rw [hyz i] at hTS ⊢
        have hTS0 : T I i S x = 0 := le_antisymm hTS (hT0 hneg i S)
        unfold T at hTS0 ⊢
        have hRx : 0 < R I i S - x := by linarith [R_nonneg I i (hw0 i) (hv i) (hr i) S]
        have hVg : V I i S ^ I.γ i = 0 := (mul_eq_zero.1 hTS0).resolve_right hRx.ne'
        rw [hVg, zero_mul]
    have := hmin _ _ hfeas
    linarith
  refine ⟨?_, ?_⟩
  · rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hsum hβ0
    linarith
  · intro i S
    have hratio : ∀ a : ℕ, a < n → 0 < V I i (NBR n a) →
        V I i (NBR n (a + 1)) ≤ factor12 I * V I i (NBR n a) := by
      intro a ha hVa
      have hL : Listed I i (a + 1) := by
        rcases (hw0 i).eq_or_lt with h0 | hp
        · refine Or.inl ⟨h0.symm, ?_, by omega⟩
          by_contra hlt
          have ha0 : a = 0 := by omega
          rw [ha0, NBR_zero] at hVa
          simp [V, ← h0] at hVa
        · exact Or.inr ⟨hp, by omega, by omega⟩
      have hle : V I i (NBR n (a + 1)) / V I i (NBR n (a + 1 - 1)) ≤ factor12 I := by
        classical
        unfold factor12
        apply Finset.le_max'
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_image]
        refine ⟨(i, a + 1), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_univ _, Finset.mem_range.2 (by omega)⟩, hL⟩
      simp only [Nat.add_sub_cancel] at hle
      rwa [div_le_iff₀ hVa] at hle
    obtain ⟨j, hj, hbound⟩ := per_nest I i (hw0 i) (hv i) (hr i) (hanti i) (hγ0 i) x (factor12 I)
      hx (by linarith) hratio S
    exact le_trans hbound (mul_le_mul_of_nonneg_left (hcand i _ (hmemN i j hj)) hβ0)

end NLAAux

open NestedLogitAssort.General in
theorem solution {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγbar : ∃ i, 1 < I.γ i)
    (σ : M → Equiv.Perm (Fin n)) (hσ : ∀ i, IsWeightOrder I i (σ i))
    (hden : ∀ i j, Listed I i j → 0 < V I i (NBR n (j - 1)))
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (fun i => CandGen (σ i)) x y) :
    Feas3 I (factor12 I * x) (fun i => factor12 I * y i) := by
  exact NLAAux.main I hv0 hw0 hv hr hanti hγ0 hγbar σ x y hopt
