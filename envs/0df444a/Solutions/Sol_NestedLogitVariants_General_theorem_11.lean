-- Prove2me | solution 1 for NestedLogitVariants.General.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T08:24:12.785997+00:00
-- url     : https://prove2.me/submissions/bcb52615-9d60-407e-9155-3622d03a38bd

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR
import Definitions.Def_NestedLogitVariants_General_Factor

set_option autoImplicit false

namespace NLV11Aux

/-- Segment bound, case `γ ≤ 1` (concavity of `t ↦ t ^ γ`). -/
lemma key_le_one {γ x β Va Vb w ρ Pa Pb V P : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hx : 0 ≤ x)
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
    have := (Real.concaveOn_rpow hγ0.le hγ1).2 (Set.mem_Ici.2 hVa.le) (Set.mem_Ici.2 hVbpos.le)
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
    have h1 : V ^ γ ≤ Vb ^ γ := Real.rpow_le_rpow hVpos.le hV2 hγ0.le
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

open NestedLogitVariants.General

lemma mem_nbr {n k : ℕ} (j : Fin n) : j ∈ nbr n k ↔ j.val < k := by
  simp [nbr]

/-- Exchange lemma: the line through the revenue-ordered prefixes `N_a`, `N_{a+1}` bounds every
assortment from above. -/
lemma exch {n : ℕ} (r v : Fin n → ℝ) (hr : Antitone r) (hv : ∀ j, 0 ≤ v j) (a : Fin n)
    (S : Finset (Fin n)) :
    ∑ j ∈ S, r j * v j ≤
      ∑ j ∈ nbr n a.val, r j * v j + (∑ j ∈ S, v j - ∑ j ∈ nbr n a.val, v j) * r a := by
  have key : ∑ j ∈ S, (r j - r a) * v j ≤ ∑ j ∈ nbr n a.val, (r j - r a) * v j := by
    rw [← Finset.sum_inter_add_sum_sdiff S (nbr n a.val)]
    have h1 : ∑ j ∈ S \ nbr n a.val, (r j - r a) * v j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      rw [Finset.mem_sdiff, mem_nbr] at hj
      have : a ≤ j := by rw [Fin.le_iff_val_le_val]; omega
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hr this]) (hv j)
    have h2 : ∑ j ∈ S ∩ nbr n a.val, (r j - r a) * v j ≤ ∑ j ∈ nbr n a.val, (r j - r a) * v j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro j hj _
      rw [mem_nbr] at hj
      have : j ≤ a := by rw [Fin.le_iff_val_le_val]; omega
      exact mul_nonneg (by linarith [hr this]) (hv j)
    linarith
  have e1 : ∑ j ∈ S, (r j - r a) * v j = ∑ j ∈ S, r j * v j - (∑ j ∈ S, v j) * r a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  have e2 : ∑ j ∈ nbr n a.val, (r j - r a) * v j =
      ∑ j ∈ nbr n a.val, r j * v j - (∑ j ∈ nbr n a.val, v j) * r a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  rw [e1, e2] at key
  linarith

lemma nbr_succ {n : ℕ} (a : Fin n) : nbr n (a.val + 1) = insert a (nbr n a.val) := by
  ext j; simp only [Finset.mem_insert, mem_nbr, Fin.ext_iff]; omega

lemma nbr_zero (n : ℕ) : nbr n 0 = ∅ := by
  ext j; simp [mem_nbr]

lemma nbr_n (n : ℕ) : nbr n n = Finset.univ := by
  ext j; simp [mem_nbr, j.isLt]

lemma smallK_n {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) : smallK I i n = Finset.univ := by
  classical
  ext j
  simp only [smallK, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  have hss : Finset.univ.filter (fun l => weightLt I i l j) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, fun h => ?_⟩
    have : j ∈ Finset.univ.filter (fun l => weightLt I i l j) := by rw [h]; exact Finset.mem_univ _
    rw [Finset.mem_filter] at this
    rcases this.2 with h1 | h1
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h1.2
  have := Finset.card_lt_card hss
  simpa using this

lemma card_filter_lt_fin {n : ℕ} (l : Fin n) [DecidablePred (fun l' : Fin n => l' < l)] :
    (Finset.univ.filter (fun l' : Fin n => l' < l)).card = l.val := by
  have : Finset.univ.filter (fun l' : Fin n => l' < l) = Finset.Iio l := by
    ext m; simp
  rw [this, Fin.card_Iio]

lemma nbr_eq_nestedPR {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (j : ℕ) :
    nbr n j = nestedPR I i n j := by
  ext l
  rw [nestedPR, smallK_n, Finset.mem_filter, mem_nbr, card_filter_lt_fin]
  simp

end NLV11Aux

open NLV11Aux in
open NestedLogitVariants.General in
/-- Per-nest bound: every assortment, at `β x`, is dominated by `β` times a revenue-ordered prefix
at `x`. -/
theorem NLV11Aux.per_nest {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing) (i : ι)
    (x β : ℝ) (hx : 0 ≤ x) (hβ1 : 1 ≤ β)
    (hratio : ∀ a : ℕ, a < n → 0 < V I i (nbr n a) → V I i (nbr n (a + 1)) ≤ β * V I i (nbr n a))
    (S : Finset (Fin n)) :
    ∃ j ≤ n, nestWeight I i S * (R I i S - β * x) ≤
      β * (nestWeight I i (nbr n j) * (R I i (nbr n j) - x)) := by
  have hn : 0 < n ∨ n = 0 := by omega
  rcases hn with hn | hn
  swap
  · subst hn
    have hS : S = ∅ := by ext j; exact j.elim0
    have hN : nbr 0 0 = ∅ := nbr_zero 0
    refine ⟨0, le_rfl, ?_⟩
    rw [hS, hN]
    have hV0 : 0 ≤ V I i ∅ := by simp [V, hI.vnp_nonneg i]
    have hR : R I i ∅ = 0 := by simp [R]
    rw [hR]
    have : 0 ≤ nestWeight I i ∅ := by
      unfold nestWeight; exact Real.rpow_nonneg hV0 _
    exact le_of_eq (by ring)
  set W : ℕ → ℝ := fun k => ∑ j ∈ nbr n k, I.v i j with hW
  set WS := ∑ j ∈ S, I.v i j with hWS
  have hvpos := hI.v_pos i
  have hv0 : ∀ j, 0 ≤ I.v i j := fun j => (hvpos j).le
  have hWS0 : 0 ≤ WS := Finset.sum_nonneg (fun j _ => hv0 j)
  have hex : ∃ k, WS ≤ W (k + 1) := by
    refine ⟨n - 1, ?_⟩
    have : n - 1 + 1 = n := by omega
    simp only [hW, this, nbr_n]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hv0 j)
  classical
  set a := Nat.find hex with ha
  have ha_spec : WS ≤ W (a + 1) := Nat.find_spec hex
  have ha_lt : a < n := by
    have := Nat.find_min' hex (show WS ≤ W (n - 1 + 1) by
      have : n - 1 + 1 = n := by omega
      simp only [hW, this, nbr_n]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hv0 j))
    omega
  have ha_lo : W a ≤ WS := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · simp only [hW, h0, nbr_zero, Finset.sum_empty]; exact hWS0
    · have := Nat.find_min hex (show a - 1 < a by omega)
      push Not at this
      have e : a - 1 + 1 = a := by omega
      rw [e] at this; exact this.le
  set a' : Fin n := ⟨a, ha_lt⟩ with ha'
  have hsucc : nbr n (a + 1) = insert a' (nbr n a) := nbr_succ a'
  have hnot : a' ∉ nbr n a := by rw [mem_nbr]; simp [ha']
  -- quantities
  set Va := V I i (nbr n a) with hVa_def
  set Vb := V I i (nbr n (a + 1)) with hVb_def
  set Pa := ∑ j ∈ nbr n a, I.r i j * I.v i j with hPa_def
  set Pb := ∑ j ∈ nbr n (a + 1), I.r i j * I.v i j with hPb_def
  set VS := V I i S with hVS_def
  set PS := ∑ j ∈ S, I.r i j * I.v i j with hPS_def
  have hVb : Vb = Va + I.v i a' := by
    simp only [hVb_def, hVa_def, V, hsucc, Finset.sum_insert hnot]; ring
  have hPb : Pb = Pa + I.v i a' * I.r i a' := by
    simp only [hPb_def, hPa_def, hsucc, Finset.sum_insert hnot]; ring
  have hVaW : Va = I.vnp i + W a := rfl
  have hVSW : VS = I.vnp i + WS := rfl
  have hVbW : Vb = I.vnp i + W (a + 1) := rfl
  have hV1 : Va ≤ VS := by rw [hVaW, hVSW]; linarith
  have hV2 : VS ≤ Vb := by rw [hVbW, hVSW]; linarith
  have hexch := exch (I.r i) (I.v i) (hI.r_antitone i) hv0 a' S
  have hP : PS ≤ Pa + (VS - Va) * I.r i a' := by
    have : VS - Va = WS - W a := by rw [hVaW, hVSW]; ring
    rw [this]; exact hexch
  have hPa0 : 0 ≤ Pa := Finset.sum_nonneg (fun j _ => mul_nonneg (hI.r_nonneg i j) (hv0 j))
  have hPS0 : 0 ≤ PS := Finset.sum_nonneg (fun j _ => mul_nonneg (hI.r_nonneg i j) (hv0 j))
  have hρ := hI.r_nonneg i a'
  have hw := hvpos a'
  have hγ := hI.γ_pos i
  have eS : nestWeight I i S * (R I i S - β * x) = VS ^ I.γ i * (PS / VS - β * x) := rfl
  have eA : nestWeight I i (nbr n a) * (R I i (nbr n a) - x) = Va ^ I.γ i * (Pa / Va - x) := rfl
  have eB : nestWeight I i (nbr n (a + 1)) * (R I i (nbr n (a + 1)) - x) =
      Vb ^ I.γ i * (Pb / Vb - x) := rfl
  have hVa0 : 0 ≤ Va := by
    rw [hVaW]; have := hI.vnp_nonneg i
    have : 0 ≤ W a := Finset.sum_nonneg (fun j _ => hv0 j)
    linarith
  have hmain : VS ^ I.γ i * (PS / VS - β * x) ≤
      β * max (Va ^ I.γ i * (Pa / Va - x)) (Vb ^ I.γ i * (Pb / Vb - x)) := by
    rcases hVa0.lt_or_eq with hVapos | hVa0'
    · have hr := hratio a ha_lt hVapos
      rcases le_total (I.γ i) 1 with hle | hge
      · exact key_le_one hγ hle hx hβ1 hVapos hw hPa0 hρ hVb hPb hV1 hV2 hP hr
      · exact key_ge_one hge hx hβ1 hVapos hw hPa0 hρ hPS0 hVb hPb hV1 hV2 hP hr
    · -- Va = 0: then the prefix is empty
      have hWa0 : W a = 0 := by
        have h1 := hI.vnp_nonneg i
        have h2 : 0 ≤ W a := Finset.sum_nonneg (fun j _ => hv0 j)
        linarith
      have hvnp : I.vnp i = 0 := by
        have h2 : 0 ≤ W a := Finset.sum_nonneg (fun j _ => hv0 j)
        linarith
      have hempty : nbr n a = ∅ := by
        by_contra hne
        have hne' := Finset.nonempty_iff_ne_empty.2 hne
        have : 0 < W a := Finset.sum_pos (fun j _ => hvpos j) hne'
        linarith
      have hPa00 : Pa = 0 := by simp only [hPa_def, hempty, Finset.sum_empty]
      have hVb' : Vb = I.v i a' := by rw [hVb, ← hVa0']; ring
      have hPb' : Pb = I.v i a' * I.r i a' := by rw [hPb, hPa00]; ring
      have hP' : PS ≤ VS * I.r i a' := by rw [hPa00, ← hVa0'] at hP; linarith
      have hVS0 : 0 ≤ VS := le_trans hVa0 hV1
      have := key_zero hγ hx hβ1 hw hVS0 (hVb' ▸ hV2) hP'
      rw [← hVa0', hPa00, hVb', hPb']
      exact this
  rcases le_total (Va ^ I.γ i * (Pa / Va - x)) (Vb ^ I.γ i * (Pb / Vb - x)) with hab | hab
  · refine ⟨a + 1, ha_lt, ?_⟩
    rw [eS, eB]; rw [max_eq_right hab] at hmain; exact hmain
  · refine ⟨a, ha_lt.le, ?_⟩
    rw [eS, eA]; rw [max_eq_left hab] at hmain; exact hmain

open NLV11Aux in
open NestedLogitVariants.General in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i) (β : ℝ) (hβ : IsGreatest (betaSet I) β)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh) :
    LP3Feasible I (β * xh) (β • yh) := by
  obtain ⟨⟨hsum, hcand⟩, hmin⟩ := hopt
  obtain ⟨i0, _⟩ := hsyn
  have h2 : (2 : ℝ) ≤ β := hβ.2 (Or.inl (Or.inl rfl))
  have hβ0 : 0 ≤ β := by linarith
  -- n ≥ 1
  have hn : 1 ≤ n := by
    by_contra hn0
    have hn0 : n = 0 := by omega
    subst hn0
    have hfeas : LP4Feasible I (candidatesPR I) (xh - 1) (fun i => yh i - I.v0) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_sub_distrib]
        have hcard : (1 : ℝ) ≤ (Finset.univ : Finset ι).card := by
          have : 0 < (Finset.univ : Finset ι).card := Finset.card_pos.2 ⟨i0, Finset.mem_univ _⟩
          exact_mod_cast this
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hv0 := hI.v0_nonneg
        have := mul_le_mul_of_nonneg_right hcard hv0
        linarith
      · intro i S hS
        rcases hS with ⟨k, hk, _⟩ | ⟨j, _⟩
        · rw [Finset.mem_Icc] at hk; omega
        · exact j.elim0
    have := hmin _ _ hfeas
    linarith
  have hmemN : ∀ i, ∀ j ≤ n, nbr n j ∈ candidatesPR I i := by
    intro i j hj
    exact Or.inl ⟨n, Finset.mem_Icc.2 ⟨hn, le_rfl⟩, j, hj, nbr_eq_nestedPR I i j⟩
  -- xh ≥ 0
  have hx : 0 ≤ xh := by
    by_contra hneg
    push Not at hneg
    have j0 : Fin n := ⟨0, hn⟩
    have hpos : ∀ i, 0 < yh i := by
      intro i
      have hc := hcand i {j0} (Or.inr ⟨j0, rfl⟩)
      have hV : 0 < V I i {j0} := by
        simp only [V, Finset.sum_singleton]
        linarith [hI.vnp_nonneg i, hI.v_pos i j0]
      have hR : 0 ≤ R I i {j0} := by
        unfold R; apply div_nonneg _ hV.le
        simp only [Finset.sum_singleton]
        exact mul_nonneg (hI.r_nonneg i j0) (hI.v_pos i j0).le
      have hw : 0 < nestWeight I i {j0} := Real.rpow_pos_of_pos hV _
      have : 0 < nestWeight I i {j0} * (R I i {j0} - xh) := mul_pos hw (by linarith)
      linarith
    have : 0 < ∑ i, yh i := Finset.sum_pos (fun i _ => hpos i) ⟨i0, Finset.mem_univ _⟩
    have := mul_nonpos_of_nonneg_of_nonpos hI.v0_nonneg hneg.le
    linarith
  refine ⟨?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hsum hβ0
    linarith
  · intro i S
    have hratio : ∀ a : ℕ, a < n → 0 < V I i (nbr n a) →
        V I i (nbr n (a + 1)) ≤ β * V I i (nbr n a) := by
      intro a ha hVa
      have hmem : V I i (nbr n (a + 1)) / V I i (nbr n (a + 1 - 1)) ∈ betaSet I := by
        rcases (hI.vnp_nonneg i).eq_or_lt with h0 | hp
        · refine Or.inl (Or.inr ⟨i, h0.symm, a + 1, Finset.mem_Icc.2 ⟨?_, by omega⟩, rfl⟩)
          by_contra hlt
          have ha0 : a = 0 := by omega
          rw [ha0, nbr_zero] at hVa
          simp [V, ← h0] at hVa
        · exact Or.inr ⟨i, hp, a + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
      have hle := hβ.2 hmem
      simp only [Nat.add_sub_cancel] at hle
      rwa [div_le_iff₀ hVa] at hle
    obtain ⟨j, hj, hbound⟩ := per_nest I hI i xh β hx (by linarith) hratio S
    have hc := hcand i (nbr n j) (hmemN i j hj)
    simp only [Pi.smul_apply, smul_eq_mul]
    calc nestWeight I i S * (R I i S - β * xh)
        ≤ β * (nestWeight I i (nbr n j) * (R I i (nbr n j) - xh)) := hbound
      _ ≤ β * yh i := mul_le_mul_of_nonneg_left hc hβ0
