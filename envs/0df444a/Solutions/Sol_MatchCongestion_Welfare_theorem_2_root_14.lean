-- Prove2me | solution 1 for MatchCongestion.Welfare.theorem_2_root_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:25:04.602311+00:00
-- url     : https://prove2.me/submissions/5bcd4af5-bf30-4669-a17c-410dac4e316b

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem mc_h14 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    ∃! t : ℝ, 0 < t ∧ t < 1 ∧ 1 - t + k * Real.log t = 0 := by
  have hconc := strictConcaveOn_log_Ioi
  have hex : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 - t + k * Real.log t = 0 := by
    have hlk : Real.log k < 0 := Real.log_neg hk0 hk1
    set t0 := k * Real.exp (-2 / k) with ht0
    have ht0pos : 0 < t0 := by positivity
    have hexp1 : Real.exp (-2 / k) < 1 := by
      have : 0 < 2 / k := by positivity
      have e : -2 / k = -(2 / k) := by ring
      have h5 := Real.exp_lt_exp.mpr (show -2 / k < 0 by linarith)
      simpa using h5
    have ht0k : t0 < k := by
      rw [ht0]; nlinarith
    have hlog0 : Real.log t0 = Real.log k + (-2 / k) := by
      rw [ht0, Real.log_mul hk0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hh0 : 1 - t0 + k * Real.log t0 < 0 := by
      rw [hlog0]
      have : k * (-2 / k) = -2 := by field_simp
      have h3 : k * Real.log k ≤ 0 := by nlinarith
      nlinarith
    have hhk : 0 < 1 - k + k * Real.log k := by
      have h1 : Real.log (1 / k) < 1 / k - 1 := by
        apply Real.log_lt_sub_one_of_pos (by positivity)
        intro h; field_simp at h; linarith
      rw [one_div, Real.log_inv] at h1
      have h2 := mul_lt_mul_of_pos_left h1 hk0
      have : k * (k⁻¹ - 1) = 1 - k := by field_simp
      nlinarith
    have hcont : ContinuousOn (fun t : ℝ => 1 - t + k * Real.log t) (Set.Icc t0 k) := by
      apply ContinuousOn.add
      · fun_prop
      · apply ContinuousOn.mul continuousOn_const
        apply Real.continuousOn_log.mono
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (lt_of_lt_of_le ht0pos hx.1).ne'
    obtain ⟨t, ht, htz⟩ := intermediate_value_Icc ht0k.le hcont
      (show (0 : ℝ) ∈ Set.Icc (1 - t0 + k * Real.log t0) (1 - k + k * Real.log k) from
        ⟨hh0.le, hhk.le⟩)
    refine ⟨t, lt_of_lt_of_le ht0pos ht.1, ?_, htz⟩
    rcases ht.2.lt_or_eq with h | h
    · linarith
    · exfalso; rw [h] at htz; linarith
  have key : ∀ t1 t2 : ℝ, 0 < t1 → t1 < t2 → t2 < 1 →
      1 - t1 + k * Real.log t1 = 0 → 1 - t2 + k * Real.log t2 = 0 → False := by
    intro t1 t2 h1 h12 h2 e1 e2
    set a := (1 - t2) / (1 - t1) with ha
    have h1m : 0 < 1 - t1 := by linarith
    have hapos : 0 < a := div_pos (by linarith) h1m
    have hb : 0 < 1 - a := by
      rw [sub_pos, ha, div_lt_one h1m]; linarith
    have hc := hconc.2 (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr one_pos)
      (by intro h; linarith) hapos hb (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
    have hlin : a * t1 + (1 - a) * 1 = t2 := by
      rw [ha]; field_simp; ring
    rw [hlin] at hc
    have hat : a * (1 - t1) = 1 - t2 := by rw [ha]; field_simp
    have h3 := mul_lt_mul_of_pos_left hc hk0
    have e1' : k * Real.log t1 = t1 - 1 := by linarith
    have e2' : k * Real.log t2 = t2 - 1 := by linarith
    have h4 : k * (a * Real.log t1) = a * (t1 - 1) := by rw [← e1']; ring
    rw [h4, e2'] at h3
    nlinarith [hat]
  obtain ⟨t, ht0, ht1, hte⟩ := hex
  refine ⟨t, ⟨ht0, ht1, hte⟩, ?_⟩
  rintro t' ⟨ht0', ht1', hte'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key t' t ht0' h ht1 hte' hte
  · exact key t t' ht0 h ht1' hte hte'

theorem solution (P : Params) (hP : P.Standing) :
    ∃! p : ℝ, P.ca < p ∧ Eq14 P p := by
  obtain ⟨hmax, hr, hβ, _, hca, hcs⟩ := hP
  have hcsβ : P.cs < P.β := lt_of_le_of_lt (le_max_right _ _) hmax
  have hk0 : 0 < P.cs / P.β := div_pos hcs hβ
  have hk1 : P.cs / P.β < 1 := by rw [div_lt_one hβ]; exact hcsβ
  obtain ⟨t, ⟨ht0, ht1, hte⟩, hu⟩ := mc_h14 _ hk0 hk1
  have hpt : P.ca < P.ca / t := by
    rw [lt_div_iff₀ ht0]; nlinarith
  refine ⟨P.ca / t, ⟨hpt, ?_⟩, ?_⟩
  · unfold Eq14
    have : P.ca / (P.ca / t) = t := by field_simp
    rw [this]; exact hte
  · rintro p ⟨hp, hpe⟩
    have hp0 : 0 < p := hca.trans hp
    have h1 : P.ca / p = t := by
      apply hu
      refine ⟨div_pos hca hp0, ?_, hpe⟩
      rw [div_lt_one hp0]; exact hp
    rw [← h1]
    field_simp
