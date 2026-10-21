-- Prove2me | solution 1 for MatchCongestion.Welfare.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:31:33.232207+00:00
-- url     : https://prove2.me/submissions/48f3c3ec-44ea-4401-8ce4-f8c7e0fa3f83

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem mcE_exp_lt_one {x : ℝ} (h : x < 0) : Real.exp x < 1 := by
  simpa using Real.exp_lt_exp.mpr h

theorem mcE_one_sub_pos {x : ℝ} (h : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have := mcE_exp_lt_one (show -x < 0 by linarith); linarith

theorem mcE_pos (x : ℝ) : 0 < E x := by
  unfold E
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hx | hx
    · have h1 : 1 < Real.exp (-x) := by
        simpa using Real.exp_lt_exp.mpr (show 0 < -x by linarith)
      exact div_pos_of_neg_of_neg (by linarith) hx
    · exact div_pos (mcE_one_sub_pos hx) hx

theorem mcE_of_pos {x : ℝ} (h : 0 < x) : E x = (1 - Real.exp (-x)) / x := by
  unfold E; rw [if_neg h.ne']

theorem mcE_zero : E 0 = 1 := by simp [E]

theorem mcE_mul (x : ℝ) : E x * x = 1 - Real.exp (-x) := by
  unfold E
  split_ifs with h
  · subst h; simp
  · field_simp

theorem mcE_anti {x z : ℝ} (hx : 0 < x) (hxz : x < z) : E z < E x := by
  have hz : 0 < z := hx.trans hxz
  rw [mcE_of_pos hx, mcE_of_pos hz, div_lt_div_iff₀ hz hx]
  have hc := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-z))
    (by intro h; linarith) (show 0 < 1 - x / z by
      rw [sub_pos, div_lt_one hz]; exact hxz) (show 0 < x / z from div_pos hx hz)
    (by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_one, mul_zero, zero_add] at hc
  have e : x / z * -z = -x := by field_simp
  rw [e] at hc
  have := mul_lt_mul_of_pos_left hc hz
  have e2 : z * ((1 - x / z) + x / z * Real.exp (-z)) = z - x + x * Real.exp (-z) := by
    field_simp
  rw [e2] at this
  nlinarith

theorem solution (P : Params) (hr : 0 < P.r) (hβ : 0 < P.β) (hβ1 : P.β ≤ 1)
    (m α : ℝ) (hm : 0 ≤ m) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃! pq : ℝ × ℝ, IsMFSS P m α pq.1 pq.2 := by
  obtain ⟨hα0, hα1⟩ := hα
  rcases hm.eq_or_lt with hm0 | hmpos
  · -- m = 0
    subst hm0
    refine ⟨(α * P.β, 1), ?_, ?_⟩
    · show IsMFSS P 0 α (α * P.β) 1
      unfold IsMFSS
      simp [mcE_zero]
    · rintro ⟨p, q⟩ ⟨h1, h2⟩
      simp only [zero_mul, mul_zero, zero_mul, mcE_zero] at h1 h2
      simp only [Prod.mk.injEq]
      refine ⟨?_, h1⟩
      rw [h2]; simp [mcE_zero]
  rcases hα0.eq_or_lt with hαz | hαpos
  · -- α = 0
    subst hαz
    refine ⟨(0, 1), ?_, ?_⟩
    · show IsMFSS P m 0 0 1
      unfold IsMFSS
      simp [mcE_zero]
    · rintro ⟨p, q⟩ ⟨h1, h2⟩
      dsimp only at h1 h2
      simp only [zero_mul] at h2
      subst h2
      refine Prod.ext rfl ?_
      show q = 1
      rw [h1]; simp [mcE_zero]
  -- general case
  set Y : ℝ → ℝ := fun p => P.r * m * P.β * E (m * p) with hY
  have hYpos : ∀ p, 0 < Y p := fun p => by
    simp only [hY]; have := mcE_pos (m * p); positivity
  have hiff : ∀ p, 0 < p → (p = α * P.β * E (Y p) ↔
      P.r * (1 - Real.exp (-(m * p))) = α * (1 - Real.exp (-(Y p)))) := by
    intro p hp
    have hy := hYpos p
    have hpY : p * Y p = P.β * (P.r * (1 - Real.exp (-(m * p)))) := by
      rw [← mcE_mul (m * p)]; simp only [hY]; ring
    rw [mcE_of_pos hy]
    constructor
    · intro h
      have h' : p * Y p = α * P.β * ((1 - Real.exp (-(Y p))) / Y p) * Y p := by
        rw [← h]
      have : p * Y p = P.β * (α * (1 - Real.exp (-(Y p)))) := by
        rw [h']; field_simp
      rw [hpY] at this
      exact mul_left_cancel₀ hβ.ne' this
    · intro h
      rw [mul_div_assoc', eq_div_iff hy.ne', hpY, h]
      ring
  -- solutions have p > 0
  have hsolpos : ∀ p q, IsMFSS P m α p q → 0 < p ∧ q = E (m * p) ∧ p = α * P.β * E (Y p) := by
    rintro p q ⟨h1, h2⟩
    have h3 : P.r * m * P.β * q = Y p := by rw [h1]
    rw [h3] at h2
    refine ⟨?_, h1, h2⟩
    rw [h2]; have := mcE_pos (Y p); positivity
  -- uniqueness of positive root
  have huniq : ∀ p1 p2, 0 < p1 → p1 < p2 →
      P.r * (1 - Real.exp (-(m * p1))) = α * (1 - Real.exp (-(Y p1))) →
      P.r * (1 - Real.exp (-(m * p2))) = α * (1 - Real.exp (-(Y p2))) → False := by
    intro p1 p2 h1 h12 e1 e2
    have hE : E (m * p2) < E (m * p1) := mcE_anti (by positivity) (by nlinarith)
    have hY12 : Y p2 < Y p1 := by
      simp only [hY]
      have : 0 < P.r * m * P.β := by positivity
      exact mul_lt_mul_of_pos_left hE this
    have h3 : Real.exp (-(Y p1)) < Real.exp (-(Y p2)) := Real.exp_lt_exp.mpr (by linarith)
    have h4 : Real.exp (-(m * p2)) < Real.exp (-(m * p1)) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    nlinarith [mul_lt_mul_of_pos_left h3 hαpos, mul_lt_mul_of_pos_left h4 hr]
  -- existence of a positive root
  have hex : ∃ p, 0 < p ∧
      P.r * (1 - Real.exp (-(m * p))) = α * (1 - Real.exp (-(Y p))) := by
    set H : ℝ → ℝ := fun p => P.r * (1 - Real.exp (-(m * p))) - α * (1 - Real.exp (-(Y p))) with hH
    -- large point p = 2
    have hH2 : 0 < H 2 := by
      simp only [hH]
      have hy := hYpos 2
      have hpY : 2 * Y 2 = P.β * (P.r * (1 - Real.exp (-(m * 2)))) := by
        rw [← mcE_mul (m * 2)]; simp only [hY]; ring
      have h1 : 1 - Real.exp (-(Y 2)) ≤ Y 2 := by
        have := Real.add_one_le_exp (-(Y 2)); linarith
      have h2 : 0 < 1 - Real.exp (-(m * 2)) := mcE_one_sub_pos (by positivity)
      have h3 : α * (1 - Real.exp (-(Y 2))) ≤ α * Y 2 := mul_le_mul_of_nonneg_left h1 hα0
      have h4 : α * P.β ≤ 1 := by nlinarith
      nlinarith [mul_pos hr h2, mul_pos (mul_pos hr h2) (by linarith : 0 < 2 - α * P.β)]
    -- small point
    set y1 := P.r * m * P.β * E (m * 1) with hy1
    have hy1pos : 0 < y1 := by have := mcE_pos (m * 1); positivity
    set c := α * (1 - Real.exp (-y1)) with hc
    have hcpos : 0 < c := mul_pos hαpos (mcE_one_sub_pos hy1pos)
    set ps := min (1 / 2) (c / (2 * P.r * m)) with hps
    have hps0 : 0 < ps := lt_min (by norm_num) (by positivity)
    have hps1 : ps < 1 := by have := min_le_left (1 / 2 : ℝ) (c / (2 * P.r * m)); linarith
    have hpsc : P.r * m * ps ≤ c / 2 := by
      have h := min_le_right (1 / 2 : ℝ) (c / (2 * P.r * m))
      have hrm : 0 < P.r * m := by positivity
      have : P.r * m * ps ≤ P.r * m * (c / (2 * P.r * m)) := mul_le_mul_of_nonneg_left h hrm.le
      have e : P.r * m * (c / (2 * P.r * m)) = c / 2 := by field_simp
      linarith
    have hHs : H ps < 0 := by
      simp only [hH]
      have hYs : y1 < Y ps := by
        simp only [hY, hy1]
        have : 0 < P.r * m * P.β := by positivity
        exact mul_lt_mul_of_pos_left (mcE_anti (by positivity) (by nlinarith)) this
      have h1 : Real.exp (-(Y ps)) < Real.exp (-y1) := Real.exp_lt_exp.mpr (by linarith)
      have h2 : 1 - Real.exp (-(m * ps)) ≤ m * ps := by
        have := Real.add_one_le_exp (-(m * ps)); linarith
      have h3 := mul_lt_mul_of_pos_left h1 hαpos
      have h4 := mul_le_mul_of_nonneg_left h2 hr.le
      nlinarith
    have hcont : ContinuousOn H (Set.Icc ps 2) := by
      have hEc : ContinuousOn (fun p : ℝ => E (m * p)) (Set.Icc ps 2) := by
        have : ContinuousOn (fun p : ℝ => (1 - Real.exp (-(m * p))) / (m * p)) (Set.Icc ps 2) := by
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro p hp
          have : 0 < p := lt_of_lt_of_le hps0 hp.1
          positivity
        refine this.congr ?_
        intro p hp
        have : 0 < p := lt_of_lt_of_le hps0 hp.1
        exact mcE_of_pos (by positivity)
      simp only [hH, hY]
      apply ContinuousOn.sub (by fun_prop)
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.sub continuousOn_const
      apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.neg
      exact ContinuousOn.mul continuousOn_const hEc
    obtain ⟨p, hp, hz⟩ := intermediate_value_Icc (by linarith : ps ≤ 2) hcont
      (show (0 : ℝ) ∈ Set.Icc (H ps) (H 2) from ⟨hHs.le, hH2.le⟩)
    refine ⟨p, lt_of_lt_of_le hps0 hp.1, ?_⟩
    simp only [hH] at hz
    linarith
  obtain ⟨p0, hp0, hroot⟩ := hex
  refine ⟨(p0, E (m * p0)), ⟨rfl, ?_⟩, ?_⟩
  · show p0 = α * P.β * E (P.r * m * P.β * E (m * p0))
    exact (hiff p0 hp0).mpr hroot
  · rintro ⟨p, q⟩ hs
    obtain ⟨hp, hq, he⟩ := hsolpos p q hs
    have hroot' := (hiff p hp).mp he
    have : p = p0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact huniq p p0 hp h hroot' hroot
      · exact huniq p0 p hp0 h hroot hroot'
    subst this
    exact Prod.ext rfl hq
