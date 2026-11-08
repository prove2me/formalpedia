-- Prove2me | solution 1 for ImpulseGames.CostMonotonicity.xi_unique_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:06:04.361743+00:00
-- url     : https://prove2.me/submissions/d1d10f5a-db59-4bbf-b625-0a6b626992a2

import Mathlib
import Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds

namespace ImpCostAux
open ImpulseGames.CostMonotonicity

/-- E(t) := log(1+t) - log(1-t). -/
lemma E_hasSum {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * t ^ (2 * k + 1))
      (Real.log (1 + t) - Real.log (1 - t)) :=
  Real.hasSum_log_sub_log_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith)

lemma key1 {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t < 1) :
    (Real.log (1 + s) - Real.log (1 - s)) - 2 * s
      < (Real.log (1 + t) - Real.log (1 - t)) - 2 * t := by
  have hS := (E_hasSum hs (by linarith)).sub (hasSum_ite_eq (0 : ℕ) (2 * s))
  have hT := (E_hasSum (by linarith) ht).sub (hasSum_ite_eq (0 : ℕ) (2 * t))
  refine hasSum_lt (i := 1) ?_ ?_ hS hT
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk0 : k ≠ 0 := by omega
      simp only [hk0, if_false, sub_zero]
      have : s ^ (2 * k + 1) ≤ t ^ (2 * k + 1) := pow_le_pow_left₀ hs hst.le _
      have hpos : (0:ℝ) ≤ 2 * (1 / (2 * (k:ℝ) + 1)) := by positivity
      exact mul_le_mul_of_nonneg_left this hpos
  · simp only [one_ne_zero, if_false, sub_zero]
    have : s ^ (2 * 1 + 1) < t ^ (2 * 1 + 1) := pow_lt_pow_left₀ hst hs (by norm_num)
    have hpos : (0:ℝ) < 2 * (1 / (2 * ((1:ℕ):ℝ) + 1)) := by positivity
    exact mul_lt_mul_of_pos_left this hpos

lemma key2 {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    (Real.log (1 + s) - Real.log (1 - s)) / s
      ≤ (Real.log (1 + t) - Real.log (1 - t)) / t := by
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  have hS := (E_hasSum hs.le (by linarith)).div_const s
  have hT := (E_hasSum ht0.le ht).div_const t
  refine hasSum_le ?_ hS hT
  intro k
  have e1 : (2:ℝ) * (1 / (2 * k + 1)) * s ^ (2 * k + 1) / s
      = 2 * (1 / (2 * k + 1)) * s ^ (2 * k) := by
    rw [pow_succ]; field_simp
  have e2 : (2:ℝ) * (1 / (2 * k + 1)) * t ^ (2 * k + 1) / t
      = 2 * (1 / (2 * k + 1)) * t ^ (2 * k) := by
    rw [pow_succ]; field_simp
  simp only [e1, e2]
  have : s ^ (2 * k) ≤ t ^ (2 * k) := pow_le_pow_left₀ hs.le hst _
  have hpos : (0:ℝ) ≤ 2 * (1 / (2 * (k:ℝ) + 1)) := by positivity
  exact mul_le_mul_of_nonneg_left this hpos

/-- G(y) = η log((η+y)/(η-y)) - 2y. -/
noncomputable def G (P : Params) (y : ℝ) : ℝ :=
  P.eta * Real.log ((P.eta + y) / (P.eta - y)) - 2 * y

lemma eta_pos (P : Params) (hP : P.Standing) : 0 < P.eta :=
  div_pos hP.one_sub_lam_mul_rho_pos hP.rho_pos

lemma theta_pos (P : Params) (hP : P.Standing) : 0 < P.theta := by
  unfold Params.theta
  apply Real.sqrt_pos.mpr
  have := hP.sigma_pos
  have := hP.rho_pos
  positivity

lemma F_eq (P : Params) (c y : ℝ) : P.F c y = P.theta * c - G P y := by
  unfold Params.F G; ring

lemma G_eq (P : Params) (hP : P.Standing) {y : ℝ} (h0 : 0 ≤ y) (h1 : y < P.eta) :
    G P y = P.eta * ((Real.log (1 + y / P.eta) - Real.log (1 - y / P.eta)) - 2 * (y / P.eta)) := by
  have he := eta_pos P hP
  unfold G
  have hq : (P.eta + y) / (P.eta - y) = (1 + y / P.eta) / (1 - y / P.eta) := by
    field_simp
  have ha : 0 < 1 + y / P.eta := by have := div_nonneg h0 he.le; linarith
  have hb : 0 < 1 - y / P.eta := by
    have : y / P.eta < 1 := (div_lt_one he).mpr h1
    linarith
  rw [hq, Real.log_div ha.ne' hb.ne']
  field_simp

lemma G_strictMonoOn (P : Params) (hP : P.Standing) : StrictMonoOn (G P) (Set.Ico 0 P.eta) := by
  have he := eta_pos P hP
  intro a ha b hb hab
  rw [G_eq P hP ha.1 ha.2, G_eq P hP hb.1 hb.2]
  apply mul_lt_mul_of_pos_left _ he
  exact key1 (div_nonneg ha.1 he.le) (div_lt_div_of_pos_right hab he) ((div_lt_one he).mpr hb.2)

lemma G_zero (P : Params) : G P 0 = 0 := by
  unfold G; simp

lemma G_contOn (P : Params) (hP : P.Standing) {b : ℝ} (hb : b < P.eta) :
    ContinuousOn (G P) (Set.Icc 0 b) := by
  have he := eta_pos P hP
  unfold G
  apply ContinuousOn.sub _ (by fun_prop)
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy; have := hy.2; linarith
  · intro y hy
    have := hy.1; have := hy.2
    apply div_ne_zero <;> linarith

lemma exists_zero (P : Params) (hP : P.Standing) (c : ℝ) (hc : 0 < c) :
    ∃ z ∈ Set.Ioo 0 P.eta, G P z = P.theta * c := by
  have he := eta_pos P hP
  have hth := theta_pos P hP
  set M := Real.exp ((P.theta * c + 2 * P.eta) / P.eta) with hM
  have hM1 : 1 < M := by
    rw [hM]; apply Real.one_lt_exp_iff.mpr; positivity
  set b := P.eta * (M - 1) / (M + 1) with hbdef
  have hb0 : 0 < b := by rw [hbdef]; apply div_pos _ (by linarith); nlinarith
  have hbη : b < P.eta := by
    rw [hbdef, div_lt_iff₀ (by linarith)]; nlinarith
  have hGb : P.theta * c < G P b := by
    unfold G
    have hq : (P.eta + b) / (P.eta - b) = M := by
      rw [hbdef]; field_simp; ring
    rw [hq, hM, Real.log_exp]
    field_simp
    nlinarith
  have hivt := intermediate_value_Icc hb0.le (G_contOn P hP hbη)
  rw [G_zero] at hivt
  obtain ⟨z, hz, hGz⟩ := hivt ⟨by positivity, hGb.le⟩
  refine ⟨z, ⟨?_, lt_of_le_of_lt hz.2 hbη⟩, hGz⟩
  rcases hz.1.lt_or_eq with h | h
  · exact h
  · subst h; rw [G_zero] at hGz; nlinarith

lemma xi_spec (P : Params) (hP : P.Standing) (c : ℝ) (hc : 0 < c) :
    P.xi c ∈ Set.Ioo 0 P.eta ∧ G P (P.xi c) = P.theta * c := by
  obtain ⟨z, hz, hGz⟩ := exists_zero P hP c hc
  have hset : {y : ℝ | y ∈ Set.Ioo 0 P.eta ∧ 0 ≤ P.F c y} = Set.Ioc 0 z := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_Ioc, F_eq]
    constructor
    · rintro ⟨⟨h0, h1⟩, hF⟩
      refine ⟨h0, ?_⟩
      by_contra hyz
      push_neg at hyz
      have := G_strictMonoOn P hP ⟨hz.1.le, hz.2⟩ ⟨h0.le, h1⟩ hyz
      linarith
    · rintro ⟨h0, hyz⟩
      refine ⟨⟨h0, lt_of_le_of_lt hyz hz.2⟩, ?_⟩
      have := (G_strictMonoOn P hP).monotoneOn ⟨h0.le, lt_of_le_of_lt hyz hz.2⟩ ⟨hz.1.le, hz.2⟩ hyz
      linarith
  have hxi : P.xi c = z := by
    unfold Params.xi; rw [hset, csSup_Ioc hz.1]
  rw [hxi]; exact ⟨hz, hGz⟩


end ImpCostAux

open ImpulseGames.CostMonotonicity in
theorem solution (P : Params) (hP : P.Standing) (c : ℝ) (hc : 0 < c) :
    P.xi c ∈ Set.Ioo 0 P.eta ∧ P.F c (P.xi c) = 0 ∧
      ∀ y ∈ Set.Ioo 0 P.eta, P.F c y = 0 → y = P.xi c := by
  obtain ⟨hx, hG⟩ := ImpCostAux.xi_spec P hP c hc
  refine ⟨hx, by rw [ImpCostAux.F_eq, hG]; ring, ?_⟩
  intro y hy hF
  rw [ImpCostAux.F_eq] at hF
  apply (ImpCostAux.G_strictMonoOn P hP).injOn ⟨hy.1.le, hy.2⟩ ⟨hx.1.le, hx.2⟩
  rw [hG]; linarith
