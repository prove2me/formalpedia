-- Prove2me | solution 1 for NaiveLearn.OverMatch.ode_consensus
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T13:25:07.998123+00:00
-- url     : https://prove2.me/submissions/55e12423-3859-4ee0-9737-30dbb8ebd123

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

namespace NLc

lemma mu_pos {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) : ∀ i, 0 < μ i := by
  obtain ⟨hμ0, hμ1, hμW⟩ := hμ
  have hpred : ∀ j k, μ j = 0 → 0 < W k j → μ k = 0 := by
    intro j k hj hkj
    have hcol : ∑ l, μ l * W l j = μ j := congrFun hμW j
    rw [hj] at hcol
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ μ l * W l j := fun l _ =>
      mul_nonneg (hμ0 l) (Matrix.nonneg_of_mem_rowStochastic hW.1)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hcol k (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := hcon
  have hi0 : μ i = 0 := le_antisymm hi (hμ0 i)
  letI := Matrix.toQuiver W
  have hpath : ∀ (k b : Fin m) (P : Quiver.Path k b), μ b = 0 → μ k = 0 := by
    intro k b P
    induction P with
    | nil => exact id
    | cons P e ih => exact fun hc => ih (hpred _ _ hc e.down)
  have hall : ∀ k, μ k = 0 := by
    intro k
    obtain ⟨P, _⟩ := hW.2.1.connected k i
    exact hpath k i P hi0
  have : ∑ k, μ k = 0 := Finset.sum_eq_zero fun k _ => hall k
  linarith


lemma dirichlet {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, μ i * W i j = μ j) (y : Fin m → ℝ) :
    2 * ∑ i, μ i * y i * (W.mulVec y i - y i) =
      -(∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2) := by
  have e1 : ∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2 =
      ∑ i, ∑ j, μ i * W i j * y i ^ 2 - 2 * ∑ i, ∑ j, μ i * W i j * y i * y j +
        ∑ i, ∑ j, μ i * W i j * y j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : ∑ i, ∑ j, μ i * W i j * y i ^ 2 = ∑ i, μ i * y i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ j, μ i * W i j * y i ^ 2) = μ i * y i ^ 2 * ∑ j, W i j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hrow i, mul_one]
  have e3 : ∑ i, ∑ j, μ i * W i j * y j ^ 2 = ∑ i, μ i * y i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (∑ i, μ i * W i j * y j ^ 2) = (∑ i, μ i * W i j) * y j ^ 2 by
      rw [Finset.sum_mul], hcol j]
  have e4 : ∑ i, ∑ j, μ i * W i j * y i * y j = ∑ i, μ i * y i * W.mulVec y i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e5 : ∑ i, μ i * y i * (W.mulVec y i - y i) =
      ∑ i, μ i * y i * W.mulVec y i - ∑ i, μ i * y i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3, e4, e5]
  ring

lemma const_of_dirichlet_zero {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hpos : ∀ i, 0 < μ i) (y : Fin m → ℝ)
    (h : ∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2 = 0) : ∀ i j, y i = y j := by
  have hnn : ∀ i j, 0 ≤ μ i * W i j * (y i - y j) ^ 2 := fun i j =>
    mul_nonneg (mul_nonneg (hpos i).le (Matrix.nonneg_of_mem_rowStochastic hW.1)) (sq_nonneg _)
  have hz : ∀ i j, μ i * W i j * (y i - y j) ^ 2 = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
      fun j _ => hnn i j)).1 h i (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 h1 j (Finset.mem_univ _)
  have hedge : ∀ i j, 0 < W i j → y i = y j := by
    intro i j hij
    have := hz i j
    rcases mul_eq_zero.1 this with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 (hpos i).ne'
      · exact absurd h3 hij.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
      linarith
  letI := Matrix.toQuiver W
  have hpath : ∀ (k b : Fin m) (P : Quiver.Path k b), y k = y b := by
    intro k b P
    induction P with
    | nil => rfl
    | cons P e ih => exact ih.trans (hedge _ _ e.down)
  intro i j
  obtain ⟨P, _⟩ := hW.2.1.connected i j
  exact hpath i j P

lemma poincare {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ y : Fin m → ℝ, ∑ i, μ i * y i = 0 →
      κ * ∑ i, μ i * y i ^ 2 ≤ ∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2 := by
  have hpos := mu_pos W μ hW hμ
  set D : (Fin m → ℝ) → ℝ := fun y => ∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2
  set V : (Fin m → ℝ) → ℝ := fun y => ∑ i, μ i * y i ^ 2
  set L : (Fin m → ℝ) → ℝ := fun y => ∑ i, μ i * y i
  have hDc : Continuous D := by fun_prop
  have hVc : Continuous V := by fun_prop
  have hLc : Continuous L := by fun_prop
  set S := {y : Fin m → ℝ | L y = 0 ∧ V y = 1}
  have hDnn : ∀ y, 0 ≤ D y := fun y => Finset.sum_nonneg fun i _ => Finset.sum_nonneg
    fun j _ => mul_nonneg (mul_nonneg (hpos i).le (Matrix.nonneg_of_mem_rowStochastic hW.1))
      (sq_nonneg _)
  have hVnn : ∀ y, 0 ≤ V y := fun y => Finset.sum_nonneg fun i _ =>
    mul_nonneg (hpos i).le (sq_nonneg _)
  -- homogeneity
  have hDs : ∀ (c : ℝ) y, D (c • y) = c ^ 2 * D y := by
    intro c y; simp only [D, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hVs : ∀ (c : ℝ) y, V (c • y) = c ^ 2 * V y := by
    intro c y; simp only [V, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hLs : ∀ (c : ℝ) y, L (c • y) = c * L y := by
    intro c y; simp only [L, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- D > 0 on S
  have hDpos : ∀ y ∈ S, 0 < D y := by
    rintro y ⟨hL, hV⟩
    rcases (hDnn y).lt_or_eq with h | h
    · exact h
    · exfalso
      have hc := const_of_dirichlet_zero W μ hW hpos y h.symm
      have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty] at hn
        have := hμ.2.1; rw [hn, Finset.sum_empty] at this; norm_num at this
      obtain ⟨i0, _⟩ := hne
      have hy0 : ∀ i, y i = y i0 := fun i => hc i i0
      have : L y = y i0 := by
        simp only [L, hy0, ← Finset.sum_mul, hμ.2.1, one_mul]
      have hyz : y i0 = 0 := by rw [← this]; exact hL
      have : V y = 0 := by simp [V, hy0, hyz]
      rw [hV] at this; norm_num at this
  -- S bounded and closed
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_eq hLc continuous_const).inter (isClosed_eq hVc continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨∑ i, (1 / μ i + 1), fun y hy => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
        by have := one_div_pos.2 (hpos i); linarith)).2 fun i => ?_
      have hVi : μ i * y i ^ 2 ≤ 1 := by
        have := Finset.single_le_sum (f := fun j => μ j * y j ^ 2)
          (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _)) (Finset.mem_univ i)
        rw [← hy.2]; exact this
      have hμi := hpos i
      have h1 : y i ^ 2 ≤ 1 / μ i := by rw [le_div_iff₀ hμi]; linarith
      have h2 : |y i| ≤ 1 + y i ^ 2 := by nlinarith [abs_nonneg (y i), sq_abs (y i)]
      rw [Real.norm_eq_abs]
      calc |y i| ≤ 1 / μ i + 1 := by linarith
        _ ≤ ∑ j, (1 / μ j + 1) := Finset.single_le_sum (f := fun j => 1 / μ j + 1)
            (fun j _ => by have := one_div_pos.2 (hpos j); linarith) (Finset.mem_univ i)
  have hscale : ∀ y, L y = 0 → V y ≠ 0 → (1 / Real.sqrt (V y)) • y ∈ S := by
    intro y hL hV
    have hVp : 0 < V y := lt_of_le_of_ne (hVnn y) (Ne.symm hV)
    refine ⟨by rw [hLs, hL, mul_zero], ?_⟩
    rw [hVs, div_pow, one_pow, Real.sq_sqrt hVp.le, one_div_mul_cancel hVp.ne']
  by_cases hS : S.Nonempty
  · obtain ⟨y0, hy0, hmin⟩ := hSc.exists_isMinOn hS hDc.continuousOn
    refine ⟨D y0, hDpos y0 hy0, fun y hL => ?_⟩
    by_cases hV : V y = 0
    · show D y0 * V y ≤ D y
      rw [hV, mul_zero]; exact hDnn y
    · have hVp : 0 < V y := lt_of_le_of_ne (hVnn y) (Ne.symm hV)
      have h1 := hmin (hscale y hL hV)
      simp only [Set.mem_setOf_eq] at h1
      rw [hDs, div_pow, one_pow, Real.sq_sqrt hVp.le] at h1
      show D y0 * V y ≤ D y
      have := mul_le_mul_of_nonneg_right h1 hVp.le
      rwa [mul_comm (1 / V y), mul_assoc, one_div_mul_cancel hVp.ne', mul_one] at this
  · refine ⟨1, one_pos, fun y hL => ?_⟩
    by_cases hV : V y = 0
    · show 1 * V y ≤ D y
      rw [hV, mul_zero]; exact hDnn y
    · exact absurd ⟨_, hscale y hL hV⟩ hS

end NLc

open NLc in
theorem solution {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) (x : Fin m → ℝ)
    (z : ℝ → (Fin m → ℝ)) (hz : IsODESolution (fun v => W.mulVec v - v) z) (hz0 : z 0 = x) :
    Tendsto z atTop (𝓝 (fun _ => ∑ i, μ i * x i)) := by
  have hpos := mu_pos W μ hW hμ
  obtain ⟨κ, hκ, hP⟩ := poincare W μ hW hμ
  have hrow : ∀ i, ∑ j, W i j = 1 := fun i => Matrix.sum_row_of_mem_rowStochastic hW.1 i
  have hcol : ∀ j, ∑ i, μ i * W i j = μ j := fun j => congrFun hμ.2.2 j
  set c := ∑ i, μ i * x i with hc
  have hzi : ∀ t, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s => z s i)
      (W.mulVec (z t) i - z t i) (Set.Ici t) t := fun t ht i =>
    hasDerivWithinAt_pi.1 (hz.2 t ht) i
  have hzc : ∀ i, ContinuousOn (fun s => z s i) (Set.Ici 0) := fun i =>
    (continuous_apply i).comp_continuousOn hz.1
  -- conservation of the weighted mean
  have hmean : ∀ t, 0 ≤ t → ∑ i, μ i * z t i = c := by
    intro t ht
    have hder : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt (fun s => ∑ i, μ i * z s i)
        (∑ i, μ i * (W.mulVec (z s) i - z s i)) (Set.Ici s) s := by
      intro s hs
      exact HasDerivWithinAt.fun_sum fun i _ => (hzi s hs.1 i).const_mul (μ i)
    have hzero : ∀ s, ∑ i, μ i * (W.mulVec (z s) i - z s i) = 0 := by
      intro s
      have : ∑ i, μ i * W.mulVec (z s) i = ∑ j, μ j * z s j := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hcol j, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun i _ => mul_sub (μ i) _ _, Finset.sum_sub_distrib, this,
        sub_self]
    have hcont : ContinuousOn (fun s => ∑ i, μ i * z s i) (Set.Icc 0 t) :=
      (continuousOn_finsetSum _ fun i _ => (hzc i).const_smul (μ i)).mono Set.Icc_subset_Ici_self
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder
      (fun s _ => by rw [hzero, norm_zero]) t ⟨ht, le_rfl⟩
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
    rw [this, hz0]
  -- Lyapunov function
  set V : ℝ → ℝ := fun s => ∑ i, μ i * (z s i - c) ^ 2 with hV
  set D : (Fin m → ℝ) → ℝ := fun y => ∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2
  have hVnn : ∀ s, 0 ≤ V s := fun s => Finset.sum_nonneg fun i _ =>
    mul_nonneg (hpos i).le (sq_nonneg _)
  have hVder : ∀ s, 0 ≤ s → HasDerivWithinAt V (-D (fun i => z s i - c)) (Set.Ici s) s := by
    intro s hs
    have h := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
      (((hzi s hs i).sub_const c).pow 2).const_mul (μ i)
    have hWy : ∀ i, W.mulVec (z s) i - z s i =
        W.mulVec (fun j => z s j - c) i - (z s i - c) := by
      intro i
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hrow i]
      ring
    have hd := dirichlet W μ hrow hcol (fun j => z s j - c)
    have heq : ∑ i, μ i * ((2 : ℕ) * (z s i - c) ^ (2 - 1) * (W.mulVec (z s) i - z s i)) =
        -D (fun i => z s i - c) := by
      show _ = -(∑ i, ∑ j, μ i * W i j * ((z s i - c) - (z s j - c)) ^ 2)
      rw [← hd, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hWy i]
      push_cast
      ring
    exact h.congr_deriv heq
  have hVbound : ∀ s, 0 ≤ s → -D (fun i => z s i - c) ≤ -κ * V s := by
    intro s hs
    have hL : ∑ i, μ i * (z s i - c) = 0 := by
      rw [Finset.sum_congr rfl fun i _ => mul_sub (μ i) _ _, Finset.sum_sub_distrib,
        hmean s hs, ← Finset.sum_mul, hμ.2.1, one_mul, sub_self]
    have := hP (fun i => z s i - c) hL
    simp only [D, V] at this ⊢
    linarith
  have hVcont : ContinuousOn V (Set.Ici 0) :=
    continuousOn_finsetSum _ fun i _ => ((hzc i).sub continuousOn_const).pow 2 |>.const_smul (μ i)
  have hVexp : ∀ t, 0 ≤ t → V t ≤ V 0 * Real.exp (-κ * t) := by
    intro t ht
    have := le_gronwallBound_of_liminf_deriv_right_le (f := V)
      (f' := fun s => -D (fun i => z s i - c)) (δ := V 0) (K := -κ) (ε := 0) (a := 0) (b := t)
      (hVcont.mono Set.Icc_subset_Ici_self)
      (fun s hs r hr => (hVder s hs.1).liminf_right_slope_le hr) le_rfl
      (fun s hs => by rw [add_zero]; exact hVbound s hs.1) t ⟨ht, le_rfl⟩
    rwa [gronwallBound_ε0, sub_zero] at this
  have hV0 : Tendsto V atTop (𝓝 0) := by
    have hexp : Tendsto (fun t => V 0 * Real.exp (-κ * t)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith :
        -κ < 0)))
      simpa using this.const_mul (V 0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall hVnn) ?_
    filter_upwards [eventually_ge_atTop 0] with t ht using hVexp t ht
  rw [tendsto_pi_nhds]
  intro i
  have hsq : Tendsto (fun s => (z s i - c) ^ 2) atTop (𝓝 0) := by
    have h1 := hV0.div_const (μ i)
    rw [zero_div] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun s => sq_nonneg _) (fun s => ?_)
    rw [le_div_iff₀ (hpos i), mul_comm]
    exact Finset.single_le_sum (f := fun j => μ j * (z s j - c) ^ 2)
      (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _)) (Finset.mem_univ i)
  have habs : Tendsto (fun s => |z s i - c|) atTop (𝓝 0) := by
    have := hsq.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    exact this
  have := (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have h2 := this.add_const c
  simp only [sub_add_cancel, zero_add] at h2
  exact h2
