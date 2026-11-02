-- Prove2me | solution 1 for NaiveLearn.OverMatch.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T13:33:58.323123+00:00
-- url     : https://prove2.me/submissions/26ade506-a3c6-45ab-a462-ae641c8f4054

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

namespace NL4

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


lemma wsum_mem {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (a : Fin m → ℝ) (ha : ∀ j, a j ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    ∑ j, W i j * a j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW) (ha j).1
  · calc ∑ j, W i j * a j ≤ ∑ j, W i j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (ha j).2 (Matrix.nonneg_of_mem_rowStochastic hW)
      _ = 1 := by simp [Matrix.sum_row_of_mem_rowStochastic hW]

lemma field_mem {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (v : Fin m → ℝ) (i : Fin m) :
    W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (v j))) i ∈ Set.Icc (0 : ℝ) 1 :=
  wsum_mem W hW _ (fun j => hmaps (Set.projIcc (0 : ℝ) 1 zero_le_one (v j)).2) i

lemma coord_deriv {m : ℕ} (σ : ℝ → ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (z : ℝ → (Fin m → ℝ))
    (hz : IsODESolution (meanField σ W) z) (t : ℝ) (ht : 0 ≤ t) (i : Fin m) :
    HasDerivWithinAt (fun s => z s i)
      (W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z t j))) i - z t i)
      (Set.Ici t) t :=
  hasDerivWithinAt_pi.1 (hz.2 t ht) i

/-- The cube is forward invariant. -/
lemma cube_inv {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (z : ℝ → (Fin m → ℝ)) (hz : IsODESolution (meanField σ W) z)
    (hz0 : ∀ i, z 0 i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t, 0 ≤ t → ∀ i, z t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t ht i
  have hc : ContinuousOn (fun s => z s i) (Set.Icc 0 t) :=
    ((continuous_apply i).comp_continuousOn hz.1).mono Set.Icc_subset_Ici_self
  constructor
  · have := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => -z s i)
      (f' := fun s => -(W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z s j))) i
        - z s i)) (δ := -z 0 i) (K := -1) (ε := 0) (a := 0) (b := t) hc.neg
      (fun s hs r hr => ((coord_deriv σ W z hz s hs.1 i).neg).liminf_right_slope_le hr) le_rfl
      (fun s hs => by
        have := (field_mem σ hmaps W hW (z s) i).1
        linarith) t ⟨ht, le_rfl⟩
    rw [gronwallBound_ε0] at this
    have h0 := (hz0 i).1
    have : -z t i ≤ 0 := this.trans (by
      have := Real.exp_pos (-1 * (t - 0)); nlinarith)
    linarith
  · have := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => z s i - 1)
      (f' := fun s => W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z s j))) i
        - z s i) (δ := z 0 i - 1) (K := -1) (ε := 0) (a := 0) (b := t) (hc.sub continuousOn_const)
      (fun s hs r hr => ((coord_deriv σ W z hz s hs.1 i).sub_const 1).liminf_right_slope_le hr)
      le_rfl
      (fun s hs => by
        have := (field_mem σ hmaps W hW (z s) i).2
        linarith) t ⟨ht, le_rfl⟩
    rw [gronwallBound_ε0] at this
    have h0 := (hz0 i).2
    have : z t i - 1 ≤ 0 := this.trans (by
      have := Real.exp_pos (-1 * (t - 0)); nlinarith)
    linarith


lemma sigma_up (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hcont : ContinuousOn σ (Set.Icc 0 1))
    (hgt : ∀ x ∈ Set.Ioo p 1, x < σ x) : ∀ x ∈ Set.Ioc p 1, x ≤ σ x := by
  rintro x ⟨hx1, hx2⟩
  rcases lt_or_eq_of_le hx2 with h | h
  · exact (hgt x ⟨hx1, h⟩).le
  · subst h
    have hc : ContinuousWithinAt σ (Set.Ioo p 1) 1 :=
      (hcont.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono
        (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hp0.le le_rfl))
    have ht : Tendsto σ (𝓝[<] (1 : ℝ)) (𝓝 (σ 1)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hx1]; exact hc.tendsto
    have hev : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ≤ σ y := by
      filter_upwards [Ioo_mem_nhdsLT hx1] with y hy using (hgt y hy).le
    exact le_of_tendsto_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ht hev

lemma mean_deriv {m : ℕ} (σ : ℝ → ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hcol : ∀ j, ∑ i, μ i * W i j = μ j) (z : ℝ → (Fin m → ℝ))
    (hz : IsODESolution (meanField σ W) z)
    (hcube : ∀ t, 0 ≤ t → ∀ i, z t i ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∑ i, μ i * z s i) (∑ i, μ i * (σ (z t i) - z t i))
      (Set.Ici t) t := by
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
    (coord_deriv σ W z hz t ht i).const_mul (μ i)
  refine h.congr_deriv ?_
  have hp : ∀ j, (Set.projIcc (0 : ℝ) 1 zero_le_one (z t j) : ℝ) = z t j := fun j => by
    simp [Set.projIcc_of_mem zero_le_one (hcube t ht j)]
  simp only [hp]
  have : ∑ i, μ i * W.mulVec (fun j => σ (z t j)) i = ∑ j, μ j * σ (z t j) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hcol j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun i _ => mul_sub (μ i) _ _, Finset.sum_sub_distrib, this,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring


lemma V_bound {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ) (hW : IsWeightMatrix W)
    (hμ : IsCentrality W μ) (κ : ℝ) (hκ : 0 < κ)
    (hP : ∀ y : Fin m → ℝ, ∑ i, μ i * y i = 0 →
      κ * ∑ i, μ i * y i ^ 2 ≤ ∑ i, ∑ j, μ i * W i j * (y i - y j) ^ 2)
    (ω : ℝ) (hω0 : 0 ≤ ω) (hω : ∀ s ∈ Set.Icc (0 : ℝ) 1, |σ s - s| ≤ ω)
    (z : ℝ → (Fin m → ℝ)) (hz : IsODESolution (meanField σ W) z)
    (hz0 : ∀ i, z 0 i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t, 0 ≤ t → ∑ i, μ i * (z t i - ∑ j, μ j * z t j) ^ 2 ≤
      Real.exp (-κ * t) + 4 * ω / κ := by
  have hrow : ∀ i, ∑ j, W i j = 1 := fun i => Matrix.sum_row_of_mem_rowStochastic hW.1 i
  have hcol : ∀ j, ∑ i, μ i * W i j = μ j := fun j => congrFun hμ.2.2 j
  have hcube := cube_inv σ hmaps W hW.1 z hz hz0
  set M : ℝ → ℝ := fun s => ∑ j, μ j * z s j with hM
  set V : ℝ → ℝ := fun s => ∑ i, μ i * (z s i - M s) ^ 2 with hV
  have hMb : ∀ s, 0 ≤ s → M s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s hs
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hμ.1 j) (hcube s hs j).1
    · calc M s ≤ ∑ j, μ j * 1 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hcube s hs j).2 (hμ.1 j)
        _ = 1 := by simp [hμ.2.1]
  have hp : ∀ s, 0 ≤ s → ∀ j, (Set.projIcc (0 : ℝ) 1 zero_le_one (z s j) : ℝ) = z s j :=
    fun s hs j => by simp [Set.projIcc_of_mem zero_le_one (hcube s hs j)]
  set Md : ℝ → ℝ := fun s => ∑ i, μ i * (σ (z s i) - z s i)
  set zd : ℝ → Fin m → ℝ := fun s i =>
    W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z s j))) i - z s i
  set Vd : ℝ → ℝ := fun s => ∑ i, μ i * ((2 : ℕ) * (z s i - M s) ^ (2 - 1) * (zd s i - Md s))
  have hVd : ∀ s, 0 ≤ s → HasDerivWithinAt V (Vd s) (Set.Ici s) s := by
    intro s hs
    exact HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
      (((coord_deriv σ W z hz s hs i).sub (mean_deriv σ W μ hcol z hz hcube s hs)).pow 2).const_mul
        (μ i)
  have hbound : ∀ s, 0 ≤ s → Vd s ≤ -κ * V s + 4 * ω := by
    intro s hs
    set y : Fin m → ℝ := fun i => z s i - M s
    set e : Fin m → ℝ := fun i =>
      W.mulVec (fun j => σ (z s j) - z s j) i - Md s
    have hzd : ∀ i, zd s i - Md s = (W.mulVec y i - y i) + e i := by
      intro i
      simp only [zd, e, y, hp s hs, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hrow i]
      ring
    have hVd' : Vd s = 2 * ∑ i, μ i * y i * (W.mulVec y i - y i) +
        2 * ∑ i, μ i * y i * e i := by
      simp only [Vd, hzd]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    have hd := dirichlet W μ hrow hcol y
    have hL : ∑ i, μ i * y i = 0 := by
      simp only [y]
      rw [Finset.sum_congr rfl fun i _ => mul_sub (μ i) _ _, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hμ.2.1, one_mul, sub_self]
    have hPy := hP y hL
    have he : ∀ i, |e i| ≤ 2 * ω := by
      intro i
      have h1 : |W.mulVec (fun j => σ (z s j) - z s j) i| ≤ ω := by
        simp only [Matrix.mulVec, dotProduct]
        calc |∑ j, W i j * (σ (z s j) - z s j)| ≤ ∑ j, |W i j * (σ (z s j) - z s j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, W i j * ω := Finset.sum_le_sum fun j _ => by
              rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hW.1)]
              exact mul_le_mul_of_nonneg_left (hω _ (hcube s hs j))
                (Matrix.nonneg_of_mem_rowStochastic hW.1)
          _ = ω := by rw [← Finset.sum_mul, hrow i, one_mul]
      have h2 : |Md s| ≤ ω := by
        calc |Md s| ≤ ∑ i, |μ i * (σ (z s i) - z s i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, μ i * ω := Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_of_nonneg (hμ.1 i)]
              exact mul_le_mul_of_nonneg_left (hω _ (hcube s hs i)) (hμ.1 i)
          _ = ω := by rw [← Finset.sum_mul, hμ.2.1, one_mul]
      calc |e i| ≤ |W.mulVec (fun j => σ (z s j) - z s j) i| + |Md s| := abs_sub _ _
        _ ≤ 2 * ω := by linarith
    have hy : ∀ i, |y i| ≤ 1 := by
      intro i
      have h1 := hcube s hs i
      have h2 := hMb s hs
      rw [abs_le]; constructor <;> simp only [y] <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hcross : ∑ i, μ i * y i * e i ≤ 2 * ω := by
      calc ∑ i, μ i * y i * e i ≤ ∑ i, μ i * (2 * ω) := Finset.sum_le_sum fun i _ => by
            have h1 : y i * e i ≤ 2 * ω := by
              calc y i * e i ≤ |y i * e i| := le_abs_self _
                _ = |y i| * |e i| := abs_mul _ _
                _ ≤ 1 * (2 * ω) := mul_le_mul (hy i) (he i) (abs_nonneg _) zero_le_one
                _ = 2 * ω := one_mul _
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (hμ.1 i)
        _ = 2 * ω := by rw [← Finset.sum_mul, hμ.2.1, one_mul]
    rw [hVd']
    have : V s = ∑ i, μ i * y i ^ 2 := rfl
    rw [this]
    linarith
  have hVc : ContinuousOn V (Set.Ici 0) := by
    have hzc : ∀ i, ContinuousOn (fun s => z s i) (Set.Ici 0) := fun i =>
      (continuous_apply i).comp_continuousOn hz.1
    have hMc : ContinuousOn M (Set.Ici 0) :=
      continuousOn_finsetSum _ fun j _ => (hzc j).const_smul (μ j)
    exact continuousOn_finsetSum _ fun i _ => ((hzc i).sub hMc).pow 2 |>.const_smul (μ i)
  have hV0 : V 0 ≤ 1 := by
    calc V 0 ≤ ∑ i, μ i * 1 := Finset.sum_le_sum fun i _ => by
          apply mul_le_mul_of_nonneg_left _ (hμ.1 i)
          have h1 := hcube 0 le_rfl i
          have h2 := hMb 0 le_rfl
          nlinarith [h1.1, h1.2, h2.1, h2.2]
      _ = 1 := by simp [hμ.2.1]
  intro t ht
  have hg := le_gronwallBound_of_liminf_deriv_right_le (f := V) (f' := Vd) (δ := V 0)
    (K := -κ) (ε := 4 * ω) (a := 0) (b := t) (hVc.mono Set.Icc_subset_Ici_self)
    (fun s hs r hr => (hVd s hs.1).liminf_right_slope_le hr) le_rfl
    (fun s hs => hbound s hs.1) t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 (by linarith : -κ ≠ 0), sub_zero] at hg
  have he : Real.exp (-κ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he0 : 0 < Real.exp (-κ * t) := Real.exp_pos _
  have : 4 * ω / -κ * (Real.exp (-κ * t) - 1) ≤ 4 * ω / κ := by
    rw [div_neg, neg_mul, ← mul_neg, neg_sub]
    have h4 : 0 ≤ 4 * ω / κ := by positivity
    nlinarith
  show V t ≤ _
  nlinarith


lemma up_core {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ) (hW : IsWeightMatrix W)
    (hμ : IsCentrality W μ) (η : ℝ) (hη : 0 < η) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ p : ℝ, 0 < p → p < 1 → ∀ σ : ℝ → ℝ,
      Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1) → ContinuousOn σ (Set.Icc 0 1) →
      (∀ x ∈ Set.Ioo p 1, x < σ x) → (∀ s ∈ Set.Icc (0 : ℝ) 1, |σ s - s| ≤ ω) →
      ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) → p + η < ∑ i, μ i * x1 i →
      ∀ z : ℝ → (Fin m → ℝ), IsODESolution (meanField σ W) z → z 0 = x1 →
        Tendsto z atTop (𝓝 1) := by
  have hpos := mu_pos W μ hW hμ
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hμ.2.1; rw [h, Finset.sum_empty] at this; norm_num at this
  set μs := Finset.univ.inf' hne μ with hμs
  have hμs0 : 0 < μs := by rw [Finset.lt_inf'_iff]; exact fun i _ => hpos i
  have hμsle : ∀ i, μs ≤ μ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨κ, hκ, hP⟩ := poincare W μ hW hμ
  have hcol : ∀ j, ∑ i, μ i * W i j = μ j := fun j => congrFun hμ.2.2 j
  set ρ := η / 8 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hev : ∀ᶠ t in atTop, Real.exp (-κ * t) < μs * ρ ^ 2 / 2 := by
    have h1 : Tendsto (fun t => Real.exp (-κ * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -κ < 0))
    exact h1.eventually (gt_mem_nhds (by positivity))
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
  set T := max T0 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hexpT : Real.exp (-κ * T) < μs * ρ ^ 2 / 2 := hT0 T (le_max_left _ _)
  set ω := min (κ * μs * ρ ^ 2 / 8) (η / (4 * T)) with hωdef
  have hω0 : 0 < ω := lt_min (by positivity) (by positivity)
  refine ⟨ω, hω0, ?_⟩
  intro p hp0 hp1 σ hmaps hcont hgt hω x1 hx1 hηx z hz hz0
  have hup := sigma_up p hp0 hp1 σ hcont hgt
  have hcube := cube_inv σ hmaps W hW.1 z hz (by rw [hz0]; exact hx1)
  set M : ℝ → ℝ := fun s => ∑ j, μ j * z s j with hM
  set Md : ℝ → ℝ := fun s => ∑ i, μ i * (σ (z s i) - z s i)
  have hMd : ∀ s, 0 ≤ s → HasDerivWithinAt M (Md s) (Set.Ici s) s :=
    fun s hs => mean_deriv σ W μ hcol z hz hcube s hs
  have hzc : ∀ i, ContinuousOn (fun s => z s i) (Set.Ici 0) := fun i =>
    (continuous_apply i).comp_continuousOn hz.1
  have hMc : ContinuousOn M (Set.Ici 0) :=
    continuousOn_finsetSum _ fun j _ => (hzc j).const_smul (μ j)
  have hMb : ∀ s, 0 ≤ s → M s ≤ 1 := by
    intro s hs
    calc M s ≤ ∑ j, μ j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hcube s hs j).2 (hμ.1 j)
      _ = 1 := by simp [hμ.2.1]
  have hMdb : ∀ s, 0 ≤ s → |Md s| ≤ ω := by
    intro s hs
    calc |Md s| ≤ ∑ i, |μ i * (σ (z s i) - z s i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, μ i * ω := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hμ.1 i)]
          exact mul_le_mul_of_nonneg_left (hω _ (hcube s hs i)) (hμ.1 i)
      _ = ω := by rw [← Finset.sum_mul, hμ.2.1, one_mul]
  -- (a) the mean barely moves up to time T
  have hMT : p + 3 * η / 4 < M T := by
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment (f := M) (f' := Md) (C := ω)
      (hMc.mono Set.Icc_subset_Ici_self) (fun s hs => hMd s hs.1)
      (fun s hs => by rw [Real.norm_eq_abs]; exact hMdb s hs.1) T ⟨hTpos.le, le_rfl⟩
    rw [Real.norm_eq_abs, sub_zero] at h
    have hM0 : M 0 = ∑ i, μ i * x1 i := by simp [M, hz0]
    have hωT : ω * T ≤ η / 4 := by
      have : ω ≤ η / (4 * T) := min_le_right _ _
      calc ω * T ≤ η / (4 * T) * T := mul_le_mul_of_nonneg_right this hTpos.le
        _ = η / 4 := by field_simp
    have := (abs_le.1 h).1
    linarith
  -- (b) after time T all coordinates are within ρ of the mean
  have hclose : ∀ s, T ≤ s → ∀ i, |z s i - M s| ≤ ρ := by
    intro s hs i
    have hs0 : 0 ≤ s := by linarith
    have hV := V_bound σ hmaps W μ hW hμ κ hκ hP ω hω0.le hω z hz (by rw [hz0]; exact hx1) s hs0
    have he : Real.exp (-κ * s) ≤ Real.exp (-κ * T) := Real.exp_le_exp.2 (by nlinarith)
    have hω' : 4 * ω / κ ≤ μs * ρ ^ 2 / 2 := by
      have : ω ≤ κ * μs * ρ ^ 2 / 8 := min_le_left _ _
      rw [div_le_iff₀ hκ]; nlinarith
    have hsum : μ i * (z s i - M s) ^ 2 ≤ μs * ρ ^ 2 := by
      have h1 := Finset.single_le_sum (f := fun j => μ j * (z s j - M s) ^ 2)
        (fun j _ => mul_nonneg (hμ.1 j) (sq_nonneg _)) (Finset.mem_univ i)
      linarith
    have hsq : (z s i - M s) ^ 2 ≤ ρ ^ 2 := by
      have h2 : μs * (z s i - M s) ^ 2 ≤ μ i * (z s i - M s) ^ 2 :=
        mul_le_mul_of_nonneg_right (hμsle i) (sq_nonneg _)
      have := le_trans h2 hsum
      exact le_of_mul_le_mul_left this hμs0
    rw [abs_le]; constructor <;> nlinarith
  -- (c) monotonicity of the mean after time T
  have hMd_nn : ∀ s, T ≤ s → p + 2 * ρ ≤ M s → 0 ≤ Md s := by
    intro s hs hMs
    refine Finset.sum_nonneg fun i _ => mul_nonneg (hμ.1 i) ?_
    have h1 := hclose s hs i
    have h2 := hcube s (by linarith) i
    have : z s i ∈ Set.Ioc p 1 := ⟨by rw [abs_le] at h1; linarith [h1.1], h2.2⟩
    linarith [hup _ this]
  have hmono : ∀ T', T ≤ T' → p + 2 * ρ < M T' → ∀ t, T' ≤ t → M T' ≤ M t := by
    intro T' hT' hMT' t ht
    set θ0 := (M T' - p - 2 * ρ) / (1 + (t - T'))
    have hθ0 : 0 < θ0 := div_pos (by linarith) (by linarith)
    have key : ∀ θ, 0 < θ → θ ≤ θ0 → M T' - θ * (1 + (t - T')) ≤ M t := by
      intro θ hθ hθle
      have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => -M s)
        (f' := fun s => -Md s) (a := T') (b := t)
        ((hMc.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 (by linarith)))).neg)
        (fun s hs => (hMd s (by linarith [hs.1])).neg)
        (B := fun s => -M T' + θ * (1 + (s - T'))) (B' := fun _ => θ)
        (by simp only [sub_self, add_zero, mul_one]; linarith) (by fun_prop)
        (fun s _ => by
          have := ((hasDerivAt_id' s).sub_const T').const_add 1 |>.const_mul θ |>.const_add (-M T')
          exact this.hasDerivWithinAt.congr_deriv (by ring))
        (fun s hs heq => by
          have hMs : M s = M T' - θ * (1 + (s - T')) := by linarith
          have h1 : θ * (1 + (s - T')) ≤ θ0 * (1 + (t - T')) :=
            mul_le_mul hθle (by linarith [hs.2]) (by linarith [hs.1]) hθ0.le
          have hden : (1 + (t - T')) ≠ 0 := by linarith
          have h2 : θ0 * (1 + (t - T')) = M T' - p - 2 * ρ := by
            simp only [θ0]; field_simp
          have := hMd_nn s (by linarith [hs.1]) (by linarith)
          linarith) (x := t) ⟨ht, le_rfl⟩
      linarith
    by_contra hcon
    push Not at hcon
    set gap := M T' - M t
    have hgap : 0 < gap := by linarith
    set θ := min θ0 (gap / (2 * (1 + (t - T'))))
    have hθ : 0 < θ := lt_min hθ0 (div_pos hgap (by linarith))
    have h1 := key θ hθ (min_le_left _ _)
    have h2 : θ * (1 + (t - T')) ≤ gap / 2 := by
      have : θ ≤ gap / (2 * (1 + (t - T'))) := min_le_right _ _
      calc θ * (1 + (t - T')) ≤ gap / (2 * (1 + (t - T'))) * (1 + (t - T')) :=
            mul_le_mul_of_nonneg_right this (by linarith)
        _ = gap / 2 := by
            have hden : (1 + (t - T')) ≠ 0 := by linarith
            field_simp
    linarith
  have hMge : ∀ t, T ≤ t → M T ≤ M t := hmono T le_rfl (by linarith) 
  -- (d) the mean tends to 1
  have hMlim : Tendsto M atTop (𝓝 1) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · -- eventually M > a
      by_contra hcon
      rw [not_eventually] at hcon
      -- since M is monotone after T, M t ≤ a for all t ≥ T
      have hall : ∀ t, T ≤ t → M t ≤ a := by
        intro t ht
        by_contra h
        push Not at h
        obtain ⟨t', ht', hle⟩ := (hcon.and_eventually (eventually_ge_atTop t)).exists
        have := hmono t ht (by linarith [hMge t ht]) t' hle
        simp only [not_lt] at ht'
        linarith
      set lo := M T - ρ
      have hlo : p < lo := by linarith
      have hla : lo ≤ a := by linarith [hall T le_rfl]
      have ha1 : a < 1 := ha
      obtain ⟨g0, hg0, hgmin⟩ : ∃ g0 : ℝ, 0 < g0 ∧ ∀ s ∈ Set.Icc lo a, g0 ≤ σ s - s := by
        have hsub : Set.Icc lo a ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc (by linarith) ha1.le
        obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn
          (Set.nonempty_Icc.2 hla) ((hcont.mono hsub).sub continuousOn_id)
        refine ⟨σ s0 - s0, by linarith [hgt s0 ⟨by linarith [hs0.1], by linarith [hs0.2]⟩],
          fun s hs => hmin hs⟩
      have hMd_lb : ∀ s, T ≤ s → μs * g0 ≤ Md s := by
        intro s hs
        obtain ⟨i, hi⟩ : ∃ i, z s i ≤ M s := by
          by_contra h
          push Not at h
          have : M s < M s := by
            calc M s = ∑ j, μ j * M s := by rw [← Finset.sum_mul, hμ.2.1, one_mul]
              _ < ∑ j, μ j * z s j := Finset.sum_lt_sum_of_nonempty hne fun j _ =>
                  mul_lt_mul_of_pos_left (h j) (hpos j)
          exact lt_irrefl _ this
        have hzi : z s i ∈ Set.Icc lo a := by
          have h1 := hclose s hs i
          rw [abs_le] at h1
          exact ⟨by linarith [hMge s hs, h1.1], by linarith [hall s hs]⟩
        have hnn := hMd_nn s hs (by linarith [hMge s hs])
        have hterm : ∀ j, 0 ≤ μ j * (σ (z s j) - z s j) := by
          intro j
          have h1 := hclose s hs j
          have h2 := hcube s (by linarith) j
          have : z s j ∈ Set.Ioc p 1 := ⟨by rw [abs_le] at h1; linarith [h1.1, hMge s hs], h2.2⟩
          exact mul_nonneg (hμ.1 j) (by linarith [hup _ this])
        calc μs * g0 ≤ μ i * (σ (z s i) - z s i) :=
              mul_le_mul (hμsle i) (hgmin _ hzi) hg0.le (hμ.1 i)
          _ ≤ Md s := Finset.single_le_sum (f := fun j => μ j * (σ (z s j) - z s j))
              (fun j _ => hterm j) (Finset.mem_univ i)
      set t2 := T + 2 / (μs * g0)
      have hlin := image_le_of_deriv_right_le_deriv_boundary (f := fun s => -M s)
        (f' := fun s => -Md s) (a := T) (b := t2)
        ((hMc.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 hTpos.le))).neg)
        (fun s hs => (hMd s (by linarith [hs.1])).neg)
        (B := fun s => -(M T + μs * g0 * (s - T))) (B' := fun _ => -(μs * g0))
        (by simp only [sub_self, mul_zero, add_zero]; exact le_rfl) (by fun_prop)
        (fun s _ => by
          have := (((hasDerivAt_id' s).sub_const T).const_mul (μs * g0)).const_add (M T) |>.neg
          exact this.hasDerivWithinAt.congr_deriv (by ring))
        (fun s hs => by linarith [hMd_lb s hs.1]) (x := t2)
        ⟨by have : 0 < 2 / (μs * g0) := by positivity
            linarith, le_rfl⟩
      have : μs * g0 * (t2 - T) = 2 := by simp only [t2]; field_simp; ring
      have := hMb t2 (by have : 0 < 2 / (μs * g0) := by positivity
                         linarith)
      linarith
    · filter_upwards [eventually_ge_atTop 0] with t ht using lt_of_le_of_lt (hMb t ht) ha
  rw [tendsto_pi_nhds]
  intro i
  simp only [Pi.one_apply]
  have h1 : Tendsto (fun t => (1 - M t) / μ i) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hMlim).div_const (μ i)
    simpa using this
  have h2 : Tendsto (fun t => 1 - z t i) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht
      linarith [(hcube t ht i).2]
    · filter_upwards [eventually_ge_atTop 0] with t ht
      rw [le_div_iff₀ (hpos i)]
      have hsplit : 1 - M t = ∑ j, μ j * (1 - z t j) := by
        rw [Finset.sum_congr rfl fun j _ => mul_sub (μ j) 1 _, Finset.sum_sub_distrib]
        simp [M, hμ.2.1]
      rw [hsplit, mul_comm]
      exact Finset.single_le_sum (f := fun j => μ j * (1 - z t j))
        (fun j _ => mul_nonneg (hμ.1 j) (by linarith [(hcube t ht j).2])) (Finset.mem_univ i)
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  simpa using this


lemma projIcc_one_sub (x : ℝ) :
    (Set.projIcc (0 : ℝ) 1 zero_le_one (1 - x) : ℝ) =
      1 - (Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ) := by
  simp only [Set.coe_projIcc]
  rcases le_total x 0 with h | h
  · rw [max_eq_left (show min 1 x ≤ 0 from (min_le_right _ _).trans h)]
    rw [min_eq_left (by linarith : (1 : ℝ) ≤ 1 - x), max_eq_right zero_le_one]
    ring
  · rcases le_total x 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h, min_eq_right (by linarith : 1 - x ≤ 1),
        max_eq_right (by linarith : (0 : ℝ) ≤ 1 - x)]
    · rw [min_eq_left h', max_eq_right zero_le_one,
        max_eq_left (show min 1 (1 - x) ≤ 0 from (min_le_right _ _).trans (by linarith))]
      ring

lemma reflect_sol {m : ℕ} (σ : ℝ → ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (z : ℝ → (Fin m → ℝ))
    (hz : IsODESolution (meanField σ W) z) :
    IsODESolution (meanField (fun s => 1 - σ (1 - s)) W) (fun t => 1 - z t) := by
  refine ⟨continuousOn_const.sub hz.1, fun t ht => ?_⟩
  have h := (hz.2 t ht).const_sub (1 : Fin m → ℝ)
  refine h.congr_deriv ?_
  funext i
  simp only [meanField, Pi.neg_apply, Pi.sub_apply, Pi.one_apply, Matrix.mulVec, dotProduct,
    projIcc_one_sub, sub_sub_cancel, mul_sub, mul_one, Finset.sum_sub_distrib,
    Matrix.sum_row_of_mem_rowStochastic hW]
  ring

end NL4

open NL4 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ → ℝ)
    (hσ : IsExtremizationFamily p σ) {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ η : ℝ, 0 < η → ∃ δ0 ∈ Set.Ioc (0 : ℝ) 1, ∀ δ ∈ Set.Ioc (0 : ℝ) δ0,
      ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ z : ℝ → (Fin m → ℝ), IsODESolution (meanField (σ δ) W) z → z 0 = x1 →
        (p + η < ∑ i, μ i * x1 i → Tendsto z atTop (𝓝 1)) ∧
        (∑ i, μ i * x1 i < p - η → Tendsto z atTop (𝓝 0)) := by
  intro η hη
  obtain ⟨ω, hω, H⟩ := up_core W μ hW hμ η hη
  have hu := Metric.tendstoUniformlyOn_iff.1 hσ.2 ω hω
  obtain ⟨δ1, hδ1, hδ1P⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hu
  refine ⟨min (δ1 / 2) 1, ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩, ?_⟩
  intro δ hδ x1 hx1 z hz hz0
  have hδI : δ ∈ Set.Ioc (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩
  have hδ1' : δ ∈ Set.Ioo (0 : ℝ) δ1 := ⟨hδ.1, by linarith [hδ.2.trans (min_le_left _ _)]⟩
  obtain ⟨hmaps, ⟨K, hlip⟩, hgt, hlt⟩ := hσ.1 δ hδI
  have hcont : ContinuousOn (σ δ) (Set.Icc 0 1) := hlip.continuousOn
  have hclose : ∀ s ∈ Set.Icc (0 : ℝ) 1, |σ δ s - s| ≤ ω := by
    intro s hs
    have := hδ1P hδ1' s hs
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  constructor
  · intro h
    exact H p hp0 hp1 (σ δ) hmaps hcont hgt hclose x1 hx1 h z hz hz0
  · intro h
    set σ' : ℝ → ℝ := fun s => 1 - σ δ (1 - s)
    have hmaps' : Set.MapsTo σ' (Set.Icc 0 1) (Set.Icc 0 1) := by
      intro s hs
      have := hmaps (show 1 - s ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      exact ⟨by simp only [σ']; linarith [this.2], by simp only [σ']; linarith [this.1]⟩
    have hcont' : ContinuousOn σ' (Set.Icc 0 1) := by
      apply continuousOn_const.sub
      exact hcont.comp (continuousOn_const.sub continuousOn_id)
        (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    have hgt' : ∀ x ∈ Set.Ioo (1 - p) 1, x < σ' x := by
      intro x hx
      have := hlt (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      simp only [σ']; linarith
    have hclose' : ∀ s ∈ Set.Icc (0 : ℝ) 1, |σ' s - s| ≤ ω := by
      intro s hs
      have := hclose (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simp only [σ']
      rw [show 1 - σ δ (1 - s) - s = -(σ δ (1 - s) - (1 - s)) by ring, abs_neg]
      exact this
    have hw := reflect_sol (σ δ) W hW.1 z hz
    have hx1' : ∀ i, (1 - x1) i ∈ Set.Icc (0 : ℝ) 1 := fun i =>
      ⟨by simp only [Pi.sub_apply, Pi.one_apply]; linarith [(hx1 i).2],
        by simp only [Pi.sub_apply, Pi.one_apply]; linarith [(hx1 i).1]⟩
    have hsum : (1 - p) + η < ∑ i, μ i * (1 - x1) i := by
      have : ∑ i, μ i * (1 - x1) i = 1 - ∑ i, μ i * x1 i := by
        simp only [Pi.sub_apply, Pi.one_apply, mul_sub, mul_one, Finset.sum_sub_distrib, hμ.2.1]
      rw [this]; linarith
    have hlim := H (1 - p) (by linarith) (by linarith) σ' hmaps' hcont' hgt' hclose' (1 - x1)
      hx1' hsum (fun t => 1 - z t) hw (by simp [hz0])
    have := (tendsto_const_nhds (x := (1 : Fin m → ℝ))).sub hlim
    simpa using this
