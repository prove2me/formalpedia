-- Prove2me | solution 1 for NonsmoothLojasiewicz.Traj.thm4_7_convergence_rates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T01:05:16.143706+00:00
-- url     : https://prove2.me/submissions/5f6ec9b0-7d2a-43c5-aa1e-880f1caaa05c

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory
import Definitions.Def_NonsmoothLojasiewicz_Traj_Subanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Traj_thm4_5_finite_length
import Theorems.Thm_NonsmoothLojasiewicz_Traj_tail_length_bound

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace Thm47Aux

theorem anti_of_D {ψ : ℝ → ℝ} {s₀ K α : ℝ} (hK : 0 < K)
    (hnn : ∀ t, s₀ ≤ t → 0 ≤ ψ t)
    (hD : ∀ s t, s₀ ≤ s → s ≤ t → K * (t - s) * ψ t ^ α ≤ ψ s - ψ t) :
    ∀ s t, s₀ ≤ s → s ≤ t → ψ t ≤ ψ s := by
  intro s t hs hst
  have h := hD s t hs hst
  have h0 : 0 ≤ K * (t - s) * ψ t ^ α :=
    mul_nonneg (mul_nonneg hK.le (sub_nonneg.2 hst)) (Real.rpow_nonneg (hnn t (hs.trans hst)) _)
  linarith

/-- exponential decay from `K (t - s) ψ t ≤ ψ s - ψ t`. -/
theorem decay_one {ψ : ℝ → ℝ} {s₀ K : ℝ} (hK : 0 < K)
    (hnn : ∀ t, s₀ ≤ t → 0 ≤ ψ t)
    (hD : ∀ s t, s₀ ≤ s → s ≤ t → K * (t - s) * ψ t ^ (1 : ℝ) ≤ ψ s - ψ t) :
    ∀ t, s₀ ≤ t → ψ t ≤ 2 * ψ s₀ * Real.exp (-(K * Real.log 2) * (t - s₀)) := by
  have hmono := anti_of_D hK hnn hD
  have hstep : ∀ j : ℕ, ψ (s₀ + j / K) ≤ ψ s₀ / 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hj0 : (0 : ℝ) ≤ j / K := by positivity
      have hs : s₀ ≤ s₀ + j / K := by linarith
      have hst : s₀ + j / K ≤ s₀ + ((j + 1 : ℕ) : ℝ) / K := by
        have : (j : ℝ) / K ≤ ((j + 1 : ℕ) : ℝ) / K := by
          apply div_le_div_of_nonneg_right _ hK.le
          push_cast; linarith
        linarith
      have h := hD _ _ hs hst
      have h1 : K * ((s₀ + ((j + 1 : ℕ) : ℝ) / K) - (s₀ + j / K)) = 1 := by
        push_cast; field_simp; ring
      rw [h1, one_mul, Real.rpow_one] at h
      have h2 : ψ (s₀ + ((j + 1 : ℕ) : ℝ) / K) ≤ ψ (s₀ + j / K) / 2 := by linarith
      calc ψ (s₀ + ((j + 1 : ℕ) : ℝ) / K) ≤ ψ (s₀ + j / K) / 2 := h2
        _ ≤ (ψ s₀ / 2 ^ j) / 2 := by linarith
        _ = ψ s₀ / 2 ^ (j + 1) := by rw [pow_succ]; ring
  intro t ht
  set j := ⌊K * (t - s₀)⌋₊ with hjdef
  have hKT : 0 ≤ K * (t - s₀) := mul_nonneg hK.le (sub_nonneg.2 ht)
  have hj1 : (j : ℝ) ≤ K * (t - s₀) := Nat.floor_le hKT
  have hj2 : K * (t - s₀) < j + 1 := Nat.lt_floor_add_one _
  have hle : s₀ + j / K ≤ t := by
    have : (j : ℝ) / K ≤ t - s₀ := by
      rw [div_le_iff₀ hK]; linarith
    linarith
  have h1 := hmono _ _ (by have : (0 : ℝ) ≤ j / K := by positivity
                           linarith) hle
  have h2 := hstep j
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h3 : (1 : ℝ) / 2 ^ j ≤ 2 * Real.exp (-(K * Real.log 2) * (t - s₀)) := by
    have e1 : (2 : ℝ) ^ j = Real.exp (j * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos]; ring_nf
    have e2 : (2 : ℝ) * Real.exp (-(K * Real.log 2) * (t - s₀)) =
        Real.exp (Real.log 2 + -(K * Real.log 2) * (t - s₀)) := by
      rw [Real.exp_add, Real.exp_log two_pos]
    rw [e1, e2, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    nlinarith
  have hψ0 : 0 ≤ ψ s₀ := hnn s₀ le_rfl
  calc ψ t ≤ ψ s₀ / 2 ^ j := h1.trans h2
    _ = ψ s₀ * (1 / 2 ^ j) := by ring
    _ ≤ ψ s₀ * (2 * Real.exp (-(K * Real.log 2) * (t - s₀))) :=
        mul_le_mul_of_nonneg_left h3 hψ0
    _ = 2 * ψ s₀ * Real.exp (-(K * Real.log 2) * (t - s₀)) := by ring

/-- polynomial decay for `α > 1`. -/
theorem decay_pow {ψ : ℝ → ℝ} {s₀ K α γ : ℝ} (hK : 0 < K) (hα : 1 < α)
    (hγ : γ * (α - 1) = 1)
    (hnn : ∀ t, s₀ ≤ t → 0 ≤ ψ t)
    (hD : ∀ s t, s₀ ≤ s → s ≤ t → K * (t - s) * ψ t ^ α ≤ ψ s - ψ t) :
    ∃ A, 0 < A ∧ ∀ t, s₀ < t → ψ t ≤ A * (t - s₀) ^ (-γ) := by
  have hmono := anti_of_D hK hnn hD
  have hγ0 : 0 < γ := by
    by_contra h
    push Not at h
    have : γ * (α - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  set B : ℝ := (2 : ℝ) ^ (1 + γ) / K with hB
  have hBpos : 0 < B := by positivity
  set A : ℝ := max (ψ s₀ + 1) (B ^ γ) with hA
  have hApos : 0 < A := lt_of_lt_of_le (by linarith [hnn s₀ le_rfl]) (le_max_left _ _)
  have hAB : B ≤ A ^ (α - 1) := by
    have : B = (B ^ γ) ^ (α - 1) := by
      rw [← Real.rpow_mul hBpos.le, hγ, Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by linarith)
  have hbase : ∀ t, s₀ < t → t ≤ s₀ + 1 → ψ t ≤ A * (t - s₀) ^ (-γ) := by
    intro t h1 h2
    have hd : 0 < t - s₀ := by linarith
    have : 1 ≤ (t - s₀) ^ (-γ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd (by linarith) (by linarith)
    calc ψ t ≤ ψ s₀ := hmono _ _ le_rfl h1.le
      _ ≤ A := by linarith [le_max_left (ψ s₀ + 1) (B ^ γ)]
      _ = A * 1 := (mul_one _).symm
      _ ≤ A * (t - s₀) ^ (-γ) := mul_le_mul_of_nonneg_left this hApos.le
  have hind : ∀ k : ℕ, ∀ t, s₀ < t → t ≤ s₀ + 2 ^ k → ψ t ≤ A * (t - s₀) ^ (-γ) := by
    intro k
    induction k with
    | zero => intro t h1 h2; exact hbase t h1 (by simpa using h2)
    | succ k ih =>
      intro t h1 h2
      by_cases hc : t ≤ s₀ + 1
      · exact hbase t h1 hc
      push Not at hc
      set d := t - s₀ with hd
      have hdpos : 0 < d := by linarith
      have hs1 : s₀ < s₀ + d / 2 := by linarith
      have hs2 : s₀ + d / 2 ≤ s₀ + 2 ^ k := by
        have : d ≤ 2 ^ (k + 1) := by linarith
        rw [pow_succ] at this; linarith
      have hih := ih _ hs1 hs2
      have hD' := hD (s₀ + d / 2) t hs1.le (by linarith)
      have e1 : t - (s₀ + d / 2) = d / 2 := by rw [hd]; ring
      rw [e1] at hD'
      have e2 : s₀ + d / 2 - s₀ = d / 2 := by ring
      rw [e2] at hih
      have hψt := hnn t h1.le
      -- set w = d ^ (-γ)
      set w := d ^ (-γ) with hw
      have hwpos : 0 < w := Real.rpow_pos_of_pos hdpos _
      have ew : (d / 2) ^ (-γ) = 2 ^ γ * w := by
        rw [Real.div_rpow hdpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), hw]
        field_simp
      have hψs : ψ (s₀ + d / 2) ≤ A * (2 ^ γ * w) := by rw [← ew]; exact hih
      -- bound: ψ t ^ α ≤ ψ s * 2 / (K d)
      have hb1 : K * (d / 2) * ψ t ^ α ≤ A * (2 ^ γ * w) := by
        have := hnn (s₀ + d / 2) hs1.le
        linarith
      by_contra hcon
      push Not at hcon
      have hAw : 0 < A * w := mul_pos hApos hwpos
      have hpow : (A * w) ^ α < ψ t ^ α :=
        Real.rpow_lt_rpow hAw.le hcon (by linarith)
      have ewα : w ^ α = w / d := by
        rw [hw, ← Real.rpow_mul hdpos.le]
        have : -γ * α = -γ + (-1) := by nlinarith
        rw [this, Real.rpow_add hdpos, Real.rpow_neg_one]
        field_simp
      have eAα : A ^ α = A * A ^ (α - 1) := by
        rw [← Real.rpow_one_add' hApos.le (by linarith)]
        congr 1; ring
      rw [Real.mul_rpow hApos.le hwpos.le, ewα, eAα] at hpow
      -- (A * A^(α-1)) * (w/d) ≥ A * B * (w/d) = A * 2^(1+γ)/K * w / d
      have hB2 : A * B * (w / d) ≤ A * A ^ (α - 1) * (w / d) := by
        have : 0 ≤ w / d := by positivity
        have h3 : A * B ≤ A * A ^ (α - 1) := mul_le_mul_of_nonneg_left hAB hApos.le
        exact mul_le_mul_of_nonneg_right h3 this
      have e3 : A * B * (w / d) * (K * (d / 2)) = A * (2 ^ γ * w) := by
        rw [hB, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
        field_simp
      have hfin : A * (2 ^ γ * w) < K * (d / 2) * ψ t ^ α := by
        have hKd : 0 < K * (d / 2) := by positivity
        calc A * (2 ^ γ * w) = A * B * (w / d) * (K * (d / 2)) := e3.symm
          _ ≤ A * A ^ (α - 1) * (w / d) * (K * (d / 2)) :=
              mul_le_mul_of_nonneg_right hB2 hKd.le
          _ < ψ t ^ α * (K * (d / 2)) := mul_lt_mul_of_pos_right hpow hKd
          _ = K * (d / 2) * ψ t ^ α := by ring
      linarith
  refine ⟨A, hApos, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (t - s₀) (by norm_num : (1 : ℝ) < 2)
  exact hind k t ht (by linarith)


/-- finite-time extinction for `0 ≤ α < 1`. -/
theorem decay_finite {ψ : ℝ → ℝ} {s₀ K α : ℝ} (hK : 0 < K) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hnn : ∀ t, s₀ ≤ t → 0 ≤ ψ t)
    (hD : ∀ s t, s₀ ≤ s → s ≤ t → K * (t - s) * ψ t ^ α ≤ ψ s - ψ t) :
    ∃ t₁, s₀ ≤ t₁ ∧ ∀ t, t₁ ≤ t → ψ t = 0 := by
  have hmono := anti_of_D hK hnn hD
  set ψ₀ := ψ s₀ with hψ₀
  rcases (hnn s₀ le_rfl).eq_or_lt with h0 | hpos
  · refine ⟨s₀, le_rfl, fun t ht => le_antisymm ?_ (hnn t ht)⟩
    have := hmono s₀ t le_rfl ht
    linarith
  set q : ℝ := (2 : ℝ) ^ (1 - α) with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) (by linarith)
  set r : ℝ := q⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hq1
  set c₀ : ℝ := 2 ^ α * ψ₀ ^ (1 - α) / K * 2 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set S : ℝ := c₀ / (1 - r) with hS
  have hSpos : 0 < S := div_pos hc₀pos (by linarith)
  set τ : ℕ → ℝ := fun j => s₀ + S * (1 - r ^ j) with hτ
  have hτge : ∀ j, s₀ ≤ τ j := by
    intro j
    have : r ^ j ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have : 0 ≤ S * (1 - r ^ j) := mul_nonneg hSpos.le (by linarith)
    simp only [hτ]; linarith
  have hτle : ∀ j, τ j ≤ s₀ + S := by
    intro j
    have : 0 ≤ S * r ^ j := mul_nonneg hSpos.le (pow_nonneg hr0.le _)
    simp only [hτ]; nlinarith
  have hpj : ∀ j : ℕ, (ψ₀ / 2 ^ j) ^ (1 - α) = ψ₀ ^ (1 - α) * r ^ j := by
    intro j
    rw [Real.div_rpow hpos.le (by positivity), hr, inv_pow]
    have : ((2 : ℝ) ^ j) ^ (1 - α) = q ^ j := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [this, div_eq_mul_inv]
  have hclaim : ∀ j : ℕ, ψ (τ j) ≤ ψ₀ / 2 ^ j := by
    intro j
    induction j with
    | zero => simp [hτ, hψ₀]
    | succ j ih =>
      set p := ψ₀ / 2 ^ j with hp
      have hppos : 0 < p := by positivity
      have h1r : (1 - r) ≠ 0 := ne_of_gt (sub_pos.2 hr1)
      have hstep : τ (j + 1) - τ j = c₀ * r ^ j := by
        simp only [hτ, hS, pow_succ]
        field_simp
        ring
      have hle : τ j ≤ τ (j + 1) := by
        have : 0 < c₀ * r ^ j := by positivity
        linarith
      by_contra hcon
      push Not at hcon
      have hD' := hD (τ j) (τ (j + 1)) (hτge j) hle
      rw [hstep] at hD'
      have hlt : p / 2 < ψ (τ (j + 1)) := by
        rw [pow_succ, ← div_div] at hcon; exact hcon
      have hpow : (p / 2) ^ α ≤ ψ (τ (j + 1)) ^ α :=
        Real.rpow_le_rpow (by positivity) hlt.le hα0
      -- K * c₀ r^j * (p/2)^α = 2 p
      have hkey : K * (c₀ * r ^ j) * (p / 2) ^ α = 2 * p := by
        have e1 : (p / 2) ^ α = p ^ α / 2 ^ α := Real.div_rpow hppos.le (by norm_num) _
        have e2 : ψ₀ ^ (1 - α) * r ^ j = p ^ (1 - α) := (hpj j).symm
        have e3 : p ^ (1 - α) * p ^ α = p := by
          rw [← Real.rpow_add hppos]; simp
        have h2a : (0 : ℝ) < 2 ^ α := by positivity
        calc K * (c₀ * r ^ j) * (p / 2) ^ α
            = 2 * (ψ₀ ^ (1 - α) * r ^ j) * p ^ α * (2 ^ α / 2 ^ α) * (K / K) := by
              rw [e1, hc₀]; field_simp
          _ = 2 * p := by rw [e2, div_self h2a.ne', div_self hK.ne', mul_assoc 2, e3]; ring
      have hKc : 0 ≤ K * (c₀ * r ^ j) := by positivity
      have h5 : 2 * p ≤ K * (c₀ * r ^ j) * ψ (τ (j + 1)) ^ α := by
        rw [← hkey]; exact mul_le_mul_of_nonneg_left hpow hKc
      have h6 : ψ (τ j) - ψ (τ (j + 1)) < p := by linarith
      linarith
  refine ⟨s₀ + S, by linarith, fun t ht => ?_⟩
  have ht0 : s₀ ≤ t := by linarith
  refine le_antisymm ?_ (hnn t ht0)
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hcon hpos) (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : ψ t ≤ ψ₀ / 2 ^ j := (hmono _ _ (hτge j) ((hτle j).trans ht)).trans (hclaim j)
  have h2 : ψ₀ / 2 ^ j = ψ₀ * (1 / 2) ^ j := by rw [div_eq_mul_inv, one_div, inv_pow]
  rw [h2] at h1
  have h3 : ψ₀ * (1 / 2) ^ j < ψ₀ * (ψ t / ψ₀) := mul_lt_mul_of_pos_left hj hpos
  rw [mul_div_cancel₀ _ hpos.ne'] at h3
  linarith

theorem ac_inner {n : ℕ} {x : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}
    (e : EuclideanSpace ℝ (Fin n)) (h : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun u => ⟪e, x u⟫_ℝ) a b := by
  unfold AbsolutelyContinuousOnInterval at h ⊢
  have h2 := h.const_mul ‖e‖
  rw [mul_zero] at h2
  refine squeeze_zero (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg)) (fun E => ?_) h2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Real.dist_eq, ← inner_sub_right, dist_eq_norm]
  exact abs_real_inner_le_norm _ _

theorem norm_sub_le_integral {n : ℕ} {x : ℝ → EuclideanSpace ℝ (Fin n)} {t b : ℝ} (htb : t ≤ b)
    (hac : AbsolutelyContinuousOnInterval x t b)
    (hdiff : ∀ᵐ u, t ≤ u → DifferentiableAt ℝ x u)
    (hint : IntervalIntegrable (fun u => ‖deriv x u‖) volume t b) :
    ‖x b - x t‖ ≤ ∫ u in t..b, ‖deriv x u‖ := by
  set e := x b - x t with he
  have hg := ac_inner e hac
  have hftc := hg.integral_deriv_eq_sub
  have hee : ⟪e, x b⟫_ℝ - ⟪e, x t⟫_ℝ = ‖e‖ ^ 2 := by
    rw [← inner_sub_right, ← he, real_inner_self_eq_norm_sq]
  rw [hee] at hftc
  have hint2 : IntervalIntegrable (fun u => ‖e‖ * ‖deriv x u‖) volume t b := hint.const_mul _
  have hmono : ∫ u in t..b, deriv (fun u => ⟪e, x u⟫_ℝ) u ≤ ∫ u in t..b, ‖e‖ * ‖deriv x u‖ := by
    apply intervalIntegral.integral_mono_ae_restrict htb hg.intervalIntegrable_deriv hint2
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hdiff] with u hu hmem
    have hd := hu hmem.1
    have hD : HasDerivAt (fun u => ⟪e, x u⟫_ℝ) ⟪e, deriv x u⟫_ℝ u := by
      exact ((innerSL ℝ e).hasFDerivAt).comp_hasDerivAt u hd.hasDerivAt
    rw [hD.deriv]
    exact real_inner_le_norm _ _
  rw [hftc, intervalIntegral.integral_const_mul] at hmono
  have hI : 0 ≤ ∫ u in t..b, ‖deriv x u‖ :=
    intervalIntegral.integral_nonneg htb (fun u _ => norm_nonneg _)
  rcases (norm_nonneg e).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hI
  · have : ‖e‖ * ‖e‖ ≤ ‖e‖ * ∫ u in t..b, ‖deriv x u‖ := by nlinarith
    exact le_of_mul_le_mul_left this hpos

end Thm47Aux

open NonsmoothLojasiewicz.Traj NonconvexSplitting.Shared in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (hbdd : Bornology.IsBounded (x '' timeDom T)) :
    T = ⊤ ∧ ∃ a ∈ NonsmoothLojasiewicz.Continuous.crit f, Tendsto x atTop (𝓝 a) ∧
      ∀ θ : ℝ, IsLojExponent f a θ →
        ∃ k : ℝ, 0 < k ∧ ∃ k' : ℝ, 0 < k' ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧
          (1 / 2 < θ → ∀ t : ℝ, t₀ ≤ t →
            ‖x t - a‖ ≤ k * (t + 1) ^ (-((1 - θ) / (2 * θ - 1)))) ∧
          (θ = 1 / 2 → ∀ t : ℝ, t₀ ≤ t → ‖x t - a‖ ≤ k * Real.exp (-k' * t)) ∧
          (θ < 1 / 2 → ∃ t₁ : ℝ, ∀ t : ℝ, t₁ ≤ t → x t = a) := by
  obtain ⟨hT, _hlen, a, hacrit, hxa⟩ :=
    NonsmoothLojasiewicz.Traj.thm4_5_finite_length f hH1 hH2 hH3 x T hx hbdd
  refine ⟨hT, a, hacrit, hxa, ?_⟩
  intro θ hθ
  obtain ⟨_hfa, hθ0, hθ1, C, U, hU, hC⟩ := hθ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  set c : ℝ := max C 1 with hcdef
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h20 : ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y,
      |(f y).toReal - (f a).toReal| ^ θ ≤ c * ‖v‖ := fun y hy v hv =>
    (hC y (hball hy) v hv).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨t₀, _ht₀, htail⟩ :=
    NonsmoothLojasiewicz.Traj.tail_length_bound f hH1 hH2 hH3 x T hx a hxa c θ ε hc hθ0 hθ1 hε h20
  obtain ⟨t₁, ht₁⟩ := Metric.tendsto_atTop.1 hxa ε hε
  set s₀ : ℝ := max (max t₀ t₁) 0 + 1 with hs₀
  have hs₀1 : 1 ≤ s₀ := by have := le_max_right (max t₀ t₁) 0; linarith
  have hs₀t₀ : t₀ ≤ s₀ := by
    have := le_max_left t₀ t₁; have := le_max_left (max t₀ t₁) 0; linarith
  have hs₀t₁ : t₁ ≤ s₀ := by
    have := le_max_right t₀ t₁; have := le_max_left (max t₀ t₁) 0; linarith
  have hθ1' : 0 < 1 - θ := by linarith
  set Ψ : ℝ → ℝ≥0∞ := fun t => ∫⁻ s in Set.Ioi t, ‖deriv x s‖ₑ with hΨ
  set ψ : ℝ → ℝ := fun t => (Ψ t).toReal with hψ
  have hΨfin : ∀ t, s₀ ≤ t → Ψ t ≠ ⊤ := fun t ht =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htail t (hs₀t₀.trans ht))
  have hψbound : ∀ t, s₀ ≤ t →
      ψ t ≤ c / (1 - θ) * |(f (x t)).toReal - (f a).toReal| ^ (1 - θ) := by
    intro t ht
    have hc1 : 0 ≤ c / (1 - θ) := div_nonneg hc.le hθ1'.le
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc1 (Real.rpow_nonneg (abs_nonneg _) _))
    refine (htail t (hs₀t₀.trans ht)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (Real.abs_rpow_le_abs_rpow _ _)) hc1
  have hae := hx.1.2.2.1
  set α : ℝ := θ / (1 - θ) with hαdef
  have hα0 : 0 ≤ α := div_nonneg hθ0 hθ1'.le
  set M : ℝ := c * (c / (1 - θ)) ^ α with hM
  have hMpos : 0 < M := mul_pos hc (Real.rpow_pos_of_pos (div_pos hc hθ1') _)
  set K : ℝ := 1 / M with hKdef
  have hK : 0 < K := one_div_pos.2 hMpos
  have hψnn : ∀ t, 0 ≤ ψ t := fun t => ENNReal.toReal_nonneg
  have hlow : ∀ᵐ u, s₀ ≤ u → K * ψ u ^ α ≤ ‖deriv x u‖ := by
    filter_upwards [hae] with u hu hsu
    have hu0 : 0 < u := by linarith
    obtain ⟨v, hv, hvsub⟩ := hu hu0 (by rw [hT]; exact ENNReal.ofReal_lt_top)
    rw [hv.deriv]
    have hin : x u ∈ Metric.ball a ε := ht₁ u (hs₀t₁.trans hsu)
    have hL := h20 (x u) hin (-v) hvsub
    rw [norm_neg] at hL
    have hb := hψbound u hsu
    set R := |(f (x u)).toReal - (f a).toReal| with hR
    have hR0 : 0 ≤ R := abs_nonneg _
    have h1 : ψ u ^ α ≤ (c / (1 - θ) * R ^ (1 - θ)) ^ α :=
      Real.rpow_le_rpow (hψnn u) hb hα0
    have h2 : (c / (1 - θ) * R ^ (1 - θ)) ^ α = (c / (1 - θ)) ^ α * R ^ θ := by
      rw [Real.mul_rpow (div_pos hc hθ1').le (Real.rpow_nonneg hR0 _), ← Real.rpow_mul hR0]
      congr 2
      rw [hαdef]; field_simp
    rw [h2] at h1
    have h3 : ψ u ^ α ≤ (c / (1 - θ)) ^ α * (c * ‖v‖) :=
      h1.trans (mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg (div_pos hc hθ1').le _))
    have h4 : K * ψ u ^ α ≤ K * ((c / (1 - θ)) ^ α * (c * ‖v‖)) :=
      mul_le_mul_of_nonneg_left h3 hK.le
    have h5 : K * ((c / (1 - θ)) ^ α * (c * ‖v‖)) = ‖v‖ := by
      rw [hKdef, hM]; field_simp
    linarith
  have hΨanti : ∀ s t, s ≤ t → Ψ t ≤ Ψ s := fun s t h =>
    lintegral_mono_set (Set.Ioi_subset_Ioi h)
  have hD : ∀ s t, s₀ ≤ s → s ≤ t → K * (t - s) * ψ t ^ α ≤ ψ s - ψ t := by
    intro s t hs hst
    have hsplit : Ψ s = (∫⁻ u in Set.Ioc s t, ‖deriv x u‖ₑ) + Ψ t := by
      simp only [hΨ]
      rw [← Set.Ioc_union_Ioi_eq_Ioi hst, lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
    have hc0 : 0 ≤ K * ψ t ^ α := mul_nonneg hK.le (Real.rpow_nonneg (hψnn t) _)
    have hlowI : ENNReal.ofReal (K * ψ t ^ α * (t - s)) ≤ ∫⁻ u in Set.Ioc s t, ‖deriv x u‖ₑ := by
      have hae2 : ∀ᵐ u ∂(volume.restrict (Set.Ioc s t)),
          ENNReal.ofReal (K * ψ t ^ α) ≤ ‖deriv x u‖ₑ := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hlow] with u hu hmem
        have hsu : s₀ ≤ u := hs.trans hmem.1.le
        have h1 : ψ t ≤ ψ u := ENNReal.toReal_mono (hΨfin u hsu) (hΨanti u t hmem.2)
        have h2 : K * ψ t ^ α ≤ K * ψ u ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hψnn t) h1 hα0) hK.le
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h2.trans (hu hsu))
      calc ENNReal.ofReal (K * ψ t ^ α * (t - s))
          = ENNReal.ofReal (K * ψ t ^ α) * volume (Set.Ioc s t) := by
            rw [Real.volume_Ioc, ← ENNReal.ofReal_mul hc0]
        _ = ∫⁻ _ in Set.Ioc s t, ENNReal.ofReal (K * ψ t ^ α) := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ u in Set.Ioc s t, ‖deriv x u‖ₑ := lintegral_mono_ae hae2
    have hfin_t := hΨfin t (hs.trans hst)
    have hfin_s := hΨfin s hs
    have hIfin : (∫⁻ u in Set.Ioc s t, ‖deriv x u‖ₑ) ≠ ⊤ := by
      intro h; apply hfin_s; rw [hsplit, h, top_add]
    have hsum : ψ s = (∫⁻ u in Set.Ioc s t, ‖deriv x u‖ₑ).toReal + ψ t := by
      simp only [hψ]; rw [hsplit, ENNReal.toReal_add hIfin hfin_t]
    have h3 : K * ψ t ^ α * (t - s) ≤ (∫⁻ u in Set.Ioc s t, ‖deriv x u‖ₑ).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hIfin).1 hlowI
    have : K * (t - s) * ψ t ^ α = K * ψ t ^ α * (t - s) := by ring
    linarith
  have hdist : ∀ t, s₀ ≤ t → ‖x t - a‖ ≤ ψ t := by
    intro t ht
    have hint : IntegrableOn (fun u => ‖deriv x u‖) (Set.Ioi t) := by
      refine ⟨(measurable_deriv x).norm.aestronglyMeasurable, ?_⟩
      simp only [HasFiniteIntegral, enorm_norm]
      exact lt_top_iff_ne_top.2 (hΨfin t ht)
    have hb : ∀ b, t ≤ b → ‖x b - x t‖ ≤ ψ t := by
      intro b htb
      have hac : AbsolutelyContinuousOnInterval x t b :=
        (hx.1.2.1 b (by linarith) (by rw [hT]; exact ENNReal.ofReal_lt_top)).mono
          (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨by linarith, htb⟩))
            (Set.mem_uIcc.2 (Or.inl ⟨by linarith, le_rfl⟩)))
      have hdiff : ∀ᵐ u, t ≤ u → DifferentiableAt ℝ x u := by
        filter_upwards [hae] with u hu htu
        obtain ⟨v, hv, _⟩ := hu (by linarith) (by rw [hT]; exact ENNReal.ofReal_lt_top)
        exact hv.differentiableAt
      have hII : IntervalIntegrable (fun u => ‖deriv x u‖) volume t b :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le htb).2 (hint.mono_set Set.Ioc_subset_Ioi_self)
      refine (Thm47Aux.norm_sub_le_integral htb hac hdiff hII).trans ?_
      rw [intervalIntegral.integral_of_le htb,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => norm_nonneg _)
          (hint.mono_set Set.Ioc_subset_Ioi_self).aestronglyMeasurable]
      apply ENNReal.toReal_mono (hΨfin t ht)
      simp_rw [ofReal_norm]
      exact lintegral_mono_set Set.Ioc_subset_Ioi_self
    have hlim : Tendsto (fun b => ‖x b - x t‖) atTop (𝓝 ‖a - x t‖) :=
      (hxa.sub_const (x t)).norm
    have := le_of_tendsto hlim (eventually_atTop.2 ⟨t, hb⟩)
    rwa [norm_sub_rev] at this
  rcases lt_trichotomy θ (1 / 2) with hlt | heq | hgt
  · have hα1 : α < 1 := by rw [hαdef, div_lt_one hθ1']; linarith
    obtain ⟨t₂, ht₂s, ht₂⟩ := Thm47Aux.decay_finite hK hα0 hα1 (fun t _ => hψnn t) hD
    refine ⟨1, one_pos, 1, one_pos, 0, le_rfl, fun h => absurd h (by linarith),
      fun h => absurd h (by linarith), fun _ => ⟨t₂, fun t ht => ?_⟩⟩
    have := hdist t (ht₂s.trans ht)
    rw [show ψ t = 0 from ht₂ t ht] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  · have hα : α = 1 := by rw [hαdef, heq]; norm_num
    have hD1 : ∀ s t, s₀ ≤ s → s ≤ t → K * (t - s) * ψ t ^ (1 : ℝ) ≤ ψ s - ψ t := by
      intro s t hs hst
      have := hD s t hs hst
      rwa [hα] at this
    have hdec := Thm47Aux.decay_one hK (fun t _ => hψnn t) hD1
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    set k' : ℝ := K * Real.log 2 with hk'
    have hk'pos : 0 < k' := mul_pos hK hlog
    have hψs₀ := hψnn s₀
    refine ⟨2 * ψ s₀ * Real.exp (k' * s₀) + 1, by positivity, k', hk'pos, s₀, by linarith,
      fun h => absurd h (by linarith), fun _ t ht => ?_, fun h => absurd h (by linarith)⟩
    have hE := Real.exp_pos (-k' * t)
    have hE2 : 0 ≤ 2 * ψ s₀ * Real.exp (k' * s₀) := by positivity
    calc ‖x t - a‖ ≤ ψ t := hdist t ht
      _ ≤ 2 * ψ s₀ * Real.exp (-k' * (t - s₀)) := hdec t ht
      _ = 2 * ψ s₀ * Real.exp (k' * s₀) * Real.exp (-k' * t) := by
          rw [mul_assoc (2 * ψ s₀), ← Real.exp_add]; ring_nf
      _ ≤ (2 * ψ s₀ * Real.exp (k' * s₀) + 1) * Real.exp (-k' * t) := by nlinarith
  · have hα1 : 1 < α := by rw [hαdef, one_lt_div hθ1']; linarith
    set γ : ℝ := (1 - θ) / (2 * θ - 1) with hγdef
    have h2θ : 0 < 2 * θ - 1 := by linarith
    have h2θ' : 2 * θ - 1 ≠ 0 := h2θ.ne'
    have h1θ : 1 - θ ≠ 0 := hθ1'.ne'
    have hγ : γ * (α - 1) = 1 := by
      rw [hγdef, hαdef, div_sub_one h1θ, div_mul_div_comm]
      rw [div_eq_one_iff_eq (mul_ne_zero h2θ' h1θ)]
      ring
    have hγ0 : 0 < γ := div_pos hθ1' h2θ
    obtain ⟨A, hA, hdec⟩ := Thm47Aux.decay_pow hK hα1 hγ (fun t _ => hψnn t) hD
    refine ⟨A * 2 ^ γ, by positivity, 1, one_pos, 2 * s₀ + 1, by linarith,
      fun _ t ht => ?_, fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩
    have hts : s₀ < t := by linarith
    have hd : (t + 1) / 2 ≤ t - s₀ := by linarith
    have h1 : (t - s₀) ^ (-γ) ≤ ((t + 1) / 2) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hd (by linarith)
    have h2 : ((t + 1) / 2) ^ (-γ) = 2 ^ γ * (t + 1) ^ (-γ) := by
      rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    calc ‖x t - a‖ ≤ ψ t := hdist t (by linarith)
      _ ≤ A * (t - s₀) ^ (-γ) := hdec t hts
      _ ≤ A * (2 ^ γ * (t + 1) ^ (-γ)) := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hA.le
      _ = A * 2 ^ γ * (t + 1) ^ (-γ) := by ring
