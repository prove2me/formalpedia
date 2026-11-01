-- Prove2me | solution 1 for InconsistentDR.Shadow.eq_75_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:09:21.267273+00:00
-- url     : https://prove2.me/submissions/cd6a12a7-c2c1-4dbf-8926-dd425e417693

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Operators

open scoped InnerProductSpace Topology
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization

namespace DRShadow75Aux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Firm nonexpansiveness implies nonexpansiveness. -/
lemma nonexp (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2) (x y : X) :
    ‖T x - T y‖ ≤ ‖x - y‖ := by
  have h := hfne x y
  have h2 : ‖T x - T y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith [sq_nonneg ‖(x - T x) - (y - T y)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `Id - T` is monotone. -/
lemma G_mono (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2) (x y : X) :
    0 ≤ ⟪(x - T x) - (y - T y), x - y⟫_ℝ := by
  have h := hfne x y
  have e : x - y = (T x - T y) + ((x - T x) - (y - T y)) := by abel
  have h3 : ‖x - y‖ ^ 2 = ‖T x - T y‖ ^ 2 + 2 * ⟪T x - T y, (x - T x) - (y - T y)⟫_ℝ
      + ‖(x - T x) - (y - T y)‖ ^ 2 := by
    rw [e, norm_add_sq_real]
  have h4 : ⟪(x - T x) - (y - T y), x - y⟫_ℝ =
      ⟪(x - T x) - (y - T y), T x - T y⟫_ℝ + ‖(x - T x) - (y - T y)‖ ^ 2 := by
    conv_lhs => rw [e]
    rw [inner_add_right, real_inner_self_eq_norm_sq]
  rw [h4, real_inner_comm]
  nlinarith [sq_nonneg ‖(x - T x) - (y - T y)‖]

/-- For `λ > 0`, the equation `u - T u + λ u = c` has a solution (Banach fixed point). -/
lemma exists_perturbed [CompleteSpace X] (T : X → X)
    (hne : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (c : X) (lam : ℝ) (hlam : 0 < lam) :
    ∃ u : X, (u - T u) + lam • u = c := by
  set K : ℝ := (1 + lam)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : K < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  let Φ : X → X := fun u => K • (T u + c)
  have hlip : LipschitzWith ⟨K, hK0⟩ Φ := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [Φ, dist_eq_norm, NNReal.coe_mk]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hK0]
    have : T a + c - (T b + c) = T a - T b := by abel
    rw [this]
    exact mul_le_mul_of_nonneg_left (hne a b) hK0
  have hcon : ContractingWith ⟨K, hK0⟩ Φ := ⟨by exact_mod_cast hK1, hlip⟩
  obtain ⟨u, hu⟩ : ∃ u, Φ u = u := ⟨_, hcon.fixedPoint_isFixedPt⟩
  refine ⟨u, ?_⟩
  have h1 : (1 + lam) • u = T u + c := by
    have : (1 + lam) • Φ u = T u + c := by
      simp only [Φ, smul_smul, hK]
      rw [mul_inv_cancel₀ (by linarith), one_smul]
    rwa [hu] at this
  have h2 : (u - T u) + lam • u = (1 + lam) • u - T u := by
    rw [add_smul, one_smul]; abel
  rw [h2, h1]; abel

lemma num_aux (ε M1 M2 r : ℝ) (hε : 0 < ε) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hr : 0 ≤ r)
    (h : r ^ 2 ≤ ε ^ 2 / (2 * (M1 + ε * M2 + ε)) * (M1 + r * M2)) : r < ε := by
  have hden : 0 < 2 * (M1 + ε * M2 + ε) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at h
  by_contra hcon
  push_neg at hcon
  -- r² · 2(M1 + εM2 + ε) ≤ ε² (M1 + r M2), with r ≥ ε
  have h1 : ε * r * (2 * (M1 + ε * M2 + ε)) ≤ r ^ 2 * (2 * (M1 + ε * M2 + ε)) := by
    apply mul_le_mul_of_nonneg_right _ hden.le; nlinarith
  have h2 : ε ^ 2 * (M1 + r * M2) ≤ ε * r * (M1 + ε * M2) := by
    have : ε ^ 2 * M1 ≤ ε * r * M1 := by
      apply mul_le_mul_of_nonneg_right _ hM1; nlinarith
    nlinarith
  have h3 : ε * r * (2 * (M1 + ε * M2 + ε)) ≤ ε * r * (M1 + ε * M2) := by linarith
  have h4 : 0 < ε * r := mul_pos hε (by linarith)
  have h5 : 2 * (M1 + ε * M2 + ε) ≤ M1 + ε * M2 := le_of_mul_le_mul_left h3 h4
  nlinarith [mul_nonneg hε.le hM2]

/-- Convex combinations of two points of `ran (Id - T)` lie in its closure. -/
lemma comb_mem_closure [CompleteSpace X] (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (y z : X) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    α • (y - T y) + β • (z - T z) ∈ closure (Set.range fun x => x - T x) := by
  obtain ⟨a, ha⟩ : ∃ a, a = y - T y := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = z - T z := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = α • a + β • b := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hc]
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨M1, hM1⟩ : ∃ M, M = ‖c - a‖ * ‖y‖ + ‖c - b‖ * ‖z‖ := ⟨_, rfl⟩
  obtain ⟨M2, hM2⟩ : ∃ M, M = ‖y‖ + ‖z‖ := ⟨_, rfl⟩
  have hM1n : 0 ≤ M1 := by rw [hM1]; positivity
  have hM2n : 0 ≤ M2 := by rw [hM2]; positivity
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = ε ^ 2 / (2 * (M1 + ε * M2 + ε)) := ⟨_, rfl⟩
  have hden : 0 < 2 * (M1 + ε * M2 + ε) := by positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  obtain ⟨u, hu⟩ := exists_perturbed T (nonexp T hfne) c lam hlam0
  refine ⟨u - T u, ⟨u, rfl⟩, ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, p = lam • u := ⟨_, rfl⟩
  have hGu : u - T u = c - p := by rw [hp, ← hu]; abel
  rw [dist_eq_norm, hGu, show c - (c - p) = p by abel]
  have m1 := G_mono T hfne u y
  have m2 := G_mono T hfne u z
  rw [hGu, ← ha] at m1
  rw [hGu, ← hb] at m2
  have hid : α • ((c - p) - a) + β • ((c - p) - b) = -p := by
    have : α • ((c - p) - a) + β • ((c - p) - b) = (α + β) • (c - p) - (α • a + β • b) := by
      module
    rw [this, ← hc, hαβ, one_smul]; abel
  have e1 : ⟪(c - p) - a, u - y⟫_ℝ = ⟪(c - p) - a, u⟫_ℝ - ⟪(c - p) - a, y⟫_ℝ :=
    inner_sub_right _ _ _
  have e2 : ⟪(c - p) - b, u - z⟫_ℝ = ⟪(c - p) - b, u⟫_ℝ - ⟪(c - p) - b, z⟫_ℝ :=
    inner_sub_right _ _ _
  have e3 : α * ⟪(c - p) - a, u⟫_ℝ + β * ⟪(c - p) - b, u⟫_ℝ = -⟪p, u⟫_ℝ := by
    rw [← real_inner_smul_left, ← real_inner_smul_left, ← inner_add_left, hid, inner_neg_left]
  have hpu : ⟪p, u⟫_ℝ * lam = ‖p‖ ^ 2 := by
    rw [hp, real_inner_smul_left, norm_smul, Real.norm_of_nonneg hlam0.le, mul_pow,
      real_inner_self_eq_norm_sq]
    ring
  have b1 : -⟪(c - p) - a, y⟫_ℝ ≤ (‖c - a‖ + ‖p‖) * ‖y‖ := by
    have := real_inner_le_norm (-((c - p) - a)) y
    rw [inner_neg_left, norm_neg] at this
    have h' : ‖(c - p) - a‖ ≤ ‖c - a‖ + ‖p‖ := by
      rw [show (c - p) - a = (c - a) - p by abel]; exact norm_sub_le _ _
    have := mul_le_mul_of_nonneg_right h' (norm_nonneg y)
    linarith
  have b2 : -⟪(c - p) - b, z⟫_ℝ ≤ (‖c - b‖ + ‖p‖) * ‖z‖ := by
    have := real_inner_le_norm (-((c - p) - b)) z
    rw [inner_neg_left, norm_neg] at this
    have h' : ‖(c - p) - b‖ ≤ ‖c - b‖ + ‖p‖ := by
      rw [show (c - p) - b = (c - b) - p by abel]; exact norm_sub_le _ _
    have := mul_le_mul_of_nonneg_right h' (norm_nonneg z)
    linarith
  have hα1 : α ≤ 1 := by linarith
  have hβ1 : β ≤ 1 := by linarith
  have s1 : ⟪p, u⟫_ℝ ≤ α * (-⟪(c - p) - a, y⟫_ℝ) + β * (-⟪(c - p) - b, z⟫_ℝ) := by
    have := mul_nonneg hα m1
    have := mul_nonneg hβ m2
    rw [e1] at *; rw [e2] at *
    nlinarith
  have s2 : α * (-⟪(c - p) - a, y⟫_ℝ) ≤ (‖c - a‖ + ‖p‖) * ‖y‖ := by
    have hnn : 0 ≤ (‖c - a‖ + ‖p‖) * ‖y‖ := by positivity
    rcases le_or_gt 0 (-⟪(c - p) - a, y⟫_ℝ) with h | h
    · nlinarith
    · nlinarith
  have s3 : β * (-⟪(c - p) - b, z⟫_ℝ) ≤ (‖c - b‖ + ‖p‖) * ‖z‖ := by
    have hnn : 0 ≤ (‖c - b‖ + ‖p‖) * ‖z‖ := by positivity
    rcases le_or_gt 0 (-⟪(c - p) - b, z⟫_ℝ) with h | h
    · nlinarith
    · nlinarith
  have hmain : ⟪p, u⟫_ℝ ≤ M1 + ‖p‖ * M2 := by
    rw [hM1, hM2]; nlinarith
  have hmain' : ‖p‖ ^ 2 ≤ lam * (M1 + ‖p‖ * M2) := by
    rw [← hpu]; nlinarith
  rw [hlam] at hmain'
  exact num_aux ε M1 M2 ‖p‖ hε hM1n hM2n (norm_nonneg _) hmain'

/-- The least-norm point `v` of `cl ran (Id - T)` satisfies `‖b - v‖² ≤ ‖b‖² - ‖v‖²` on `ran (Id - T)`. -/
lemma minnorm_ineq [CompleteSpace X] (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (v : X) (hv1 : v ∈ closure (Set.range fun x => x - T x))
    (hv2 : ∀ c ∈ closure (Set.range fun x => x - T x), ‖v‖ ≤ ‖c‖) (z : X) :
    ‖(z - T z) - v‖ ^ 2 ≤ ‖z - T z‖ ^ 2 - ‖v‖ ^ 2 := by
  obtain ⟨b, hb⟩ : ∃ b, b = z - T z := ⟨_, rfl⟩
  rw [← hb]
  -- Step 1: `‖v‖ ≤ ‖(1 - t) v + t b‖` for `t ∈ [0, 1]`.
  have step1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖v‖ ≤ ‖(1 - t) • v + t • b‖ := by
    intro t ht0 ht1
    have hS : IsClosed {a : X | ‖v‖ ≤ ‖(1 - t) • a + t • b‖} :=
      isClosed_le continuous_const (by fun_prop)
    have hsub : (Set.range fun x => x - T x) ⊆ {a : X | ‖v‖ ≤ ‖(1 - t) • a + t • b‖} := by
      rintro _ ⟨y, rfl⟩
      apply hv2
      rw [hb]
      exact comb_mem_closure T hfne y z (1 - t) t (by linarith) ht0 (by ring)
    exact closure_minimal hsub hS hv1
  -- Step 2: `⟪v, b - v⟫ ≥ 0`.
  have step2 : 0 ≤ ⟪v, b - v⟫_ℝ := by
    by_contra hneg
    push_neg at hneg
    set w := b - v
    have hk : 0 < ‖w‖ ^ 2 + 1 := by positivity
    set q := -⟪v, w⟫_ℝ
    have hq : 0 < q := by simp only [q]; linarith
    set t := min 1 (q / (‖w‖ ^ 2 + 1))
    have ht0 : 0 < t := lt_min one_pos (div_pos hq hk)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htq : t ≤ q / (‖w‖ ^ 2 + 1) := min_le_right _ _
    have h1 := step1 t ht0.le ht1
    have e : (1 - t) • v + t • b = v + t • w := by simp only [w]; module
    rw [e] at h1
    have h2 : ‖v‖ ^ 2 ≤ ‖v + t • w‖ ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le,
      mul_pow] at h2
    have h3 : t * ‖w‖ ^ 2 ≤ q := by
      have := mul_le_mul_of_nonneg_right htq hk.le
      rw [div_mul_cancel₀ _ hk.ne'] at this
      nlinarith [sq_nonneg ‖w‖]
    have h4 : 0 ≤ t * (2 * ⟪v, w⟫_ℝ + t * ‖w‖ ^ 2) := by nlinarith
    have h5 : 2 * ⟪v, w⟫_ℝ + t * ‖w‖ ^ 2 < 0 := by
      have : ⟪v, w⟫_ℝ = -q := by simp only [q]; ring
      rw [this]; linarith
    nlinarith
  -- Step 3: expand `‖b‖² = ‖v + (b - v)‖²`.
  have e : ‖b‖ ^ 2 = ‖v‖ ^ 2 + 2 * ⟪v, b - v⟫_ℝ + ‖b - v‖ ^ 2 := by
    rw [← norm_add_sq_real]; congr 2; abel
  linarith

/-- Baillon–Bruck–Reich for a firmly nonexpansive `T`: `Tⁿx - Tⁿ⁺¹x → v`. -/
lemma bbr [CompleteSpace X] (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (v : X) (hv1 : v ∈ closure (Set.range fun x => x - T x))
    (hv2 : ∀ c ∈ closure (Set.range fun x => x - T x), ‖v‖ ≤ ‖c‖) (x : X) :
    Tendsto (fun n : ℕ => T^[n] x - T^[n + 1] x) atTop (𝓝 v) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε ^ 2 / 8 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  -- choose `y` with `‖y - T y‖² ≤ ‖v‖² + δ`
  obtain ⟨y, hy⟩ : ∃ y, ‖y - T y‖ ^ 2 ≤ ‖v‖ ^ 2 + δ := by
    have hk : 0 < 2 * ‖v‖ + 1 := by positivity
    obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (δ / (2 * ‖v‖ + 1)) := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hη]; exact lt_min one_pos (div_pos hδ0 hk)
    have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
    have hη2 : η ≤ δ / (2 * ‖v‖ + 1) := by rw [hη]; exact min_le_right _ _
    obtain ⟨c, ⟨y, rfl⟩, hc⟩ := Metric.mem_closure_iff.mp hv1 η hη0
    refine ⟨y, ?_⟩
    rw [dist_eq_norm] at hc
    have h1 : ‖y - T y‖ ≤ ‖v‖ + η := by
      have := norm_sub_norm_le (y - T y) v
      rw [norm_sub_rev] at hc
      linarith
    have h2 : η * (2 * ‖v‖ + 1) ≤ δ := by
      have := mul_le_mul_of_nonneg_right hη2 hk.le
      rwa [div_mul_cancel₀ _ hk.ne'] at this
    have h3 : ‖y - T y‖ ^ 2 ≤ (‖v‖ + η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [norm_nonneg v]
  -- displacement along the `y`-orbit is nonincreasing
  have hdisp : ∀ n : ℕ, ‖T^[n] y - T (T^[n] y)‖ ≤ ‖y - T y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (nonexp T hfne _ _).trans ih
  have hq : ∀ n : ℕ, ‖(T^[n] y - T (T^[n] y)) - v‖ ^ 2 ≤ δ := by
    intro n
    have h1 := minnorm_ineq T hfne v hv1 hv2 (T^[n] y)
    have h2 : ‖T^[n] y - T (T^[n] y)‖ ^ 2 ≤ ‖y - T y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdisp n) 2
    linarith
  -- telescoping with firm nonexpansiveness
  set D : ℕ → ℝ := fun n => ‖(T^[n] x - T (T^[n] x)) - (T^[n] y - T (T^[n] y))‖ ^ 2 with hD
  have hstep : ∀ n : ℕ, ‖T^[n + 1] x - T^[n + 1] y‖ ^ 2 + D n ≤ ‖T^[n] x - T^[n] y‖ ^ 2 := by
    intro n
    have := hfne (T^[n] x) (T^[n] y)
    simp only [hD, Function.iterate_succ_apply']
    exact this
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, D i ≤ ‖x - y‖ ^ 2 - ‖T^[n] x - T^[n] y‖ ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      linarith
  have hDnn : ∀ n, 0 ≤ D n := fun n => by positivity
  have hsummable : Summable D := by
    refine summable_of_sum_range_le hDnn (c := ‖x - y‖ ^ 2) fun n => ?_
    have := hsum n
    nlinarith [sq_nonneg ‖T^[n] x - T^[n] y‖]
  have hD0 := hsummable.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at hD0
  obtain ⟨N, hN⟩ := hD0 δ hδ0
  refine ⟨N, fun n hn => ?_⟩
  have hDn : D n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hDnn n)] at this
    exact this
  rw [dist_eq_norm]
  have e : T^[n] x - T^[n + 1] x - v =
      ((T^[n] x - T (T^[n] x)) - (T^[n] y - T (T^[n] y))) + ((T^[n] y - T (T^[n] y)) - v) := by
    rw [Function.iterate_succ_apply']; abel
  rw [e]
  set P := ‖(T^[n] x - T (T^[n] x)) - (T^[n] y - T (T^[n] y))‖
  set Q := ‖(T^[n] y - T (T^[n] y)) - v‖
  have hP : P ^ 2 < δ := hDn
  have hQ : Q ^ 2 ≤ δ := hq n
  have hP0 : 0 ≤ P := norm_nonneg _
  have hQ0 : 0 ≤ Q := norm_nonneg _
  have hPQ : P + Q < ε := by
    have : (P + Q) ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg (P - Q)]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  exact lt_of_le_of_lt (norm_add_le _ _) hPQ

/-- Monotonicity of the subdifferential. -/
lemma subgrad_mono (f : X → EReal) {x y a b : X} (ha : a ∈ subgrad f x) (hb : b ∈ subgrad f y) :
    0 ≤ ⟪x - y, a - b⟫_ℝ := by
  obtain ⟨F, hF⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal ha.2.1 ha.1).symm⟩
  obtain ⟨G, hG⟩ : ∃ r : ℝ, f y = r := ⟨(f y).toReal, (EReal.coe_toReal hb.2.1 hb.1).symm⟩
  have h1 := ha.2.2 y
  have h2 := hb.2.2 x
  rw [hF, hG] at h1
  rw [hF, hG] at h2
  have h1' : F + ⟪y - x, a⟫_ℝ ≤ G := by exact_mod_cast h1
  have h2' : G + ⟪x - y, b⟫_ℝ ≤ F := by exact_mod_cast h2
  have e : ⟪y - x, a⟫_ℝ = -⟪x - y, a⟫_ℝ := by rw [← inner_neg_left, neg_sub]
  rw [inner_sub_right]
  linarith

/-- The proximal map is firmly nonexpansive. -/
lemma prox_fne (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) (x y : X) :
    ‖P x - P y‖ ^ 2 ≤ ⟪P x - P y, x - y⟫_ℝ := by
  have hx := hP x
  have hy := hP y
  rw [inv_one, one_smul] at hx hy
  have := subgrad_mono f hx hy
  have e : (x - P x) - (y - P y) = (x - y) - (P x - P y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at this
  linarith

/-- The reflected proximal map is nonexpansive. -/
lemma refl_nonexp (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) (x y : X) :
    ‖InconsistentDR.Shadow.refl P x - InconsistentDR.Shadow.refl P y‖ ≤ ‖x - y‖ := by
  have h := prox_fne f P hP x y
  have e : InconsistentDR.Shadow.refl P x - InconsistentDR.Shadow.refl P y =
      (2 : ℝ) • (P x - P y) - (x - y) := by
    simp only [InconsistentDR.Shadow.refl]; module
  have h2 : ‖InconsistentDR.Shadow.refl P x - InconsistentDR.Shadow.refl P y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e, norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Douglas–Rachford operator of two proximal maps is firmly nonexpansive. -/
lemma drT_fne (f g : X → EReal) (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf)
    (hPg : IsResolvent 1 (subgrad g) Pg) (x y : X) :
    ‖InconsistentDR.Shadow.drT Pf Pg x - InconsistentDR.Shadow.drT Pf Pg y‖ ^ 2 +
      ‖(x - InconsistentDR.Shadow.drT Pf Pg x) - (y - InconsistentDR.Shadow.drT Pf Pg y)‖ ^ 2
      ≤ ‖x - y‖ ^ 2 := by
  open InconsistentDR.Shadow in
  have hN : ‖refl Pg (refl Pf x) - refl Pg (refl Pf y)‖ ≤ ‖x - y‖ :=
    (refl_nonexp g Pg hPg _ _).trans (refl_nonexp f Pf hPf x y)
  open InconsistentDR.Shadow in
  have e1 : drT Pf Pg x - drT Pf Pg y =
      (1 / 2 : ℝ) • ((x - y) + (refl Pg (refl Pf x) - refl Pg (refl Pf y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  open InconsistentDR.Shadow in
  have e2 : (x - drT Pf Pg x) - (y - drT Pf Pg y) =
      (1 / 2 : ℝ) • ((x - y) - (refl Pg (refl Pf x) - refl Pg (refl Pf y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  rw [e1, e2]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
  generalize x - y = a at h2 ⊢
  generalize InconsistentDR.Shadow.refl Pg (InconsistentDR.Shadow.refl Pf x) -
    InconsistentDR.Shadow.refl Pg (InconsistentDR.Shadow.refl Pf y) = b at h2 ⊢
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  have : ‖(1 / 2 : ℝ)‖ ^ 2 = 1 / 4 := by norm_num
  rw [this]
  nlinarith

end DRShadow75Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v) (x : X) :
    (∀ n : ℕ, Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) =
      (drT Pf Pg)^[n] x - (drT Pf Pg)^[n + 1] x) ∧
    Tendsto (fun n : ℕ => (drT Pf Pg)^[n] x - (drT Pf Pg)^[n + 1] x) atTop (𝓝 v) := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [Function.iterate_succ_apply']
    simp only [drT]; abel
  · exact DRShadow75Aux.bbr (drT Pf Pg) (DRShadow75Aux.drT_fne f g Pf Pg hPf hPg) v hv.1 hv.2 x
