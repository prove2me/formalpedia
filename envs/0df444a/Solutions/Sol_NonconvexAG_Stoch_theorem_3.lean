-- Prove2me | solution 1 for NonconvexAG.Stoch.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T19:11:08.263545+00:00
-- url     : https://prove2.me/submissions/fc9c317f-2900-4d34-ac51-0d020e556014

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace RSAG8be

/-! ## Generic smooth / convex analysis (copied from our NonconvexAG.Smooth.theorem_1 proof) -/

theorem ag_line_deriv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem ag_descent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : V) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := ag_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem ag_convex_fo {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : V) :
    F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x with hw
  let φ : ℝ → ℝ := fun s => F (x + s • w)
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ p q hp hq hpq
    have h := hc.2 (Set.mem_univ (x + a • w)) (Set.mem_univ (x + b • w)) hp hq hpq
    have e : p • (x + a • w) + q • (x + b • w) = x + (p • a + q • b) • w := by
      have : p • (x + a • w) + q • (x + b • w) = (p + q) • x + (p * a + q * b) • w := by
        module
      rw [this, hpq, one_smul, smul_eq_mul, smul_eq_mul]
    show F (x + (p • a + q • b) • w) ≤ p • F (x + a • w) + q • F (x + b • w)
    rw [← e]
    exact h
  have hd := ag_line_deriv hF x w 0
  rw [zero_smul, add_zero] at hd
  have hs := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at hs
  have h1 : φ 1 = F y := by
    show F (x + (1:ℝ) • w) = F y
    rw [one_smul, hw, add_sub_cancel]
  have h0 : φ 0 = F x := by
    show F (x + (0:ℝ) • w) = F x
    rw [zero_smul, add_zero]
  rw [h1, h0] at hs
  norm_num at hs
  linarith

/-! ## Probability infrastructure -/

/-- Tower property for an inner product with an `m`-measurable left factor. -/
theorem cross_eq {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {Y Z W : Ω → V}
    (hY : AEStronglyMeasurable[m] Y μ)
    (hYZ : Integrable (fun ω => ⟪Y ω, Z ω⟫) μ) (hZ : Integrable Z μ)
    (hce : μ[Z|m] =ᵐ[μ] W) :
    ∫ ω, ⟪Y ω, Z ω⟫ ∂μ = ∫ ω, ⟪Y ω, W ω⟫ ∂μ := by
  have h1 : μ[fun ω => ⟪Y ω, Z ω⟫|m] =ᵐ[μ] fun ω => ⟪Y ω, μ[Z|m] ω⟫ :=
    condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hY hYZ hZ
  rw [← integral_condExp hm]
  refine integral_congr_ae ?_
  filter_upwards [h1, hce] with ω h1 h2
  rw [h1, h2]

/-- Averaging over an independent random index. -/
theorem avg_R {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] (X : Ω → S) (R : Ω → ℕ) (hR : Measurable R)
    (hind : IndepFun R X μ) (N : ℕ) (hRN : ∀ ω, R ω ∈ Finset.Icc 1 N)
    (F : ℕ → S → ℝ) (hF : ∀ k, Measurable (F k))
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => F k (X ω)) μ) :
    Integrable (fun ω => F (R ω) (X ω)) μ ∧
    ∫ ω, F (R ω) (X ω) ∂μ =
      ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} * ∫ ω, F k (X ω) ∂μ := by
  have hdecomp : (fun ω => F (R ω) (X ω)) = fun ω => ∑ k ∈ Finset.Icc 1 N,
      (if R ω = k then (1:ℝ) else 0) * F k (X ω) := by
    funext ω
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [hRN ω]
  have hmeasS : ∀ k, MeasurableSet {ω | R ω = k} := fun k => hR (measurableSet_singleton k)
  have hind_k : ∀ k, (fun ω => {ω | R ω = k}.indicator (1 : Ω → ℝ) ω) =
      fun ω => (if R ω = k then (1:ℝ) else 0) := by
    intro k; funext ω; simp [Set.indicator_apply]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => (if R ω = k then (1:ℝ) else 0) * F k (X ω)) μ := by
    intro k hk
    have : (fun ω => (if R ω = k then (1:ℝ) else 0) * F k (X ω)) =
        {ω | R ω = k}.indicator (fun ω => F k (X ω)) := by
      funext ω; by_cases h : R ω = k <;> simp [h]
    rw [this]; exact (hint k hk).indicator (hmeasS k)
  refine ⟨?_, ?_⟩
  · rw [hdecomp]; exact integrable_finset_sum _ hterm
  · rw [hdecomp, integral_finset_sum _ hterm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hφ : Measurable fun r : ℕ => if r = k then (1:ℝ) else 0 := measurable_of_countable _
    have hind' : IndepFun (fun ω => if R ω = k then (1:ℝ) else 0) (fun ω => F k (X ω)) μ :=
      hind.comp hφ (hF k)
    have hm1 : AEStronglyMeasurable (fun ω => if R ω = k then (1:ℝ) else 0) μ :=
      (hφ.comp hR).aestronglyMeasurable
    have := hind'.integral_mul_eq_mul_integral hm1 (hint k hk).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, ← hind_k k, integral_indicator_one (hmeasS k)]

/-- Inner products of two square-integrable vectors are integrable. -/
theorem int_inner {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Y Z : Ω → V}
    (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : Integrable (fun ω => ⟪Y ω, Z ω⟫) μ := by
  have hY2 := (memLp_two_iff_integrable_sq_norm hY.1).1 hY
  have hZ2 := (memLp_two_iff_integrable_sq_norm hZ.1).1 hZ
  refine Integrable.mono' (hY2.add hZ2) (hY.1.inner hZ.1) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (Y ω) (Z ω)
  have h2 := norm_nonneg (Y ω)
  have h3 := norm_nonneg (Z ω)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖Y ω‖ - ‖Z ω‖)]

theorem int_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Type*}
    [NormedAddCommGroup V] {Y : Ω → V}
    (hY : MemLp Y 2 μ) : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hY.1).1 hY

/-- Lipschitz images of square-integrable vectors are square-integrable. -/
theorem memLp_lip {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {X : Ω → V} (hX : MemLp X 2 μ) :
    MemLp (fun ω => g (X ω)) 2 μ := by
  have hcont : Continuous g := by
    refine (LipschitzWith.of_dist_le' (K := L) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]; exact hg x y
  have hb1 : MemLp (fun _ : Ω => ‖g 0‖) 2 μ := memLp_const _
  have hb2 : MemLp (fun ω => L * ‖X ω‖) 2 μ := hX.norm.const_mul L
  have hb := hb1.add hb2
  refine hb.of_le (hcont.comp_aestronglyMeasurable hX.1) (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  have h1 := hg (X ω) 0
  rw [sub_zero] at h1
  have h2 : ‖g (X ω)‖ ≤ ‖g 0‖ + ‖g (X ω) - g 0‖ := by
    have := norm_add_le (g 0) (g (X ω) - g 0)
    rwa [add_sub_cancel] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

/-! ## Pathwise one-step inequalities -/

open NonconvexAG.Stoch
open GhadimiLan.RSG (E)

theorem stepA_path {n : ℕ} {Ψ : E n → ℝ} {g : E n → E n} {L : ℝ}
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (xp ap md d : E n) (a l : ℝ) (hl : 0 ≤ l)
    (hmd : md - xp = (1 - a) • (ap - xp)) :
    Ψ (xp - l • (g md + d)) ≤ Ψ xp - l * (1 - L * l) * ‖g md‖ ^ 2
      + L * (1 - a) ^ 2 / 2 * ‖ap - xp‖ ^ 2 + L * l ^ 2 / 2 * ‖d‖ ^ 2
      + ⟪(L * l ^ 2) • g md - l • g xp, d⟫ := by
  have hL := hΨ.1
  have h1 := ag_descent hΨ.2.1 hΨ.2.2 xp (xp - l • (g md + d))
  have e1 : xp - l • (g md + d) - xp = -(l • (g md + d)) := by abel
  rw [e1, inner_neg_right, norm_neg, real_inner_smul_right, inner_add_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, norm_add_sq_real] at h1
  have hlip := hΨ.2.2 md xp
  have hmdn : ‖md - xp‖ ^ 2 = (1 - a) ^ 2 * ‖ap - xp‖ ^ 2 := by
    rw [hmd, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have e2 : l * ⟪g xp, g md⟫ = l * ‖g md‖ ^ 2 - l * ⟪g md - g xp, g md⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]; ring
  have e3 : ⟪g md - g xp, g md⟫ ≤ L * ‖md - xp‖ * ‖g md‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hlip (norm_nonneg _))
  have f1 : l * ⟪g md - g xp, g md⟫ ≤ l * (L * ‖md - xp‖ * ‖g md‖) :=
    mul_le_mul_of_nonneg_left e3 hl
  have f2 : l * (L * ‖md - xp‖ * ‖g md‖) ≤ L / 2 * (l ^ 2 * ‖g md‖ ^ 2) + L / 2 * ‖md - xp‖ ^ 2 := by
    have := mul_nonneg hL (sq_nonneg (l * ‖g md‖ - ‖md - xp‖))
    nlinarith
  have e4 : ⟪(L * l ^ 2) • g md - l • g xp, d⟫ = L * l ^ 2 * ⟪g md, d⟫ - l * ⟪g xp, d⟫ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  rw [e4]
  have f3 : L / 2 * ‖md - xp‖ ^ 2 = L * (1 - a) ^ 2 / 2 * ‖ap - xp‖ ^ 2 := by rw [hmdn]; ring
  nlinarith [h1, e2, f1, f2, f3]

theorem stepB_path {n : ℕ} {Ψ : E n → ℝ} {g : E n → E n} {L : ℝ}
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (hcvx : ConvexOn ℝ Set.univ Ψ)
    (xs xp ap md d : E n) (a l b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hl : 0 < l)
    (hmd : md = (1 - a) • ap + a • xp) :
    Ψ (md - b • (g md + d)) ≤ (1 - a) * Ψ ap + a * Ψ xs
      + a / (2 * l) * (‖xp - xs‖ ^ 2 - ‖xp - l • (g md + d) - xs‖ ^ 2)
      - (b - (L * b ^ 2 + a * l) / 2) * ‖g md‖ ^ 2 + (L * b ^ 2 + a * l) / 2 * ‖d‖ ^ 2
      + ⟪(L * b ^ 2 + a * l - b) • g md - a • (xp - xs), d⟫ := by
  have h1 := ag_descent hΨ.2.1 hΨ.2.2 md (md - b • (g md + d))
  have c1 := ag_convex_fo hΨ.2.1 hcvx md ap
  have c2 := ag_convex_fo hΨ.2.1 hcvx md xs
  have e0 : (1 - a) • (ap - md) + a • (xs - md) = a • (xs - xp) := by rw [hmd]; module
  have cc : Ψ md - a * ⟪g md, xp - xs⟫ ≤ (1 - a) * Ψ ap + a * Ψ xs := by
    have := congrArg (fun v => ⟪g md, v⟫) e0
    simp only [inner_add_right, real_inner_smul_right] at this
    have e4 : ⟪g md, xs - xp⟫ = -⟪g md, xp - xs⟫ := by rw [← inner_neg_right, neg_sub]
    rw [e4] at this
    nlinarith [mul_le_mul_of_nonneg_left c1 (sub_nonneg.2 ha1), mul_le_mul_of_nonneg_left c2 ha0]
  have e1 : md - b • (g md + d) - md = -(b • (g md + d)) := by abel
  rw [e1, inner_neg_right, norm_neg, real_inner_smul_right, inner_add_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, norm_add_sq_real, real_inner_self_eq_norm_sq] at h1
  have e2 : ‖xp - l • (g md + d) - xs‖ ^ 2 = ‖xp - xs‖ ^ 2
      - 2 * l * (⟪g md, xp - xs⟫ + ⟪d, xp - xs⟫)
      + l ^ 2 * (‖g md‖ ^ 2 + 2 * ⟪g md, d⟫ + ‖d‖ ^ 2) := by
    have : xp - l • (g md + d) - xs = (xp - xs) - l • (g md + d) := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, inner_add_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, norm_add_sq_real, real_inner_comm (xp - xs) (g md),
      real_inner_comm (xp - xs) d]
    ring
  have e3 : ⟪(L * b ^ 2 + a * l - b) • g md - a • (xp - xs), d⟫ =
      (L * b ^ 2 + a * l - b) * ⟪g md, d⟫ - a * ⟪d, xp - xs⟫ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm d (xp - xs)]
  have e5 : a / (2 * l) * (‖xp - xs‖ ^ 2 - (‖xp - xs‖ ^ 2
      - 2 * l * (⟪g md, xp - xs⟫ + ⟪d, xp - xs⟫)
      + l ^ 2 * (‖g md‖ ^ 2 + 2 * ⟪g md, d⟫ + ‖d‖ ^ 2))) =
      a * (⟪g md, xp - xs⟫ + ⟪d, xp - xs⟫)
        - a * l / 2 * (‖g md‖ ^ 2 + 2 * ⟪g md, d⟫ + ‖d‖ ^ 2) := by
    field_simp; ring
  rw [e2, e3, e5]
  nlinarith [h1, cc]

/-! ## Integral bookkeeping -/

theorem int_lin5 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f1 f2 f3 f4 f5 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (c1 c2 c3 : ℝ) :
    ∫ ω, (f1 ω - c1 * f2 ω + c2 * f3 ω + c3 * f4 ω + f5 ω) ∂μ =
      ∫ ω, f1 ω ∂μ - c1 * ∫ ω, f2 ω ∂μ + c2 * ∫ ω, f3 ω ∂μ + c3 * ∫ ω, f4 ω ∂μ
        + ∫ ω, f5 ω ∂μ := by
  have i1 : Integrable (fun ω => f1 ω - c1 * f2 ω) μ := h1.sub (h2.const_mul c1)
  have i2 : Integrable (fun ω => f1 ω - c1 * f2 ω + c2 * f3 ω) μ := i1.add (h3.const_mul c2)
  have i3 : Integrable (fun ω => f1 ω - c1 * f2 ω + c2 * f3 ω + c3 * f4 ω) μ :=
    i2.add (h4.const_mul c3)
  rw [integral_add i3 h5, integral_add i2 (h4.const_mul c3), integral_add i1 (h3.const_mul c2),
    integral_sub h1 (h2.const_mul c1), integral_const_mul, integral_const_mul, integral_const_mul]

theorem int_lin4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f1 f2 f3 f5 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h5 : Integrable f5 μ) (c1 c2 : ℝ) :
    ∫ ω, (f1 ω - c1 * f2 ω + c2 * f3 ω + f5 ω) ∂μ =
      ∫ ω, f1 ω ∂μ - c1 * ∫ ω, f2 ω ∂μ + c2 * ∫ ω, f3 ω ∂μ + ∫ ω, f5 ω ∂μ := by
  have i1 : Integrable (fun ω => f1 ω - c1 * f2 ω) μ := h1.sub (h2.const_mul c1)
  have i2 : Integrable (fun ω => f1 ω - c1 * f2 ω + c2 * f3 ω) μ := i1.add (h3.const_mul c2)
  rw [integral_add i2 h5, integral_add i1 (h3.const_mul c2),
    integral_sub h1 (h2.const_mul c1), integral_const_mul, integral_const_mul]

theorem int_f1B {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f1 f2 f3 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (c1 c0 c2 : ℝ) :
    ∫ ω, (c1 * f1 ω + c0 + c2 * (f2 ω - f3 ω)) ∂μ =
      c1 * ∫ ω, f1 ω ∂μ + c0 + c2 * (∫ ω, f2 ω ∂μ - ∫ ω, f3 ω ∂μ) := by
  have i1 : Integrable (fun ω => c1 * f1 ω + c0) μ := (h1.const_mul c1).add (integrable_const c0)
  have i2 : Integrable (fun ω => f2 ω - f3 ω) μ := h2.sub h3
  rw [integral_add i1 (i2.const_mul c2), integral_add (h1.const_mul c1) (integrable_const c0),
    integral_const_mul, integral_const_mul, integral_sub h2 h3, integral_const]
  simp

/-! ## The RSAG run -/

open NonconvexAG.Stoch
open GhadimiLan.RSG (E)

section run
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)

theorem Gamma_zero : NonconvexAG.Smooth.Gamma α 0 = 1 := by
  unfold NonconvexAG.Smooth.Gamma; rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty]

theorem Gamma_one : NonconvexAG.Smooth.Gamma α 1 = 1 := by
  unfold NonconvexAG.Smooth.Gamma; rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty]

theorem Gamma_succ (k : ℕ) (hk : 1 ≤ k) :
    NonconvexAG.Smooth.Gamma α (k + 1) = NonconvexAG.Smooth.Gamma α k * (1 - α (k + 1)) := by
  unfold NonconvexAG.Smooth.Gamma; rw [Finset.prod_Icc_succ_top (by omega)]

variable {α β lam} in
theorem alpha_pos (h : RSAGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) : 0 < α k := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · have : k = 1 := by omega
    subst this; rw [h.1]; norm_num
  · exact (h.2.1 k h2).1

variable {α β lam} in
theorem alpha_le_one (h : RSAGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) : α k ≤ 1 := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · have : k = 1 := by omega
    subst this; rw [h.1]
  · exact (h.2.1 k h2).2.le

variable {α β lam} in
theorem Gamma_pos (h : RSAGStepsizes α β lam) (k : ℕ) : 0 < NonconvexAG.Smooth.Gamma α k :=
  Finset.prod_pos fun i hi => by
    have := (h.2.1 i (Finset.mem_Icc.1 hi).1).2
    linarith

/-! ## Real-sequence lemmas for part a) and part b) -/

variable {α β lam} in
set_option maxHeartbeats 1000000 in
theorem realA (h : RSAGStepsizes α β lam) {L σ : ℝ} (hL : 0 ≤ L)
    (P a s D : ℕ → ℝ) (ha : ∀ k, 1 ≤ k → 0 ≤ a k) (hs0 : ∀ k, 1 ≤ k → 0 ≤ s k)
    (hsσ : ∀ k, 1 ≤ k → s k ≤ σ ^ 2)
    (hstep : ∀ k, P (k + 1) ≤ P k - lam (k + 1) * (1 - L * lam (k + 1)) * a (k + 1)
      + L * (1 - α (k + 1)) ^ 2 / 2 * D k + L * lam (k + 1) ^ 2 / 2 * s (k + 1))
    (hD : ∀ k, D k ≤ NonconvexAG.Smooth.Gamma α k * ∑ τ ∈ Finset.Icc 1 k,
        (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) * (a τ + s τ)) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C L α β lam N k * a k ≤
      P 0 - P N + L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N,
        lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
          ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ) := by
  set c : ℕ → ℝ := fun τ => (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) with hc
  set T : ℕ → ℝ := fun k => ∑ τ ∈ Finset.Icc 1 k, c τ * (a τ + s τ) with hT
  set S : ℕ → ℝ := fun k => ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ with hS
  have hcnn : ∀ τ, 1 ≤ τ → 0 ≤ c τ := fun τ hτ =>
    div_nonneg (sq_nonneg _) (mul_pos (Gamma_pos h τ) (alpha_pos h τ hτ)).le
  have hTnn : ∀ k, 0 ≤ T k := fun k => Finset.sum_nonneg fun τ hτ => by
    have h1 := (Finset.mem_Icc.1 hτ).1
    exact mul_nonneg (hcnn τ h1) (add_nonneg (ha τ h1) (hs0 τ h1))
  have hTsucc : ∀ k, T (k + 1) = T k + c (k + 1) * (a (k + 1) + s (k + 1)) := fun k => by
    simp only [hT]; rw [Finset.sum_Icc_succ_top (by omega)]
  have hSnn : ∀ k, 0 ≤ S k := fun k =>
    Finset.sum_nonneg fun τ _ => (Gamma_pos h τ).le
  have hsum : ∀ M, P M ≤ P 0 - ∑ k ∈ Finset.Icc 1 M, lam k * (1 - L * lam k) * a k
      + L / 2 * ∑ k ∈ Finset.Icc 1 M, NonconvexAG.Smooth.Gamma α k * T k
      + L / 2 * ∑ k ∈ Finset.Icc 1 M, lam k ^ 2 * s k := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have hs := hstep M
      have hb : (1 - α (M + 1)) ^ 2 * D M ≤ NonconvexAG.Smooth.Gamma α (M + 1) * T (M + 1) := by
        rcases Nat.eq_zero_or_pos M with hM | hM
        · subst hM
          have h0 : D 0 ≤ 0 := by simpa using hD 0
          have h1 := mul_nonneg (Gamma_pos h (0 + 1)).le (hTnn (0 + 1))
          have h2 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (1 - α (0 + 1))) h0
          linarith
        · have hDM := hD M
          have ha0 := alpha_pos h (M + 1) (by omega)
          have ha1 := alpha_le_one h (M + 1) (by omega)
          have hTmono : T M ≤ T (M + 1) := by
            rw [hTsucc]
            have := mul_nonneg (hcnn (M + 1) (by omega))
              (add_nonneg (ha (M + 1) (by omega)) (hs0 (M + 1) (by omega)))
            linarith
          rw [Gamma_succ α M hM]
          have hΓ := Gamma_pos h M
          have hGS : 0 ≤ NonconvexAG.Smooth.Gamma α M * T M := mul_nonneg hΓ.le (hTnn M)
          calc (1 - α (M + 1)) ^ 2 * D M
              ≤ (1 - α (M + 1)) ^ 2 * (NonconvexAG.Smooth.Gamma α M * T M) :=
                mul_le_mul_of_nonneg_left hDM (sq_nonneg _)
            _ ≤ (1 - α (M + 1)) * (NonconvexAG.Smooth.Gamma α M * T M) :=
                mul_le_mul_of_nonneg_right (by nlinarith) hGS
            _ ≤ NonconvexAG.Smooth.Gamma α M * (1 - α (M + 1)) * T (M + 1) := by
                have := mul_le_mul_of_nonneg_left hTmono
                  (mul_nonneg hΓ.le (show (0:ℝ) ≤ 1 - α (M + 1) by linarith))
                linarith
      have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ L / 2)
      linarith
  have hswap : ∑ k ∈ Finset.Icc 1 N, NonconvexAG.Smooth.Gamma α k * T k =
      ∑ τ ∈ Finset.Icc 1 N, c τ * (a τ + s τ) * S τ := by
    simp only [hT, hS]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun τ => Finset.Icc τ N)]
    · exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => by ring
    · intro k τ; simp only [Finset.mem_Icc]; omega
  have hCk : ∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C L α β lam N k * a k =
      ∑ k ∈ Finset.Icc 1 N, lam k * (1 - L * lam k) * a k
        - L / 2 * ∑ k ∈ Finset.Icc 1 N, c k * a k * S k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 := (Finset.mem_Icc.1 hk).1
    have hl : lam k ≠ 0 := (h.2.2.2 k hk1).ne'
    have hα : α k ≠ 0 := (alpha_pos h k hk1).ne'
    have hΓ : NonconvexAG.Smooth.Gamma α k ≠ 0 := (Gamma_pos h k).ne'
    simp only [hc, hS, NonconvexAG.Smooth.C]
    field_simp
  have hsplit : ∑ τ ∈ Finset.Icc 1 N, c τ * (a τ + s τ) * S τ =
      ∑ τ ∈ Finset.Icc 1 N, c τ * a τ * S τ + ∑ τ ∈ Finset.Icc 1 N, c τ * s τ * S τ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  have hR : ∑ k ∈ Finset.Icc 1 N, c k * s k * S k + ∑ k ∈ Finset.Icc 1 N, lam k ^ 2 * s k ≤
      σ ^ 2 * ∑ k ∈ Finset.Icc 1 N,
        lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
          S k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 := (Finset.mem_Icc.1 hk).1
    have hl : lam k ≠ 0 := (h.2.2.2 k hk1).ne'
    have hα : α k ≠ 0 := (alpha_pos h k hk1).ne'
    have hΓ : NonconvexAG.Smooth.Gamma α k ≠ 0 := (Gamma_pos h k).ne'
    have e : lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
        S k) = lam k ^ 2 + c k * S k := by
      simp only [hc]
      field_simp
    rw [e]
    have hnn : 0 ≤ lam k ^ 2 + c k * S k :=
      add_nonneg (sq_nonneg _) (mul_nonneg (hcnn k hk1) (hSnn k))
    have := mul_le_mul_of_nonneg_left (hsσ k hk1) hnn
    nlinarith
  have hN := hsum N
  rw [hswap, hsplit] at hN
  rw [hCk]
  have := mul_le_mul_of_nonneg_left hR (by positivity : (0:ℝ) ≤ L / 2)
  have e2 : L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N,
        lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
          S k) = L / 2 * (σ ^ 2 * ∑ k ∈ Finset.Icc 1 N,
        lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
          S k)) := by ring
  rw [e2]
  linarith

variable {α β lam} in
set_option maxHeartbeats 1000000 in
theorem realB (h : RSAGStepsizes α β lam) {L σ : ℝ} (hL : 0 < L)
    (B e a s : ℕ → ℝ) (ps : ℝ) (ha : ∀ k, 1 ≤ k → 0 ≤ a k) (hs0 : ∀ k, 1 ≤ k → 0 ≤ s k)
    (hsσ : ∀ k, 1 ≤ k → s k ≤ σ ^ 2) (he : ∀ k, 0 ≤ e k)
    (hstep : ∀ k, B (k + 1) ≤ (1 - α (k + 1)) * B k + α (k + 1) * ps
      + α (k + 1) / (2 * lam (k + 1)) * (e k - e (k + 1))
      - (β (k + 1) - (L * β (k + 1) ^ 2 + α (k + 1) * lam (k + 1)) / 2) * a (k + 1)
      + (L * β (k + 1) ^ 2 + α (k + 1) * lam (k + 1)) / 2 * s (k + 1))
    (N : ℕ)
    (h210 : ∀ k ∈ Finset.Icc 2 N,
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤
        α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (h36 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ L * β k ^ 2 ∧ β k < 1 / L) :
    ∀ M, 1 ≤ M → M ≤ N →
      (B M - ps) / NonconvexAG.Smooth.Gamma α M
        + ∑ k ∈ Finset.Icc 1 M, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - L * β k) * a k
        + 1 / 2 * (α M / (lam M * NonconvexAG.Smooth.Gamma α M)) * e M
      ≤ (2 * lam 1)⁻¹ * e 0
        + L * σ ^ 2 * ∑ k ∈ Finset.Icc 1 M, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k ^ 2 := by
  -- simplified one-step bound
  have hst : ∀ k, k + 1 ≤ N → B (k + 1) - ps ≤ (1 - α (k + 1)) * (B k - ps)
      + α (k + 1) / (2 * lam (k + 1)) * (e k - e (k + 1))
      - β (k + 1) * (1 - L * β (k + 1)) * a (k + 1) + L * β (k + 1) ^ 2 * σ ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Icc.2 ⟨(by omega : 1 ≤ k + 1), hk⟩
    have h1 := (h36 (k + 1) hk').1
    have hα := alpha_pos h (k + 1) (by omega)
    have hl := h.2.2.2 (k + 1) (by omega)
    have hal : 0 ≤ α (k + 1) * lam (k + 1) := (mul_pos hα hl).le
    have hak := ha (k + 1) (by omega)
    have hsk := hs0 (k + 1) (by omega)
    have hsk' := hsσ (k + 1) (by omega)
    have q1 : (L * β (k + 1) ^ 2 + α (k + 1) * lam (k + 1)) / 2 * a (k + 1) ≤
        L * β (k + 1) ^ 2 * a (k + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hak
    have q2 : (L * β (k + 1) ^ 2 + α (k + 1) * lam (k + 1)) / 2 * s (k + 1) ≤
        L * β (k + 1) ^ 2 * s (k + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hsk
    have q3 : L * β (k + 1) ^ 2 * s (k + 1) ≤ L * β (k + 1) ^ 2 * σ ^ 2 :=
      mul_le_mul_of_nonneg_left hsk' (by positivity)
    have := hstep k
    nlinarith
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro hN1
    have hs := hst 0 hN1
    have hl1 := h.2.2.2 1 le_rfl
    simp only [zero_add, h.1, sub_self, zero_mul] at hs
    rw [Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton, Gamma_one, h.1]
    have e1 : 1 / (2 * lam 1) * (e 0 - e 1) =
        (2 * lam 1)⁻¹ * e 0 - 1 / 2 * (1 / (lam 1 * 1)) * e 1 := by
      field_simp
    rw [e1] at hs
    simp only [div_one, inv_one, one_mul] at hs ⊢
    linarith
  | succ M hM ih =>
    intro hMN
    have ih' := ih (by omega)
    have hk := Finset.mem_Icc.2 ⟨(by omega : 2 ≤ M + 1), hMN⟩
    have ha0 := alpha_pos h (M + 1) (by omega)
    have ha1 : α (M + 1) < 1 := (h.2.1 (M + 1) (by omega)).2
    have hl := h.2.2.2 (M + 1) (by omega)
    have hs := hst M hMN
    have hmono := h210 (M + 1) hk
    simp only [Nat.add_sub_cancel] at hmono
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    rw [Gamma_succ α M hM] at hmono ⊢
    have hΓ := Gamma_pos h M
    set Γ := NonconvexAG.Smooth.Gamma α M
    set a' := α (M + 1)
    set l := lam (M + 1)
    set b := β (M + 1)
    set q := a (M + 1)
    set eM := e M
    set eM1 := e (M + 1)
    set DA := B M - ps
    have hpos : 0 < Γ * (1 - a') := mul_pos hΓ (by linarith)
    have hdiv := div_le_div_of_nonneg_right hs hpos.le
    have hne1 : (1 - a') ≠ 0 := (sub_pos.2 ha1).ne'
    have heq : ((1 - a') * DA + a' / (2 * l) * (eM - eM1) - b * (1 - L * b) * q
        + L * b ^ 2 * σ ^ 2) / (Γ * (1 - a'))
        = DA / Γ + 1 / 2 * (a' / (l * (Γ * (1 - a')))) * eM
          - 1 / 2 * (a' / (l * (Γ * (1 - a')))) * eM1
          - (Γ * (1 - a'))⁻¹ * b * (1 - L * b) * q
          + L * σ ^ 2 * ((Γ * (1 - a'))⁻¹ * b ^ 2) := by
      field_simp
      ring
    rw [heq] at hdiv
    have hw := mul_le_mul_of_nonneg_right hmono (he M)
    rw [mul_add]
    linarith

variable {α β lam} in
/-- The Γ-weighted Jensen bound for `u_{k+1} = (1-α_{k+1}) u_k + (λ_{k+1}-β_{k+1}) v_{k+1}`. -/
theorem D_bound_gen (h : RSAGStepsizes α β lam) (u v : ℕ → E n) (hu0 : u 0 = 0)
    (hu : ∀ k, u (k + 1) = (1 - α (k + 1)) • u k + (lam (k + 1) - β (k + 1)) • v (k + 1))
    (k : ℕ) :
    ‖u k‖ ^ 2 ≤ NonconvexAG.Smooth.Gamma α k * ∑ τ ∈ Finset.Icc 1 k,
      (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) * ‖v τ‖ ^ 2 := by
  induction k with
  | zero => simp [hu0]
  | succ k ih =>
    rw [hu, Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [h.1, Gamma_one, hu0, norm_smul, mul_pow]
    · have ha0 := alpha_pos h (k + 1) (by omega)
      have ha1 : α (k + 1) < 1 := (h.2.1 (k + 1) (by omega)).2
      rw [Gamma_succ α k hk]
      have hΓ := Gamma_pos h k
      have hSk : 0 ≤ ∑ τ ∈ Finset.Icc 1 k,
          (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) * ‖v τ‖ ^ 2 :=
        Finset.sum_nonneg fun τ hτ => mul_nonneg (div_nonneg (sq_nonneg _)
          (mul_pos (Gamma_pos h τ) (alpha_pos h τ (Finset.mem_Icc.1 hτ).1)).le) (sq_nonneg _)
      set a := α (k + 1)
      set w := u k
      set V := v (k + 1)
      set c := lam (k + 1) - β (k + 1)
      set Γ := NonconvexAG.Smooth.Gamma α k
      set Sk := ∑ τ ∈ Finset.Icc 1 k,
          (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) * ‖v τ‖ ^ 2
      have hne1 : (1 - a) ≠ 0 := (sub_pos.2 ha1).ne'
      have hne2 : a ≠ 0 := ha0.ne'
      have hne3 : Γ ≠ 0 := hΓ.ne'
      have hexp : ‖(1 - a) • w + c • V‖ ^ 2 =
          (1 - a) ^ 2 * ‖w‖ ^ 2 + 2 * ((1 - a) * c) * ⟪w, V⟫ + c ^ 2 * ‖V‖ ^ 2 := by
        rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
          mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
        ring
      have h0 : 0 ≤ a ^ 2 * ‖w‖ ^ 2 - 2 * (a * c) * ⟪w, V⟫ + c ^ 2 * ‖V‖ ^ 2 := by
        have : ‖a • w - c • V‖ ^ 2 = a ^ 2 * ‖w‖ ^ 2 - 2 * (a * c) * ⟪w, V⟫ + c ^ 2 * ‖V‖ ^ 2 := by
          rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
            mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
          ring
        rw [← this]; positivity
      have hrhs : Γ * (1 - a) * (Sk + c ^ 2 / (Γ * (1 - a) * a) * ‖V‖ ^ 2) =
          (1 - a) * (Γ * Sk) + c ^ 2 * ‖V‖ ^ 2 / a := by
        field_simp
      rw [hexp, hrhs]
      have key : (1 - a) ^ 2 * ‖w‖ ^ 2 + 2 * ((1 - a) * c) * ⟪w, V⟫ + c ^ 2 * ‖V‖ ^ 2 ≤
          (1 - a) * ‖w‖ ^ 2 + c ^ 2 * ‖V‖ ^ 2 / a := by
        rw [← sub_nonneg]
        have : (1 - a) * ‖w‖ ^ 2 + c ^ 2 * ‖V‖ ^ 2 / a -
            ((1 - a) ^ 2 * ‖w‖ ^ 2 + 2 * ((1 - a) * c) * ⟪w, V⟫ + c ^ 2 * ‖V‖ ^ 2) =
            (1 - a) / a * (a ^ 2 * ‖w‖ ^ 2 - 2 * (a * c) * ⟪w, V⟫ + c ^ 2 * ‖V‖ ^ 2) := by
          field_simp
          ring
        rw [this]
        exact mul_nonneg (div_nonneg (by linarith) ha0.le) h0
      have := mul_le_mul_of_nonneg_left ih (show (0:ℝ) ≤ 1 - a by linarith)
      linarith

theorem path_meas_seq (hG : Measurable (Function.uncurry G)) (k : ℕ) :
    Measurable (fun s : ℕ → Ξ => rsagPath G α β lam x0 s k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hc : Continuous fun p : E n × E n => (1 - α (k + 1)) • p.2 + α (k + 1) • p.1 := by
      fun_prop
    have hT : Continuous fun q : (E n × E n) × E n =>
        (q.1.1 - lam (k + 1) • q.2,
          ((1 - α (k + 1)) • q.1.2 + α (k + 1) • q.1.1) - β (k + 1) • q.2) := by fun_prop
    have hmd := hc.measurable.comp ih
    have hGk : Measurable fun s : ℕ → Ξ => G ((1 - α (k + 1)) • (rsagPath G α β lam x0 s k).2
        + α (k + 1) • (rsagPath G α β lam x0 s k).1) (s (k + 1)) :=
      hG.comp (hmd.prodMk (measurable_pi_apply (k + 1)))
    exact hT.measurable.comp (ih.prodMk hGk)

theorem path_meas_adapted {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0)
    (ξ : ℕ → Ω → Ξ) (hG : Measurable (Function.uncurry G))
    (hξ : ∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k)) (k : ℕ) :
    Measurable[ℱ k] (fun ω => rsagPath G α β lam x0 (fun j => ξ j ω) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have ih' : Measurable[ℱ (k + 1)] (fun ω => rsagPath G α β lam x0 (fun j => ξ j ω) k) :=
      ih.mono (ℱ.mono (Nat.le_succ k)) le_rfl
    have hc : Continuous fun p : E n × E n => (1 - α (k + 1)) • p.2 + α (k + 1) • p.1 := by
      fun_prop
    have hT : Continuous fun q : (E n × E n) × E n =>
        (q.1.1 - lam (k + 1) • q.2,
          ((1 - α (k + 1)) • q.1.2 + α (k + 1) • q.1.1) - β (k + 1) • q.2) := by fun_prop
    have hmd := hc.measurable.comp ih'
    have hGk : Measurable[ℱ (k + 1)] fun ω =>
        G ((1 - α (k + 1)) • (rsagPath G α β lam x0 (fun j => ξ j ω) k).2
          + α (k + 1) • (rsagPath G α β lam x0 (fun j => ξ j ω) k).1) (ξ (k + 1) ω) :=
      hG.comp (hmd.prodMk (hξ (k + 1) (by omega)))
    exact hT.measurable.comp (ih'.prodMk hGk)

section prob
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ)

theorem X_meas (hG : Measurable (Function.uncurry G))
    (hξ : ∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k)) (k : ℕ) :
    StronglyMeasurable[ℱ k] (xSeq G α β lam x0 ξ k) :=
  (path_meas_adapted G α β lam x0 ℱ ξ hG hξ k).fst.stronglyMeasurable

theorem A_meas (hG : Measurable (Function.uncurry G))
    (hξ : ∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k)) (k : ℕ) :
    StronglyMeasurable[ℱ k] (xagSeq G α β lam x0 ξ k) :=
  (path_meas_adapted G α β lam x0 ℱ ξ hG hξ k).snd.stronglyMeasurable

theorem M_meas' (hG : Measurable (Function.uncurry G))
    (hξ : ∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k)) (k : ℕ) :
    Measurable[ℱ k] (xmdSeq G α β lam x0 ξ (k + 1)) := by
  have hc : Continuous fun p : E n × E n => (1 - α (k + 1)) • p.2 + α (k + 1) • p.1 := by
    fun_prop
  exact hc.measurable.comp (path_meas_adapted G α β lam x0 ℱ ξ hG hξ k)

theorem M_meas (hG : Measurable (Function.uncurry G))
    (hξ : ∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k)) (k : ℕ) :
    StronglyMeasurable[ℱ k] (xmdSeq G α β lam x0 ξ (k + 1)) :=
  (M_meas' G α β lam x0 ℱ ξ hG hξ k).stronglyMeasurable

variable {G α β lam x0 ℱ ξ}
variable {g : E n → E n} {L σ : ℝ}

theorem memLp_step (hL : 0 ≤ L) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (k : ℕ)
    (hX : MemLp (xSeq G α β lam x0 ξ k) 2 μ) (hA : MemLp (xagSeq G α β lam x0 ξ k) 2 μ) :
    MemLp (xmdSeq G α β lam x0 ξ (k + 1)) 2 μ ∧
    MemLp (fun ω => g (xmdSeq G α β lam x0 ξ (k + 1) ω)) 2 μ ∧
    MemLp (delta G g α β lam x0 ξ (k + 1)) 2 μ ∧
    MemLp (fun ω => G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω)) 2 μ := by
  have hM : MemLp (xmdSeq G α β lam x0 ξ (k + 1)) 2 μ :=
    (hA.const_smul (1 - α (k + 1))).add (hX.const_smul (α (k + 1)))
  have hgM := memLp_lip hL hg hM
  have hMm : Measurable (xmdSeq G α β lam x0 ξ (k + 1)) :=
    (M_meas' G α β lam x0 ℱ ξ hG hA1.adapted k).mono (ℱ.le k) le_rfl
  have hξm : Measurable (ξ (k + 1)) := (hA1.adapted (k + 1) (by omega)).mono (ℱ.le _) le_rfl
  have hGm : Measurable fun ω => G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω) :=
    hG.comp (hMm.prodMk hξm)
  have hδm : AEStronglyMeasurable (delta G g α β lam x0 ξ (k + 1)) μ :=
    hGm.aestronglyMeasurable.sub hgM.1
  have hδ : MemLp (delta G g α β lam x0 ξ (k + 1)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hδm).2 (hA1.integrable_sq_error (k + 1) (by omega))
  have hGk : MemLp (fun ω => G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω)) 2 μ := by
    have e : (fun ω => G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω)) =
        delta G g α β lam x0 ξ (k + 1) + fun ω => g (xmdSeq G α β lam x0 ξ (k + 1) ω) := by
      funext ω; simp [delta]
    rw [e]; exact hδ.add hgM
  exact ⟨hM, hgM, hδ, hGk⟩

theorem memLp_run (hL : 0 ≤ L) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (k : ℕ) :
    MemLp (xSeq G α β lam x0 ξ k) 2 μ ∧ MemLp (xagSeq G α β lam x0 ξ k) 2 μ := by
  induction k with
  | zero => exact ⟨memLp_const x0, memLp_const x0⟩
  | succ k ih =>
    obtain ⟨hM, -, -, hGk⟩ := memLp_step hL hg hG hA1 k ih.1 ih.2
    exact ⟨ih.1.sub (hGk.const_smul (lam (k + 1))), hM.sub (hGk.const_smul (β (k + 1)))⟩

theorem cross_zero (hL : 0 ≤ L) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (k : ℕ)
    {Y : Ω → E n} (hYm : StronglyMeasurable[ℱ k] Y) (hY : MemLp Y 2 μ) :
    ∫ ω, ⟪Y ω, delta G g α β lam x0 ξ (k + 1) ω⟫ ∂μ = 0 := by
  have hr := memLp_run hL hg hG hA1 k
  obtain ⟨-, hgM, -, hGk⟩ := memLp_step hL hg hG hA1 k hr.1 hr.2
  have e : (fun ω => ⟪Y ω, delta G g α β lam x0 ξ (k + 1) ω⟫) = fun ω =>
      ⟪Y ω, G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω)⟫ -
        ⟪Y ω, g (xmdSeq G α β lam x0 ξ (k + 1) ω)⟫ := by
    funext ω; simp only [delta, inner_sub_right]
  rw [e, integral_sub (int_inner hY hGk) (int_inner hY hgM)]
  have hu := hA1.unbiased (k + 1) (by omega)
  rw [Nat.add_sub_cancel] at hu
  rw [cross_eq (ℱ.le k) hYm.aestronglyMeasurable (int_inner hY hGk)
    (hGk.integrable one_le_two) hu, sub_self]

theorem int_Psi {Ψ : E n → ℝ} (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    {X : Ω → E n} (hX : MemLp X 2 μ) : Integrable (fun ω => Ψ (X ω)) μ := by
  have hcont : Continuous Ψ :=
    continuous_iff_continuousAt.2 fun x => (hΨ.2.1 x).differentiableAt.continuousAt
  have hb : Integrable (fun ω => (|Ψ 0| + ‖g 0‖) + (‖g 0‖ + 2 * L) * ‖X ω‖ ^ 2) μ :=
    (integrable_const _).add ((int_sq hX).const_mul _)
  refine hb.mono' (hcont.comp_aestronglyMeasurable hX.1) (ae_of_all _ fun ω => ?_)
  set y := X ω
  have hL := hΨ.1
  have hup := ag_descent hΨ.2.1 hΨ.2.2 0 y
  have hlo := ag_descent hΨ.2.1 hΨ.2.2 y 0
  simp only [sub_zero, zero_sub, norm_neg, inner_neg_right] at hup hlo
  have i1 := real_inner_le_norm (g 0) y
  have i2 : -⟪g y, y⟫ ≤ ‖g y‖ * ‖y‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have i3 : -⟪g 0, y⟫ ≤ ‖g 0‖ * ‖y‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hgy : ‖g y‖ ≤ ‖g 0‖ + L * ‖y‖ := by
    have h1 := hΨ.2.2 y 0
    rw [sub_zero] at h1
    have := norm_add_le (g 0) (g y - g 0)
    rw [add_sub_cancel] at this
    linarith
  have hy0 := norm_nonneg y
  have hg0 := norm_nonneg (g 0)
  have hyy : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have e1 : ‖g y‖ * ‖y‖ ≤ ‖g 0‖ * ‖y‖ + L * ‖y‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hgy hy0; nlinarith
  have e2 : ‖g 0‖ * ‖y‖ ≤ ‖g 0‖ + ‖g 0‖ * ‖y‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hyy hg0; nlinarith
  rw [Real.norm_eq_abs, abs_le]
  have ha := abs_nonneg (Ψ 0)
  have ha1 := le_abs_self (Ψ 0)
  have ha2 := neg_abs_le (Ψ 0)
  constructor <;> nlinarith

theorem g_cont (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) : Continuous g := by
  refine (LipschitzWith.of_dist_le' (K := L) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]; exact hg x y

set_option maxHeartbeats 1000000 in
theorem stepA_exp {Ψ : E n → ℝ} (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (k : ℕ) (hl : 0 ≤ lam (k + 1)) :
    ∫ ω, Ψ (xSeq G α β lam x0 ξ (k + 1) ω) ∂μ ≤ ∫ ω, Ψ (xSeq G α β lam x0 ξ k ω) ∂μ
      - lam (k + 1) * (1 - L * lam (k + 1)) *
          ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2 ∂μ
      + L * (1 - α (k + 1)) ^ 2 / 2 *
          ∫ ω, ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2 ∂μ
      + L * lam (k + 1) ^ 2 / 2 * ∫ ω, ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2 ∂μ := by
  have hr := memLp_run hΨ.1 hΨ.2.2 hG hA1 k
  have hr1 := memLp_run hΨ.1 hΨ.2.2 hG hA1 (k + 1)
  obtain ⟨-, hgM, hδ, -⟩ := memLp_step hΨ.1 hΨ.2.2 hG hA1 k hr.1 hr.2
  have hgX := memLp_lip hΨ.1 hΨ.2.2 hr.1
  have hgc := g_cont hΨ.2.2
  have hY : MemLp (fun ω => (L * lam (k + 1) ^ 2) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
      - lam (k + 1) • g (xSeq G α β lam x0 ξ k ω)) 2 μ :=
    (hgM.const_smul (L * lam (k + 1) ^ 2)).sub (hgX.const_smul (lam (k + 1)))
  have hYm : StronglyMeasurable[ℱ k] (fun ω =>
      (L * lam (k + 1) ^ 2) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
        - lam (k + 1) • g (xSeq G α β lam x0 ξ k ω)) :=
    ((hgc.comp_stronglyMeasurable (M_meas G α β lam x0 ℱ ξ hG hA1.adapted k)).const_smul
      (L * lam (k + 1) ^ 2)).sub
      ((hgc.comp_stronglyMeasurable (X_meas G α β lam x0 ℱ ξ hG hA1.adapted k)).const_smul
        (lam (k + 1)))
  have hz := cross_zero hΨ.1 hΨ.2.2 hG hA1 k hYm hY
  have h1 : Integrable (fun ω => Ψ (xSeq G α β lam x0 ξ k ω)) μ := int_Psi hΨ hr.1
  have h2 : Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2) μ := int_sq hgM
  have h3 : Integrable (fun ω => ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2) μ :=
    int_sq (hr.2.sub hr.1)
  have h4 : Integrable (fun ω => ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2) μ := int_sq hδ
  have h5 : Integrable (fun ω => ⟪(L * lam (k + 1) ^ 2) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
      - lam (k + 1) • g (xSeq G α β lam x0 ξ k ω), delta G g α β lam x0 ξ (k + 1) ω⟫) μ :=
    int_inner hY hδ
  have hpath : ∀ ω, Ψ (xSeq G α β lam x0 ξ (k + 1) ω) ≤ Ψ (xSeq G α β lam x0 ξ k ω)
      - lam (k + 1) * (1 - L * lam (k + 1)) * ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2
      + L * (1 - α (k + 1)) ^ 2 / 2 *
          ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2
      + L * lam (k + 1) ^ 2 / 2 * ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2
      + ⟪(L * lam (k + 1) ^ 2) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
          - lam (k + 1) • g (xSeq G α β lam x0 ξ k ω), delta G g α β lam x0 ξ (k + 1) ω⟫ := by
    intro ω
    have eX : xSeq G α β lam x0 ξ (k + 1) ω = xSeq G α β lam x0 ξ k ω - lam (k + 1) •
        (g (xmdSeq G α β lam x0 ξ (k + 1) ω) + delta G g α β lam x0 ξ (k + 1) ω) := by
      simp only [delta, add_sub_cancel]; rfl
    rw [eX]
    refine stepA_path hΨ _ (xagSeq G α β lam x0 ξ k ω) _ _ (α (k + 1)) (lam (k + 1)) hl ?_
    show (1 - α (k + 1)) • xagSeq G α β lam x0 ξ k ω + α (k + 1) • xSeq G α β lam x0 ξ k ω
      - xSeq G α β lam x0 ξ k ω = _
    module
  have hRint := ((((h1.sub (h2.const_mul (lam (k + 1) * (1 - L * lam (k + 1))))).add
    (h3.const_mul (L * (1 - α (k + 1)) ^ 2 / 2))).add (h4.const_mul (L * lam (k + 1) ^ 2 / 2))).add h5)
  calc ∫ ω, Ψ (xSeq G α β lam x0 ξ (k + 1) ω) ∂μ
      ≤ ∫ ω, (Ψ (xSeq G α β lam x0 ξ k ω)
      - lam (k + 1) * (1 - L * lam (k + 1)) * ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2
      + L * (1 - α (k + 1)) ^ 2 / 2 *
          ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2
      + L * lam (k + 1) ^ 2 / 2 * ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2
      + ⟪(L * lam (k + 1) ^ 2) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
          - lam (k + 1) • g (xSeq G α β lam x0 ξ k ω), delta G g α β lam x0 ξ (k + 1) ω⟫) ∂μ :=
        integral_mono (int_Psi hΨ hr1.1) hRint hpath
    _ = _ := int_lin5 h1 h2 h3 h4 h5 _ _ _
    _ = _ := by rw [hz, add_zero]

theorem Gsq_exp (hL : 0 ≤ L) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (k : ℕ) :
    ∫ ω, ‖G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω)‖ ^ 2 ∂μ =
      ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2 ∂μ
        + ∫ ω, ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2 ∂μ := by
  have hr := memLp_run hL hg hG hA1 k
  obtain ⟨-, hgM, hδ, -⟩ := memLp_step hL hg hG hA1 k hr.1 hr.2
  have hz := cross_zero hL hg hG hA1 k
    ((g_cont hg).comp_stronglyMeasurable (M_meas G α β lam x0 ℱ ξ hG hA1.adapted k)) hgM
  have h2 : Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2) μ := int_sq hgM
  have h4 : Integrable (fun ω => ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2) μ := int_sq hδ
  have h5 : Integrable (fun ω => ⟪g (xmdSeq G α β lam x0 ξ (k + 1) ω),
      delta G g α β lam x0 ξ (k + 1) ω⟫) μ := int_inner hgM hδ
  have i1 : Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2
      + 2 * ⟪g (xmdSeq G α β lam x0 ξ (k + 1) ω), delta G g α β lam x0 ξ (k + 1) ω⟫) μ :=
    h2.add (h5.const_mul 2)
  calc ∫ ω, ‖G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω)‖ ^ 2 ∂μ
      = ∫ ω, (‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2
      + 2 * ⟪g (xmdSeq G α β lam x0 ξ (k + 1) ω), delta G g α β lam x0 ξ (k + 1) ω⟫
      + ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        have e : G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω) =
            g (xmdSeq G α β lam x0 ξ (k + 1) ω) + delta G g α β lam x0 ξ (k + 1) ω := by
          simp [delta]
        simp only [e, norm_add_sq_real]
    _ = _ := by
        rw [integral_add i1 h4, integral_add h2 (h5.const_mul 2), integral_const_mul, hz]
        ring

theorem D_exp (hstep : RSAGStepsizes α β lam) (hL : 0 ≤ L)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (k : ℕ) :
    ∫ ω, ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2 ∂μ ≤
      NonconvexAG.Smooth.Gamma α k * ∑ τ ∈ Finset.Icc 1 k,
        (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) *
          (∫ ω, ‖g (xmdSeq G α β lam x0 ξ τ ω)‖ ^ 2 ∂μ
            + ∫ ω, ‖delta G g α β lam x0 ξ τ ω‖ ^ 2 ∂μ) := by
  have hr := memLp_run hL hg hG hA1 k
  have hpath : ∀ ω, ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2 ≤
      NonconvexAG.Smooth.Gamma α k * ∑ τ ∈ Finset.Icc 1 k,
        (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) *
          ‖G (xmdSeq G α β lam x0 ξ τ ω) (ξ τ ω)‖ ^ 2 := by
    intro ω
    refine D_bound_gen hstep (fun j => xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω)
      (fun j => G (xmdSeq G α β lam x0 ξ j ω) (ξ j ω)) (sub_self x0) (fun j => ?_) k
    have hx : xSeq G α β lam x0 ξ (j + 1) ω = xSeq G α β lam x0 ξ j ω
        - lam (j + 1) • G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) := rfl
    have ha : xagSeq G α β lam x0 ξ (j + 1) ω = xmdSeq G α β lam x0 ξ (j + 1) ω
        - β (j + 1) • G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) := rfl
    have hm : xmdSeq G α β lam x0 ξ (j + 1) ω = (1 - α (j + 1)) • xagSeq G α β lam x0 ξ j ω
        + α (j + 1) • xSeq G α β lam x0 ξ j ω := rfl
    show xagSeq G α β lam x0 ξ (j + 1) ω - xSeq G α β lam x0 ξ (j + 1) ω = _
    rw [hx, ha]
    generalize G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) = Gv
    rw [hm]
    module
  have hGint : ∀ τ ∈ Finset.Icc 1 k, Integrable (fun ω =>
      (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) *
        ‖G (xmdSeq G α β lam x0 ξ τ ω) (ξ τ ω)‖ ^ 2) μ := by
    intro τ hτ
    obtain ⟨j, rfl⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by have := (Finset.mem_Icc.1 hτ).1; omega⟩
    have hrj := memLp_run hL hg hG hA1 j
    exact (int_sq (memLp_step hL hg hG hA1 j hrj.1 hrj.2).2.2.2).const_mul _
  calc ∫ ω, ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2 ∂μ
      ≤ ∫ ω, NonconvexAG.Smooth.Gamma α k * ∑ τ ∈ Finset.Icc 1 k,
        (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) *
          ‖G (xmdSeq G α β lam x0 ξ τ ω) (ξ τ ω)‖ ^ 2 ∂μ :=
        integral_mono (int_sq (hr.2.sub hr.1))
          ((integrable_finset_sum _ hGint).const_mul _) hpath
    _ = _ := by
        rw [integral_const_mul, integral_finset_sum _ hGint]
        congr 1
        refine Finset.sum_congr rfl fun τ hτ => ?_
        obtain ⟨j, rfl⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by have := (Finset.mem_Icc.1 hτ).1; omega⟩
        rw [integral_const_mul, Gsq_exp hL hg hG hA1 j]

set_option maxHeartbeats 1000000 in
theorem stepB_exp {Ψ : E n → ℝ} (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    (hcvx : ConvexOn ℝ Set.univ Ψ) (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (xs : E n)
    (k : ℕ) (ha0 : 0 ≤ α (k + 1)) (ha1 : α (k + 1) ≤ 1) (hl : 0 < lam (k + 1)) :
    ∫ ω, Ψ (xagSeq G α β lam x0 ξ (k + 1) ω) ∂μ ≤
      (1 - α (k + 1)) * ∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ + α (k + 1) * Ψ xs
      + α (k + 1) / (2 * lam (k + 1)) * (∫ ω, ‖xSeq G α β lam x0 ξ k ω - xs‖ ^ 2 ∂μ
          - ∫ ω, ‖xSeq G α β lam x0 ξ (k + 1) ω - xs‖ ^ 2 ∂μ)
      - (β (k + 1) - (L * β (k + 1) ^ 2 + α (k + 1) * lam (k + 1)) / 2) *
          ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2 ∂μ
      + (L * β (k + 1) ^ 2 + α (k + 1) * lam (k + 1)) / 2 *
          ∫ ω, ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2 ∂μ := by
  have hr := memLp_run hΨ.1 hΨ.2.2 hG hA1 k
  have hr1 := memLp_run hΨ.1 hΨ.2.2 hG hA1 (k + 1)
  obtain ⟨-, hgM, hδ, -⟩ := memLp_step hΨ.1 hΨ.2.2 hG hA1 k hr.1 hr.2
  have hgc := g_cont hΨ.2.2
  set a := α (k + 1)
  set l := lam (k + 1)
  set b := β (k + 1)
  have hXs : MemLp (fun ω => xSeq G α β lam x0 ξ k ω - xs) 2 μ := hr.1.sub (memLp_const xs)
  have hXs1 : MemLp (fun ω => xSeq G α β lam x0 ξ (k + 1) ω - xs) 2 μ := hr1.1.sub (memLp_const xs)
  have hY : MemLp (fun ω => (L * b ^ 2 + a * l - b) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
      - a • (xSeq G α β lam x0 ξ k ω - xs)) 2 μ :=
    (hgM.const_smul (L * b ^ 2 + a * l - b)).sub (hXs.const_smul a)
  have hYm : StronglyMeasurable[ℱ k] (fun ω =>
      (L * b ^ 2 + a * l - b) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
        - a • (xSeq G α β lam x0 ξ k ω - xs)) :=
    ((hgc.comp_stronglyMeasurable (M_meas G α β lam x0 ℱ ξ hG hA1.adapted k)).const_smul
      (L * b ^ 2 + a * l - b)).sub
      (((X_meas G α β lam x0 ℱ ξ hG hA1.adapted k).sub stronglyMeasurable_const).const_smul a)
  have hz := cross_zero hΨ.1 hΨ.2.2 hG hA1 k hYm hY
  have g1 : Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ k ω)) μ := int_Psi hΨ hr.2
  have g2 : Integrable (fun ω => ‖xSeq G α β lam x0 ξ k ω - xs‖ ^ 2) μ := int_sq hXs
  have g3 : Integrable (fun ω => ‖xSeq G α β lam x0 ξ (k + 1) ω - xs‖ ^ 2) μ := int_sq hXs1
  have h1 : Integrable (fun ω => (1 - a) * Ψ (xagSeq G α β lam x0 ξ k ω) + a * Ψ xs
      + a / (2 * l) * (‖xSeq G α β lam x0 ξ k ω - xs‖ ^ 2
        - ‖xSeq G α β lam x0 ξ (k + 1) ω - xs‖ ^ 2)) μ :=
    ((g1.const_mul _).add (integrable_const _)).add ((g2.sub g3).const_mul _)
  have h2 : Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2) μ := int_sq hgM
  have h3 : Integrable (fun ω => ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2) μ := int_sq hδ
  have h5 : Integrable (fun ω => ⟪(L * b ^ 2 + a * l - b) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
      - a • (xSeq G α β lam x0 ξ k ω - xs), delta G g α β lam x0 ξ (k + 1) ω⟫) μ :=
    int_inner hY hδ
  have hpath : ∀ ω, Ψ (xagSeq G α β lam x0 ξ (k + 1) ω) ≤
      ((1 - a) * Ψ (xagSeq G α β lam x0 ξ k ω) + a * Ψ xs
      + a / (2 * l) * (‖xSeq G α β lam x0 ξ k ω - xs‖ ^ 2
        - ‖xSeq G α β lam x0 ξ (k + 1) ω - xs‖ ^ 2))
      - (b - (L * b ^ 2 + a * l) / 2) * ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2
      + (L * b ^ 2 + a * l) / 2 * ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2
      + ⟪(L * b ^ 2 + a * l - b) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
          - a • (xSeq G α β lam x0 ξ k ω - xs), delta G g α β lam x0 ξ (k + 1) ω⟫ := by
    intro ω
    have eX : xSeq G α β lam x0 ξ (k + 1) ω = xSeq G α β lam x0 ξ k ω - l •
        (g (xmdSeq G α β lam x0 ξ (k + 1) ω) + delta G g α β lam x0 ξ (k + 1) ω) := by
      simp only [delta, add_sub_cancel, l]; rfl
    have eA : xagSeq G α β lam x0 ξ (k + 1) ω = xmdSeq G α β lam x0 ξ (k + 1) ω - b •
        (g (xmdSeq G α β lam x0 ξ (k + 1) ω) + delta G g α β lam x0 ξ (k + 1) ω) := by
      simp only [delta, add_sub_cancel, b]; rfl
    have := stepB_path hΨ hcvx xs (xSeq G α β lam x0 ξ k ω) (xagSeq G α β lam x0 ξ k ω)
      (xmdSeq G α β lam x0 ξ (k + 1) ω) (delta G g α β lam x0 ξ (k + 1) ω) a l b ha0 ha1 hl rfl
    rw [← eX, ← eA] at this
    exact this
  calc ∫ ω, Ψ (xagSeq G α β lam x0 ξ (k + 1) ω) ∂μ
      ≤ ∫ ω, (((1 - a) * Ψ (xagSeq G α β lam x0 ξ k ω) + a * Ψ xs
      + a / (2 * l) * (‖xSeq G α β lam x0 ξ k ω - xs‖ ^ 2
        - ‖xSeq G α β lam x0 ξ (k + 1) ω - xs‖ ^ 2))
      - (b - (L * b ^ 2 + a * l) / 2) * ‖g (xmdSeq G α β lam x0 ξ (k + 1) ω)‖ ^ 2
      + (L * b ^ 2 + a * l) / 2 * ‖delta G g α β lam x0 ξ (k + 1) ω‖ ^ 2
      + ⟪(L * b ^ 2 + a * l - b) • g (xmdSeq G α β lam x0 ξ (k + 1) ω)
          - a • (xSeq G α β lam x0 ξ k ω - xs), delta G g α β lam x0 ξ (k + 1) ω⟫) ∂μ :=
        integral_mono (int_Psi hΨ hr1.2)
          (((h1.sub (h2.const_mul _)).add (h3.const_mul _)).add h5) hpath
    _ = _ := int_lin4 h1 h2 h3 h5 _ _
    _ = _ := by rw [hz, add_zero, int_f1B g1 g2 g3]

theorem gM_memLp (hL : 0 ≤ L) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry G))
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ) (k : ℕ) (hk : 1 ≤ k) :
    MemLp (fun ω => g (xmdSeq G α β lam x0 ξ k ω)) 2 μ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hr := memLp_run hL hg hG hA1 j
  exact (memLp_step hL hg hG hA1 j hr.1 hr.2).2.1

end prob
end run

end RSAG8be

set_option maxHeartbeats 1000000 in
open MeasureTheory ProbabilityTheory NonconvexAG.Stoch GhadimiLan.RSG in
theorem solution {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (N : ℕ) (hN : 1 ≤ N) :
    (BddBelow (Set.range Ψ) → (∀ k ∈ Finset.Icc 1 N, 0 < NonconvexAG.Smooth.C LΨ α β lam N k) →
      ∀ R : Ω → ℕ, IsOutputIndex μ R N (pmfA LΨ α β lam N) →
        IndepFun R (fun ω k => ξ k ω) μ →
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
      ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k) *
          (Ψ x0 - (⨅ x, Ψ x) + LΨ * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N,
            lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
              ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ))) ∧
    (∀ xstar : E n, ConvexOn ℝ Set.univ Ψ → (∀ x, Ψ xstar ≤ Ψ x) →
      (∀ k ∈ Finset.Icc 2 N,
        α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) →
      (∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ LΨ * β k ^ 2 ∧ β k < 1 / LΨ) →
      ∀ R : Ω → ℕ, IsOutputIndex μ R N (pmfB LΨ α β N) →
        IndepFun R (fun ω k => ξ k ω) μ →
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
      ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ ≤
        ((2 * lam 1)⁻¹ * ‖x0 - xstar‖ ^ 2
            + LΨ * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k ^ 2) /
          ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) ∧
      Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ xstar) μ ∧
      ∫ ω, (Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ xstar) ∂μ ≤
        (∑ k ∈ Finset.Icc 1 N, β k * (1 - LΨ * β k) *
            ((2 * lam 1)⁻¹ * ‖x0 - xstar‖ ^ 2
              + LΨ * σ ^ 2 * ∑ j ∈ Finset.Icc 1 k, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j ^ 2)) /
          ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) := by
  have hL0 : 0 ≤ LΨ := hL.le
  have hg := hΨ.2.2
  have hgc := RSAG8be.g_cont hg
  have hΨc : Continuous Ψ :=
    continuous_iff_continuousAt.2 fun x => (hΨ.2.1 x).differentiableAt.continuousAt
  have hFm : ∀ k, Measurable (fun s : ℕ → Ξ =>
      ‖g ((1 - α k) • (rsagPath G α β lam x0 s (k - 1)).2
        + α k • (rsagPath G α β lam x0 s (k - 1)).1)‖ ^ 2) := fun k => by
    have hc : Continuous fun p : E n × E n => ‖g ((1 - α k) • p.2 + α k • p.1)‖ ^ 2 := by
      fun_prop
    exact hc.measurable.comp (RSAG8be.path_meas_seq G α β lam x0 hG (k - 1))
  have hgM : ∀ k, 1 ≤ k → MemLp (fun ω => g (xmdSeq G α β lam x0 ξ k ω)) 2 μ :=
    fun k hk => RSAG8be.gM_memLp hL0 hg hG hA1 k hk
  have hintA : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω =>
      (fun k (s : ℕ → Ξ) => ‖g ((1 - α k) • (rsagPath G α β lam x0 s (k - 1)).2
        + α k • (rsagPath G α β lam x0 s (k - 1)).1)‖ ^ 2) k (fun j => ξ j ω)) μ :=
    fun k hk => RSAG8be.int_sq (hgM k (Finset.mem_Icc.1 hk).1)
  have ha0 : ∀ k, 1 ≤ k → 0 ≤ ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ :=
    fun k _ => integral_nonneg fun ω => by positivity
  have hs0 : ∀ k, 1 ≤ k → 0 ≤ ∫ ω, ‖delta G g α β lam x0 ξ k ω‖ ^ 2 ∂μ :=
    fun k _ => integral_nonneg fun ω => by positivity
  have hsσ : ∀ k, 1 ≤ k → ∫ ω, ‖delta G g α β lam x0 ξ k ω‖ ^ 2 ∂μ ≤ σ ^ 2 :=
    fun k hk => hA1.variance_bound k hk
  have hav := fun (R : Ω → ℕ) (hR : Measurable R) (hRind : IndepFun R (fun ω k => ξ k ω) μ)
      (hRN : ∀ ω, R ω ∈ Finset.Icc 1 N) =>
    RSAG8be.avg_R (fun ω k => ξ k ω) R hR hRind N hRN
      (fun k (s : ℕ → Ξ) => ‖g ((1 - α k) • (rsagPath G α β lam x0 s (k - 1)).2
        + α k • (rsagPath G α β lam x0 s (k - 1)).1)‖ ^ 2) hFm hintA
  refine ⟨fun hbdd hC R hR hRind => ?_, fun xstar hcvx hmin h210 h36 R hR hRind => ?_⟩
  · have hav1 := hav R hR.1 hRind (hR.2.1)
    refine ⟨hav1.1, ?_⟩
    have e1 : ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ =
        ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} *
          ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ := hav1.2
    have hSpos : 0 < ∑ j ∈ Finset.Icc 1 N, lam j * NonconvexAG.Smooth.C LΨ α β lam N j :=
      Finset.sum_pos (fun j hj => mul_pos (hstep.2.2.2 j (Finset.mem_Icc.1 hj).1) (hC j hj))
        (Finset.nonempty_Icc.2 hN)
    have hpm : ∀ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} =
        lam k * NonconvexAG.Smooth.C LΨ α β lam N k /
          ∑ j ∈ Finset.Icc 1 N, lam j * NonconvexAG.Smooth.C LΨ α β lam N j := by
      intro k hk
      have hnn : 0 ≤ pmfA LΨ α β lam N k :=
        div_nonneg (mul_pos (hstep.2.2.2 k (Finset.mem_Icc.1 hk).1) (hC k hk)).le hSpos.le
      rw [show μ.real {ω | R ω = k} = (μ {ω | R ω = k}).toReal from rfl, hR.2.2 k hk,
        ENNReal.toReal_ofReal hnn]
      rfl
    have e2 : ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} *
          ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ =
        1 / (∑ j ∈ Finset.Icc 1 N, lam j * NonconvexAG.Smooth.C LΨ α β lam N j) *
          ∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k *
            ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk => by rw [hpm k hk]; ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hA := RSAG8be.realA hstep hL0 (fun k => ∫ ω, Ψ (xSeq G α β lam x0 ξ k ω) ∂μ)
      (fun k => ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ)
      (fun k => ∫ ω, ‖delta G g α β lam x0 ξ k ω‖ ^ 2 ∂μ)
      (fun k => ∫ ω, ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2 ∂μ)
      ha0 hs0 hsσ
      (fun k => RSAG8be.stepA_exp hΨ hG hA1 k (hstep.2.2.2 (k + 1) (by omega)).le)
      (fun k => RSAG8be.D_exp hstep hL0 hg hG hA1 k) N
    beta_reduce at hA
    have hP0 : ∫ ω, Ψ (xSeq G α β lam x0 ξ 0 ω) ∂μ = Ψ x0 := by simp [xSeq, rsagPath]
    have hPN : (⨅ x, Ψ x) ≤ ∫ ω, Ψ (xSeq G α β lam x0 ξ N ω) ∂μ := by
      have := integral_mono (integrable_const (⨅ x, Ψ x))
        (RSAG8be.int_Psi hΨ (RSAG8be.memLp_run hL0 hg hG hA1 N).1) (fun ω => ciInf_le hbdd _)
      simpa using this
    rw [hP0] at hA
    exact hA.trans (add_le_add (sub_le_sub_left hPN _) le_rfl)
  · have hwpos : ∀ k ∈ Finset.Icc 1 N,
        0 < (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) := by
      intro k hk
      have hb := hstep.2.2.1 k (Finset.mem_Icc.1 hk).1
      have h1 : LΨ * β k < 1 := by
        have := (h36 k hk).2
        rw [lt_div_iff₀ hL] at this
        linarith
      have := RSAG8be.Gamma_pos hstep k
      have : 0 < 1 - LΨ * β k := by linarith
      positivity
    have hWpos : 0 < ∑ k ∈ Finset.Icc 1 N,
        (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) :=
      Finset.sum_pos hwpos (Finset.nonempty_Icc.2 hN)
    have hpm : ∀ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} =
        (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) /
          ∑ j ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j) := by
      intro k hk
      have hnn : 0 ≤ pmfB LΨ α β N k := div_nonneg (hwpos k hk).le hWpos.le
      rw [show μ.real {ω | R ω = k} = (μ {ω | R ω = k}).toReal from rfl, hR.2.2 k hk,
        ENNReal.toReal_ofReal hnn]
      rfl
    have hinv := RSAG8be.realB hstep hL
      (fun k => ∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ)
      (fun k => ∫ ω, ‖xSeq G α β lam x0 ξ k ω - xstar‖ ^ 2 ∂μ)
      (fun k => ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ)
      (fun k => ∫ ω, ‖delta G g α β lam x0 ξ k ω‖ ^ 2 ∂μ) (Ψ xstar)
      ha0 hs0 hsσ (fun k => integral_nonneg fun ω => by positivity)
      (fun k => RSAG8be.stepB_exp hΨ hcvx hG hA1 xstar k
        (RSAG8be.alpha_pos hstep (k + 1) (by omega)).le
        (RSAG8be.alpha_le_one hstep (k + 1) (by omega)) (hstep.2.2.2 (k + 1) (by omega)))
      N h210 h36
    beta_reduce at hinv
    have he0 : ∫ ω, ‖xSeq G α β lam x0 ξ 0 ω - xstar‖ ^ 2 ∂μ = ‖x0 - xstar‖ ^ 2 := by
      simp [xSeq, rsagPath]
    rw [he0] at hinv
    have hBnn : ∀ k, Ψ xstar ≤ ∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ := fun k => by
      have := integral_mono (integrable_const (Ψ xstar))
        (RSAG8be.int_Psi hΨ (RSAG8be.memLp_run hL0 hg hG hA1 k).2) (fun ω => hmin _)
      simpa using this
    have hkey : ∀ k ∈ Finset.Icc 1 N,
        (∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ - Ψ xstar) / NonconvexAG.Smooth.Gamma α k
          + ∑ j ∈ Finset.Icc 1 k, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j) *
              ∫ ω, ‖g (xmdSeq G α β lam x0 ξ j ω)‖ ^ 2 ∂μ
        ≤ (2 * lam 1)⁻¹ * ‖x0 - xstar‖ ^ 2
            + LΨ * σ ^ 2 * ∑ j ∈ Finset.Icc 1 k, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j ^ 2 := by
      intro k hk
      have hk1 := Finset.mem_Icc.1 hk
      have h1 := hinv k hk1.1 hk1.2
      have ha := RSAG8be.alpha_pos hstep k hk1.1
      have hl := hstep.2.2.2 k hk1.1
      have hΓ := RSAG8be.Gamma_pos hstep k
      have hi : 0 ≤ ∫ ω, ‖xSeq G α β lam x0 ξ k ω - xstar‖ ^ 2 ∂μ :=
        integral_nonneg fun ω => sq_nonneg _
      have hT : 0 ≤ 1 / 2 * (α k / (lam k * NonconvexAG.Smooth.Gamma α k)) *
          ∫ ω, ‖xSeq G α β lam x0 ξ k ω - xstar‖ ^ 2 ∂μ :=
        mul_nonneg (mul_nonneg (by norm_num) (div_nonneg ha.le (mul_pos hl hΓ).le)) hi
      exact (le_add_of_nonneg_right hT).trans h1
    have hav1 := hav R hR.1 hRind (hR.2.1)
    have hF2m : ∀ k, Measurable (fun s : ℕ → Ξ =>
        Ψ (rsagPath G α β lam x0 s k).2 - Ψ xstar) := fun k =>
      (hΨc.measurable.comp (measurable_snd.comp
        (RSAG8be.path_meas_seq G α β lam x0 hG k))).sub_const _
    have hint2 : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω =>
        (fun k (s : ℕ → Ξ) => Ψ (rsagPath G α β lam x0 s k).2 - Ψ xstar) k
          (fun j => ξ j ω)) μ :=
      fun k _ => (RSAG8be.int_Psi hΨ (RSAG8be.memLp_run hL0 hg hG hA1 k).2).sub
        (integrable_const (Ψ xstar))
    have hav2 := RSAG8be.avg_R (fun ω k => ξ k ω) R hR.1 hRind N hR.2.1
      (fun k (s : ℕ → Ξ) => Ψ (rsagPath G α β lam x0 s k).2 - Ψ xstar) hF2m hint2
    refine ⟨hav1.1, ?_, hav2.1, ?_⟩
    · have e1 : ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ =
          ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} *
            ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ := hav1.2
      have e2 : ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} *
            ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ =
          (∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) *
            ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ) /
          ∑ j ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k hk => by rw [hpm k hk]; ring
      rw [e1, e2]
      refine div_le_div_of_nonneg_right ?_ hWpos.le
      have h1 := hkey N (Finset.mem_Icc.2 ⟨hN, le_rfl⟩)
      have : 0 ≤ (∫ ω, Ψ (xagSeq G α β lam x0 ξ N ω) ∂μ - Ψ xstar) /
          NonconvexAG.Smooth.Gamma α N :=
        div_nonneg (sub_nonneg.2 (hBnn N)) (RSAG8be.Gamma_pos hstep N).le
      exact (le_add_of_nonneg_left this).trans h1
    · have e1 : ∫ ω, (Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ xstar) ∂μ =
          ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} *
            ∫ ω, (Ψ (xagSeq G α β lam x0 ξ k ω) - Ψ xstar) ∂μ := hav2.2
      rw [e1, Finset.sum_div]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := Finset.mem_Icc.1 hk
      have hI : ∫ ω, (Ψ (xagSeq G α β lam x0 ξ k ω) - Ψ xstar) ∂μ =
          ∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ - Ψ xstar := by
        rw [integral_sub (RSAG8be.int_Psi hΨ (RSAG8be.memLp_run hL0 hg hG hA1 k).2)
          (integrable_const _)]
        simp
      rw [hpm k hk, hI]
      have h1 := hkey k hk
      have hsumnn : 0 ≤ ∑ j ∈ Finset.Icc 1 k,
          (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j) *
            ∫ ω, ‖g (xmdSeq G α β lam x0 ξ j ω)‖ ^ 2 ∂μ :=
        Finset.sum_nonneg fun j hj => by
          have hj1 := Finset.mem_Icc.1 hj
          exact mul_nonneg (hwpos j (Finset.mem_Icc.2 ⟨hj1.1, hj1.2.trans hk1.2⟩)).le
            (ha0 j hj1.1)
      have h2 : (∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ - Ψ xstar) /
          NonconvexAG.Smooth.Gamma α k ≤ (2 * lam 1)⁻¹ * ‖x0 - xstar‖ ^ 2
            + LΨ * σ ^ 2 * ∑ j ∈ Finset.Icc 1 k, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j ^ 2 :=
        (le_add_of_nonneg_right hsumnn).trans h1
      have hc : 0 ≤ β k * (1 - LΨ * β k) := by
        have hw := hwpos k hk
        have hΓ := RSAG8be.Gamma_pos hstep k
        have e : β k * (1 - LΨ * β k) = NonconvexAG.Smooth.Gamma α k *
            ((NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) := by
          field_simp
        rw [e]; positivity
      have h3 := mul_le_mul_of_nonneg_left h2 hc
      have e : (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) /
            (∑ j ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j)) *
            (∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ - Ψ xstar) =
          β k * (1 - LΨ * β k) * ((∫ ω, Ψ (xagSeq G α β lam x0 ξ k ω) ∂μ - Ψ xstar) /
            NonconvexAG.Smooth.Gamma α k) /
          (∑ j ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j)) := by
        ring
      rw [e]
      exact div_le_div_of_nonneg_right h3 hWpos.le
