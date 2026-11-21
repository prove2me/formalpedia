-- Prove2me | solution 1 for MasulloAudit.unhalved_chapter13_rational_trace_fails
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:53:50.469782+00:00
-- url     : https://prove2.me/submissions/e8585e32-b208-4754-851f-068c6a659c9a

import Mathlib
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_MasulloAudit_Chapter13Scalar
import Theorems.Thm_MasulloRH_weighted_positive_zeta_zeros_schwartz_scaling
import Theorems.Thm_MasulloRH_padic_unit_connes_principal_value_zero

/-!
# Real-place finite part in logarithmic norm coordinates

For the positive real branch in Masullo (13.3.1.4), the kernel in
`x = log |g|` has singular term `1 / |x|`. With the symmetric log cutoff
`|x| > δ`, the counterterm for the pole is `2 h(0) log δ`.
Rescaling the test by `x ↦ x / ε` changes the finite part by
`2 h(0) log ε`. The absolute factor of two comes from the two sides
of the singularity in the positive real branch.
-/

open Filter MeasureTheory Set
open scoped Interval Topology

namespace MasulloAudit

private def outside (δ : ℝ) : Set ℝ := {x | δ < |x|}

private lemma measurableSet_outside (δ : ℝ) : MeasurableSet (outside δ) :=
  isOpen_lt continuous_const continuous_abs |>.measurableSet

/-- Symmetric cutoff of the real pole together with its finite-part counterterm. -/
noncomputable def cutoffRealPole (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in outside δ, h x / |x|) + 2 * h 0 * Real.log δ

/-- Exact scale identity at every positive cutoff. -/
theorem cutoffRealPole_scale (h : ℝ → ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    cutoffRealPole (fun x ↦ h (x / ε)) δ =
      cutoffRealPole h (δ / ε) + 2 * h 0 * Real.log ε := by
  have hcut : (∫ x in outside δ, h (x / ε) / |x|) = ∫ y in outside (δ / ε), h y / |y| := by
    rw [← integral_indicator (measurableSet_outside δ),
      ← integral_indicator (measurableSet_outside (δ / ε))]
    have hfun : (outside δ).indicator (fun x ↦ h (x / ε) / |x|) =
        fun x ↦ ε⁻¹ * (outside (δ / ε)).indicator (fun y ↦ h y / |y|) (x / ε) := by
      funext x
      have hmem : x / ε ∈ outside (δ / ε) ↔ x ∈ outside δ := by
        simp only [outside, mem_ofPred_eq, abs_div, abs_of_pos hε]
        exact div_lt_div_iff_of_pos_right hε
      by_cases hx : x ∈ outside δ
      · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx), abs_div, abs_of_pos hε]
        have hx0 : |x| ≠ 0 := (hδ.trans hx).ne'
        field_simp
      · rw [indicator_of_notMem hx, indicator_of_notMem (hmem.not.mpr hx), mul_zero]
    rw [hfun, integral_const_mul, Measure.integral_comp_div, abs_of_pos hε, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
  rw [cutoffRealPole, cutoffRealPole, zero_div, hcut, Real.log_div hδ.ne' hε.ne']
  ring

private def annulus (δ : ℝ) : Set ℝ := {x | δ < |x| ∧ |x| ≤ 1}

private lemma annulus_eq {δ : ℝ} (hδ : 0 < δ) :
    annulus δ = Ico (-1) (-δ) ∪ Ioc δ 1 := by
  ext x
  change (δ < |x| ∧ |x| ≤ 1) ↔ (-1 ≤ x ∧ x < -δ) ∨ (δ < x ∧ x ≤ 1)
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    constructor
    · exact Or.inr
    · rintro (hh | hh)
      · linarith [hh.2]
      · exact hh
  · rw [abs_of_nonpos hx.le]
    constructor
    · intro hh
      exact Or.inl ⟨by linarith [hh.2], by linarith [hh.1]⟩
    · rintro (hh | hh)
      · exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
      · linarith [hh.1]

private lemma invAbs_integrable_interval {a b : ℝ} (hz : (0 : ℝ) ∉ uIcc a b) :
    IntervalIntegrable (fun x : ℝ ↦ |x|⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine continuous_abs.continuousOn.inv₀ fun x hx ↦ ?_
  exact abs_ne_zero.mpr (fun he ↦ hz (he ▸ hx))

private lemma invAbs_integrable_annulus {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (annulus δ) := by
  have hn : (-1 : ℝ) ≤ -δ := by linarith
  have hi₁ := invAbs_integrable_interval (a := -1) (b := -δ) (by
    rw [uIcc_of_le hn]; intro hz; linarith [hz.2])
  have hi₂ := invAbs_integrable_interval (a := δ) (b := 1) (by
    rw [uIcc_of_le hδ₁]; intro hz; linarith [hz.1])
  rw [annulus_eq hδ]
  have hi₁' : IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (Ioc (-1) (-δ)) := hi₁.1
  have he : IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (Ico (-1) (-δ)) := by
    simpa only [IntegrableOn, Measure.restrict_congr_set (μ := volume) Ico_ae_eq_Ioc] using hi₁'
  exact he.union hi₂.1

private lemma integral_invAbs_annulus {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (∫ x in annulus δ, |x|⁻¹) = -2 * Real.log δ := by
  have hn : (-1 : ℝ) ≤ -δ := by linarith
  have ha := invAbs_integrable_annulus hδ hδ₁
  have hs : Disjoint (Ico (-1) (-δ)) (Ioc δ 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1]
  rw [annulus_eq hδ, setIntegral_union hs measurableSet_Ioc
    (ha.mono_set (annulus_eq hδ ▸ subset_union_left))
    (ha.mono_set (annulus_eq hδ ▸ subset_union_right)),
    setIntegral_congr_set Ico_ae_eq_Ioc, ← intervalIntegral.integral_of_le hn,
    ← intervalIntegral.integral_of_le hδ₁]
  have hleft : (∫ x in (-1 : ℝ)..(-δ), |x|⁻¹) = - Real.log δ := by
    calc
      _ = ∫ x in (-1 : ℝ)..(-δ), -x⁻¹ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hn] at hx
        change |x|⁻¹ = -x⁻¹
        rw [abs_of_nonpos (by linarith [hx.2]), inv_neg]
      _ = _ := by
        rw [intervalIntegral.integral_neg, integral_inv_of_neg (by norm_num) (by linarith)]
        simp
  have hright : (∫ x in δ..1, |x|⁻¹) = - Real.log δ := by
    calc
      _ = ∫ x in δ..1, x⁻¹ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hδ₁] at hx
        change |x|⁻¹ = x⁻¹
        rw [abs_of_nonneg (hδ.le.trans hx.1)]
      _ = _ := by rw [integral_inv_of_pos hδ zero_lt_one, one_div, Real.log_inv]
  rw [hleft, hright]
  ring

/-- Subtract the value at the pole on the unit interval before integrating. -/
noncomputable def subtractedRealPole (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (h x - (Icc (-1 : ℝ) 1).indicator (fun _ ↦ h 0) x) / |x|

private lemma cutoffRealPole_eq_integral {h : ℝ → ℝ} (hg : Integrable (subtractedRealPole h))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    cutoffRealPole h δ = ∫ x in outside δ, subtractedRealPole h x := by
  have ha : MeasurableSet (annulus δ) := by rw [annulus_eq hδ]; exact measurableSet_Ico.union measurableSet_Ioc
  have hS := measurableSet_outside δ
  have hfun : (outside δ).indicator (fun x ↦ h x / |x|) = fun x ↦
      (outside δ).indicator (subtractedRealPole h) x +
      h 0 * (annulus δ).indicator (fun x : ℝ ↦ |x|⁻¹) x := by
    funext x
    by_cases hx : x ∈ outside δ
    · rcases le_or_gt |x| 1 with hx₁ | hx₁
      · have hI : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx₁
        have hA : x ∈ annulus δ := ⟨hx, hx₁⟩
        rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hA, subtractedRealPole,
          indicator_of_mem hI]
        rw [sub_div, div_eq_mul_inv (h 0), sub_add_cancel]
      · have hI : x ∉ Icc (-1 : ℝ) 1 := fun h ↦ hx₁.not_ge (abs_le.mpr h)
        have hA : x ∉ annulus δ := fun h ↦ hx₁.not_ge h.2
        rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_notMem hA, mul_zero, add_zero,
          subtractedRealPole, indicator_of_notMem hI, sub_zero]
    · have hA : x ∉ annulus δ := fun h ↦ hx h.1
      rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hA, mul_zero, zero_add]
  rw [cutoffRealPole, ← integral_indicator hS, hfun,
    integral_add (hg.indicator hS) ((invAbs_integrable_annulus hδ hδ₁).integrable_indicator ha |>.const_mul (h 0)),
    integral_indicator hS, integral_const_mul, integral_indicator ha, integral_invAbs_annulus hδ hδ₁]
  ring

private lemma tendsto_integral_outside {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun δ ↦ ∫ x in outside δ, f x) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x)) := by
  have hi : Tendsto (fun δ ↦ ∫ x, (outside δ).indicator (f) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    · exact Eventually.of_forall (fun δ ↦ hf.aestronglyMeasurable.indicator (measurableSet_outside δ))
    · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall (fun x ↦ by
        by_cases hx : x ∈ outside δ
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _))
    · exact hf.norm
    · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
      filter_upwards [hne] with x hx
      have he : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < |x| :=
        (gt_mem_nhds (abs_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [he] with δ hδ
      exact (indicator_of_mem (show x ∈ outside δ from hδ) _).symm
  simpa only [integral_indicator (measurableSet_outside _)] using hi

/-- The normalized cutoff integral converges to the integral of the subtracted kernel. -/
theorem cutoffRealPole_tendsto {h : ℝ → ℝ} (hg : Integrable (subtractedRealPole h)) :
    Tendsto (cutoffRealPole h) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, subtractedRealPole h x)) := by
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ 1 := by
    have h0 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have h1 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < 1 :=
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [h0, h1] with δ hδ hδ₁ using ⟨hδ, hδ₁.le⟩
  have hi := tendsto_integral_outside hg
  refine hi.congr' ?_
  filter_upwards [hall] with δ hδ
  exact (cutoffRealPole_eq_integral hg hδ.1 hδ.2).symm

/-- Scaling the test shifts the finite part by exactly `2 * h 0 * log ε`. -/
theorem cutoffRealPole_scaled_tendsto {h : ℝ → ℝ} (hg : Integrable (subtractedRealPole h))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (cutoffRealPole (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x, subtractedRealPole h x) + 2 * h 0 * Real.log ε)) := by
  have hdiv : Tendsto (fun δ : ℝ ↦ δ / ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const ε).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with δ hδ
      exact div_pos hδ hε
  have hlim := ((cutoffRealPole_tendsto hg).comp hdiv).add_const (2 * h 0 * Real.log ε)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with δ hδ
  exact (cutoffRealPole_scale h hε hδ).symm

/-- A bounded compactly supported test with linear variation at zero has an integrable
subtracted pole. -/
theorem integrable_subtractedRealPole {h : ℝ → ℝ} (hh : Measurable h) {R M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hbound : ∀ x, |h x| ≤ M)
    (hsupport : ∀ x, R < |x| → h x = 0)
    (hLip : ∀ x, |x| ≤ 1 → |h x - h 0| ≤ L * |x|) :
    Integrable (subtractedRealPole h) := by
  let S := Icc (-max R 1) (max R 1)
  have hS : MeasurableSet S := measurableSet_Icc
  have hB : Integrable (S.indicator fun _ ↦ L + M) :=
    (integrableOn_const (C := L + M) (isCompact_Icc.measure_lt_top.ne)).integrable_indicator hS
  refine hB.mono' ?_ ?_
  · exact ((hh.sub (measurable_const.indicator measurableSet_Icc)).div measurable_abs).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, subtractedRealPole, abs_div, abs_abs]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      rcases le_or_gt |x| 1 with hx₁ | hx₁
      · rw [indicator_of_mem (show x ∈ Icc (-1 : ℝ) 1 from abs_le.mp hx₁)]
        by_cases hx₀ : x = 0
        · simp [hx₀, add_nonneg hL hM]
        · have hhx := hLip x hx₁
          exact ((div_le_iff₀ (abs_pos.mpr hx₀)).mpr hhx).trans (le_add_of_nonneg_right hM)
      · rw [indicator_of_notMem (show x ∉ Icc (-1 : ℝ) 1 from fun h ↦ hx₁.not_ge (abs_le.mpr h)),
          sub_zero]
        exact ((div_le_self (abs_nonneg _) hx₁.le).trans (hbound x)).trans (le_add_of_nonneg_left hL)
    · have hx' : max R 1 < |x| := lt_of_not_ge (fun h ↦ hx (abs_le.mp h))
      rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ Icc (-1 : ℝ) 1 from fun h ↦
        (lt_of_le_of_lt (le_max_right R 1) hx').not_ge (abs_le.mpr h)),
        hsupport x ((le_max_left R 1).trans_lt hx')]
      simp

private noncomputable def realKernelPos (x : ℝ) : ℝ :=
  Real.exp (x / 2) / |1 - Real.exp x|

private noncomputable def realKernelNeg (x : ℝ) : ℝ :=
  Real.exp (x / 2) / (1 + Real.exp x)

/-- The kernel on both real branches in the log coordinate for the trivial character. -/
noncomputable def realPlaceKernel (x : ℝ) : ℝ := realKernelPos x + realKernelNeg x

private noncomputable def realPlaceRemainder (x : ℝ) : ℝ :=
  realPlaceKernel x - |x|⁻¹

private lemma realKernelNeg_nonneg (x : ℝ) : 0 ≤ realKernelNeg x := by
  unfold realKernelNeg
  positivity

private lemma realKernelNeg_le (x : ℝ) : realKernelNeg x ≤ 1 / 2 := by
  have hsq : Real.exp x = (Real.exp (x / 2)) ^ 2 := by
    rw [show x = x / 2 + x / 2 by ring, Real.exp_add, pow_two]
    ring_nf
  unfold realKernelNeg
  apply (div_le_iff₀ (by positivity)).mpr
  rw [hsq]
  nlinarith [sq_nonneg (Real.exp (x / 2) - 1)]

private lemma abs_exp_half_sub_one_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp (x / 2) - 1| ≤ |x| := by
  have hhalf : |x / 2| = |x| / 2 := by rw [abs_div, abs_two]
  have hr := Real.abs_exp_sub_one_sub_id_le (show |x / 2| ≤ 1 by rw [hhalf]; linarith)
  have hxs : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  calc
    _ = |(Real.exp (x / 2) - 1 - x / 2) + x / 2| := by congr 1; ring
    _ ≤ |Real.exp (x / 2) - 1 - x / 2| + |x / 2| := abs_add_le _ _
    _ ≤ (x / 2) ^ 2 + |x / 2| := add_le_add hr le_rfl
    _ ≤ _ := by
      rw [hhalf, div_pow, hxs]
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg x)]

private lemma realKernelPos_sub_invAbs_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |realKernelPos x - |x|⁻¹| ≤ 4 := by
  by_cases hx₀ : x = 0
  · simp [hx₀, realKernelPos]
  have hxpos : 0 < |x| := abs_pos.mpr hx₀
  have hd : abs (|1 - Real.exp x| - |x|) ≤ |x| ^ 2 := by
    rw [abs_sub_comm 1 (Real.exp x), sq_abs]
    exact (abs_abs_sub_abs_le_abs_sub (Real.exp x - 1) x).trans
      (Real.abs_exp_sub_one_sub_id_le (by linarith))
  have hden : |x| / 2 ≤ |1 - Real.exp x| := by
    have hr := (abs_le.mp hd).1
    nlinarith [mul_le_mul_of_nonneg_left hx hxpos.le]
  have hden₀ : 0 < |1 - Real.exp x| := (half_pos hxpos).trans_le hden
  have hnum : abs (|x| * Real.exp (x / 2) - |1 - Real.exp x|) ≤ 2 * |x| ^ 2 := by
    calc
      _ = abs (|x| * (Real.exp (x / 2) - 1) - (|1 - Real.exp x| - |x|)) := by congr 1; ring
      _ ≤ abs (|x| * (Real.exp (x / 2) - 1)) + abs (|1 - Real.exp x| - |x|) := abs_sub _ _
      _ ≤ |x| * |x| + |x| ^ 2 := by
        rw [abs_mul, abs_abs]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_exp_half_sub_one_le (by linarith)) hxpos.le) hd
      _ = _ := by ring
  have hEq : realKernelPos x - |x|⁻¹ =
      (|x| * Real.exp (x / 2) - |1 - Real.exp x|) / (|1 - Real.exp x| * |x|) := by
    unfold realKernelPos
    field_simp [hden₀.ne', hxpos.ne']
  rw [hEq, abs_div, abs_of_pos (mul_pos hden₀ hxpos)]
  apply (div_le_iff₀ (mul_pos hden₀ hxpos)).mpr
  exact hnum.trans (by nlinarith [mul_le_mul_of_nonneg_right hden hxpos.le])

private lemma realPlaceRemainder_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |realPlaceRemainder x| ≤ 5 := by
  unfold realPlaceRemainder realPlaceKernel
  rw [add_sub_right_comm]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (realKernelNeg_nonneg x)]
  linarith [realKernelPos_sub_invAbs_bound hx, realKernelNeg_le x]

private lemma integrable_norm_integral_le_of_Icc {f : ℝ → ℝ} (hf : Measurable f)
    {r C : ℝ} (hr : 0 ≤ r) (hb : ∀ x ∈ Icc (-r) r, ‖f x‖ ≤ C)
    (hz : ∀ x ∉ Icc (-r) r, f x = 0) :
    Integrable f ∧ ‖∫ x, f x‖ ≤ (2 * r) * C := by
  have hC : Integrable ((Icc (-r) r).indicator (fun _ ↦ C)) :=
    (integrableOn_const (C := C) isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hdom : ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ (Icc (-r) r).indicator (fun _ ↦ C) x := by
    filter_upwards with x
    by_cases hx : x ∈ Icc (-r) r
    · rw [indicator_of_mem hx]
      exact hb x hx
    · rw [indicator_of_notMem hx, hz x hx, norm_zero]
  refine ⟨hC.mono' hf.aestronglyMeasurable hdom, ?_⟩
  have h := norm_integral_le_of_norm_le hC hdom
  rw [integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : -r ≤ r), smul_eq_mul,
    show r - -r = 2 * r by ring] at h
  exact h

private lemma scaledRealRemainder {h : ℝ → ℝ} (hh : Measurable h) {R M ε : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hε : 0 < ε) (hsmall : R * ε ≤ 1 / 2)
    (hbound : ∀ x, |h x| ≤ M) (hsupport : ∀ x, R < |x| → h x = 0) :
    Integrable (fun x ↦ h (x / ε) * realPlaceRemainder x) ∧
      |∫ x, h (x / ε) * realPlaceRemainder x| ≤ 10 * M * R * ε := by
  have hmeas : Measurable (fun x ↦ h (x / ε) * realPlaceRemainder x) := by
    unfold realPlaceRemainder realPlaceKernel realKernelPos realKernelNeg
    fun_prop
  have hB (x : ℝ) (hx : x ∈ Icc (-(R * ε)) (R * ε)) :
      ‖h (x / ε) * realPlaceRemainder x‖ ≤ 5 * M := by
    rw [Real.norm_eq_abs, abs_mul]
    have hx' : |x| ≤ 1 / 2 := (abs_le.mpr hx).trans hsmall
    calc
      _ ≤ M * 5 := mul_le_mul (hbound (x / ε)) (realPlaceRemainder_bound hx') (abs_nonneg _) hM
      _ = _ := by ring
  have hZ (x : ℝ) (hx : x ∉ Icc (-(R * ε)) (R * ε)) :
      h (x / ε) * realPlaceRemainder x = 0 := by
    have hx' : R * ε < |x| := lt_of_not_ge (fun he ↦ hx (abs_le.mp he))
    have hr : R < |x / ε| := by
      rw [abs_div, abs_of_pos hε]
      exact (lt_div_iff₀ hε).mpr hx'
    rw [hsupport _ hr, zero_mul]
  obtain ⟨hi, hb⟩ := integrable_norm_integral_le_of_Icc hmeas (mul_nonneg hR hε.le) hB hZ
  refine ⟨hi, ?_⟩
  rw [Real.norm_eq_abs, show 2 * (R * ε) * (5 * M) = 10 * M * R * ε by ring] at hb
  exact hb

private lemma integrableOn_scaled_pole {h : ℝ → ℝ} (hh : Measurable h) {R M ε δ : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hε : 0 < ε) (hδ : 0 < δ)
    (hbound : ∀ x, |h x| ≤ M) (hsupport : ∀ x, R < |x| → h x = 0) :
    IntegrableOn (fun x ↦ h (x / ε) / |x|) (outside δ) := by
  let f := (outside δ).indicator (fun x ↦ h (x / ε) / |x|)
  have hf : Measurable f := ((hh.comp (measurable_id.div_const _)).div measurable_abs).indicator
    (measurableSet_outside δ)
  have hB (x : ℝ) (_hx : x ∈ Icc (-(R * ε)) (R * ε)) : ‖f x‖ ≤ M / δ := by
    dsimp only [f]
    by_cases hx : x ∈ outside δ
    · change δ < |x| at hx
      rw [indicator_of_mem (show x ∈ outside δ from hx), Real.norm_eq_abs, abs_div, abs_abs]
      exact (div_le_div_of_nonneg_right (hbound _) (abs_nonneg _)).trans
        (div_le_div_of_nonneg_left hM hδ hx.le)
    · rw [indicator_of_notMem hx, norm_zero]
      positivity
  have hZ (x : ℝ) (hx : x ∉ Icc (-(R * ε)) (R * ε)) : f x = 0 := by
    have hx' : R * ε < |x| := lt_of_not_ge (fun he ↦ hx (abs_le.mp he))
    have hr : R < |x / ε| := by
      rw [abs_div, abs_of_pos hε]
      exact (lt_div_iff₀ hε).mpr hx'
    simp [f, hsupport _ hr]
  exact (integrable_indicator_iff (measurableSet_outside δ)).mp
    (integrable_norm_integral_le_of_Icc hf (mul_nonneg hR hε.le) hB hZ).1

/-- Symmetric logarithmic cutoff of the real-place integral without the prefactor `1/2`. -/
noncomputable def cutoffRealPlace (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in outside δ, h x * realPlaceKernel x) + 2 * h 0 * Real.log δ

/-- The real-place finite part under shrinking tests has logarithmic coefficient `2 h(0)`.
Restoring the prefactor `1/2` from Theorem 12.5.1.1 gives the coefficient `h(0)`. -/
theorem real_place_finite_part_log_scaling {h : ℝ → ℝ} (hh : Measurable h) {R M L ε : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L) (hε : 0 < ε) (hsmall : R * ε ≤ 1 / 2)
    (hbound : ∀ x, |h x| ≤ M) (hsupport : ∀ x, R < |x| → h x = 0)
    (hLip : ∀ x, |x| ≤ 1 → |h x - h 0| ≤ L * |x|) :
    ∃ v : ℝ, Tendsto (cutoffRealPlace (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      |v - ((∫ x, subtractedRealPole h x) + 2 * h 0 * Real.log ε)| ≤ 10 * M * R * ε := by
  have hG := integrable_subtractedRealPole hh hM hL hbound hsupport hLip
  obtain ⟨hRI, hRbound⟩ := scaledRealRemainder hh hR hM hε hsmall hbound hsupport
  have hcont := (cutoffRealPole_scaled_tendsto hG hε).add (tendsto_integral_outside hRI)
  refine ⟨_, hcont.congr' ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with δ hδ
    have hPo := integrableOn_scaled_pole hh hR hM hε hδ hbound hsupport
    have hfun : (fun x ↦ h (x / ε) * realPlaceKernel x) =
        (fun x ↦ h (x / ε) / |x| + h (x / ε) * realPlaceRemainder x) := by
      funext x
      unfold realPlaceRemainder
      rw [div_eq_mul_inv]
      ring
    rw [cutoffRealPlace, cutoffRealPole, hfun, integral_add hPo hRI.integrableOn]
    ring
  · simpa only [add_sub_cancel_left] using hRbound


/-- Integrability of the regularized positive branch and of the entire
negative branch, for the same shrinking tests as in the scaling theorem. -/
theorem integrable_shrinking_real_place_branches {h : ℝ → ℝ} (hh : Measurable h)
    {R M L ε : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hε : 0 < ε) (hsmall : R * ε ≤ 1 / 2)
    (hbound : ∀ x, |h x| ≤ M) (hsupport : ∀ x, R < |x| → h x = 0)
    (hLip : ∀ x, |x| ≤ 1 → |h x - h 0| ≤ L * |x|) :
    Integrable (fun x : ℝ ↦ h (x / ε) * (Real.exp (x / 2) / |1 - Real.exp x|) -
        h 0 * (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x) ∧
    Integrable (fun x : ℝ ↦ h (x / ε) * (Real.exp (x / 2) / (1 + Real.exp x))) := by
  have hsc : Measurable (fun x : ℝ ↦ h (x / ε)) := hh.comp (measurable_id.div_const ε)
  have hscBound (x : ℝ) : |h (x / ε)| ≤ M := hbound _
  have hscSupport (x : ℝ) (hx : R * ε < |x|) : h (x / ε) = 0 := by
    apply hsupport
    rw [abs_div, abs_of_pos hε]
    exact (lt_div_iff₀ hε).mpr hx
  have hconst (x : ℝ) : |h (x / ε) - h (0 / ε)| ≤ (max L (2 * M) / ε) * |x| := by
    rw [zero_div, div_mul_eq_mul_div, mul_div_assoc]
    have he : |x| / ε = |x / ε| := by rw [abs_div, abs_of_pos hε]
    rw [he]
    rcases le_or_gt |x / ε| 1 with hb | hb
    · exact (hLip _ hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · calc
        _ ≤ |h (x / ε)| + |h 0| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hbound (x / ε), hbound 0]
        _ ≤ max L (2 * M) * |x / ε| :=
          (le_max_right _ _).trans (le_mul_of_one_le_right
            (le_trans (by positivity : 0 ≤ 2 * M) (le_max_right _ _)) hb.le)
  have hSub : Integrable (subtractedRealPole (fun x : ℝ ↦ h (x / ε))) :=
    integrable_subtractedRealPole hsc hM (div_nonneg (le_trans hL (le_max_left _ _)) hε.le)
      hscBound hscSupport (fun x _ ↦ hconst x)
  have hNeg : Integrable (fun x : ℝ ↦ h (x / ε) * realKernelNeg x) := by
    have hM' : Measurable (fun x : ℝ ↦ h (x / ε) * realKernelNeg x) := by
      unfold realKernelNeg
      fun_prop
    apply (integrable_norm_integral_le_of_Icc hM' (mul_nonneg hR hε.le) (C := M / 2) ?_ ?_).1
    · intro x _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (realKernelNeg_nonneg x)]
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul (hbound (x / ε)) (realKernelNeg_le x) (realKernelNeg_nonneg x) hM
    · intro x hx
      have hx' : R * ε < |x| := lt_of_not_ge (fun he ↦ hx (abs_le.mp he))
      rw [hscSupport x hx', zero_mul]
  refine ⟨?_, hNeg⟩
  have hRem := (scaledRealRemainder hh hR hM hε hsmall hbound hsupport).1
  have hSum := (hSub.add hRem).sub hNeg
  have heq : (fun x ↦ (subtractedRealPole (fun x : ℝ ↦ h (x / ε)) x +
      h (x / ε) * realPlaceRemainder x) - h (x / ε) * realKernelNeg x) =
      (fun x ↦ h (x / ε) * (Real.exp (x / 2) / |1 - Real.exp x|) -
        h 0 * (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x) := by
    funext x
    unfold subtractedRealPole realPlaceRemainder realPlaceKernel realKernelPos
    simp only [zero_div]
    have he : (Icc (-1 : ℝ) 1).indicator (fun _ ↦ h 0) x / |x| =
        h 0 * (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x := by
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hx, indicator_of_mem hx, div_eq_mul_inv]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_div, mul_zero]
    rw [sub_div, he, div_eq_mul_inv]
    ring
  rwa [← heq]

end MasulloAudit

/-!
# The real-place finite part under a change of cutoff

For the positive branch in Masullo's formula, cutting out `|g - 1| ≤ δ`
amounts to cutting out the logarithmic interval
`[log (1 - δ), log (1 + δ)]`. The two one-sided log radii are asymptotic
to δ. The finite-part counterterm consequently has the same limit.
-/

open Filter MeasureTheory Set
open scoped Interval Topology

namespace MasulloAudit

private def exterior (a b : ℝ) : Set ℝ := Iio (-a) ∪ Ioi b

private lemma measurableSet_exterior (a b : ℝ) : MeasurableSet (exterior a b) :=
  measurableSet_Iio.union measurableSet_Ioi

private noncomputable def localPole (x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x

private lemma integrable_leftPole {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (Ico (-1) (-a)) := by
  have hO : (-1 : ℝ) ≤ -a := by linarith
  have hI : IntervalIntegrable (fun x : ℝ ↦ |x|⁻¹) volume (-1) (-a) := by
    apply ContinuousOn.intervalIntegrable
    refine continuous_abs.continuousOn.inv₀ fun x hx ↦ abs_ne_zero.mpr ?_
    rw [uIcc_of_le hO] at hx
    exact (show x < 0 by linarith [hx.2]).ne
  simpa only [IntegrableOn, Measure.restrict_congr_set (μ := volume) Ico_ae_eq_Ioc] using hI.1

private lemma integrable_rightPole {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) :
    IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (Ioc b 1) := by
  have hI : IntervalIntegrable (fun x : ℝ ↦ |x|⁻¹) volume b 1 := by
    apply ContinuousOn.intervalIntegrable
    refine continuous_abs.continuousOn.inv₀ fun x hx ↦ abs_ne_zero.mpr ?_
    rw [uIcc_of_le hb₁] at hx
    exact (hb.trans_le hx.1).ne'
  exact hI.1

private lemma integral_leftPole {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    (∫ x in Ico (-1 : ℝ) (-a), |x|⁻¹) = -Real.log a := by
  have hO : (-1 : ℝ) ≤ -a := by linarith
  rw [setIntegral_congr_set Ico_ae_eq_Ioc, ← intervalIntegral.integral_of_le hO]
  calc
    _ = ∫ x in (-1 : ℝ)..(-a), -x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hO] at hx
      change |x|⁻¹ = -x⁻¹
      rw [abs_of_nonpos (by linarith [hx.2]), inv_neg]
    _ = _ := by
      rw [intervalIntegral.integral_neg, integral_inv_of_neg (by norm_num) (by linarith)]
      simp

private lemma integral_rightPole {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) :
    (∫ x in Ioc b 1, |x|⁻¹) = -Real.log b := by
  rw [← intervalIntegral.integral_of_le hb₁]
  calc
    _ = ∫ x in b..1, x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb₁] at hx
      change |x|⁻¹ = x⁻¹
      rw [abs_of_nonneg (hb.le.trans hx.1)]
    _ = _ := by rw [integral_inv_of_pos hb zero_lt_one, one_div, Real.log_inv]

private lemma exterior_inter_Icc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    exterior a b ∩ Icc (-1 : ℝ) 1 = Ico (-1) (-a) ∪ Ioc b 1 := by
  ext x
  change (x < -a ∨ b < x) ∧ (-1 ≤ x ∧ x ≤ 1) ↔
    (-1 ≤ x ∧ x < -a) ∨ (b < x ∧ x ≤ 1)
  constructor
  · rintro ⟨hx | hx, hx₁, hx₂⟩
    · exact Or.inl ⟨hx₁, hx⟩
    · exact Or.inr ⟨hx, hx₂⟩
  · rintro (⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩)
    · exact ⟨Or.inl hx₂, hx₁, by linarith⟩
    · exact ⟨Or.inr hx₁, by linarith, hx₂⟩

private lemma integrableOn_localPole {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) : IntegrableOn localPole (exterior a b) := by
  unfold localPole
  rw [integrableOn_indicator_iff measurableSet_Icc, inter_comm, exterior_inter_Icc ha hb]
  exact (integrable_leftPole ha ha₁).union (integrable_rightPole hb hb₁)

private lemma integral_localPole {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) :
    (∫ x in exterior a b, localPole x) = -Real.log a - Real.log b := by
  have hD : Disjoint (Ico (-1 : ℝ) (-a)) (Ioc b 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1]
  unfold localPole
  rw [setIntegral_indicator measurableSet_Icc, exterior_inter_Icc ha hb,
    setIntegral_union hD measurableSet_Ioc (integrable_leftPole ha ha₁)
      (integrable_rightPole hb hb₁), integral_leftPole ha ha₁, integral_rightPole hb hb₁]
  ring

private lemma corrected_cutoff_eq (f : ℝ → ℝ) (c : ℝ)
    (hI : Integrable (fun x ↦ f x - c * localPole x)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) :
    (∫ x in exterior a b, f x) + c * (Real.log a + Real.log b) =
      ∫ x in exterior a b, f x - c * localPole x := by
  have heq : f = fun x ↦ (f x - c * localPole x) + c * localPole x := by
    funext x
    ring
  have hInt := (integrableOn_localPole ha hb ha₁ hb₁).const_mul c
  nth_rw 1 [heq]
  rw [integral_add hI.integrableOn hInt, integral_const_mul, integral_localPole ha hb ha₁ hb₁]
  ring

private lemma tendsto_setIntegral_exterior {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {a b : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 0))
    {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun t ↦ ∫ x in exterior (a t) (b t), g x) l (𝓝 (∫ x, g x)) := by
  simp only [← integral_indicator (measurableSet_exterior _ _)]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖g x‖)
  · exact Eventually.of_forall fun t ↦
      hg.aestronglyMeasurable.indicator (measurableSet_exterior (a t) (b t))
  · exact Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ exterior (a t) (b t)
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
  · exact hg.norm
  · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with x hx
    have he : ∀ᶠ t in l, x ∈ exterior (a t) (b t) := by
      rcases lt_or_gt_of_ne hx with h | h
      · filter_upwards [ha (gt_mem_nhds (neg_pos.mpr h))] with t ht
        change a t < -x at ht
        exact Or.inl (show x < -a t by linarith)
      · filter_upwards [hb (gt_mem_nhds h)] with t ht
        exact Or.inr ht
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [he] with t ht
    exact (indicator_of_mem ht _).symm

private lemma tendsto_corrected_cutoff {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {a b : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 0))
    (hapos : ∀ᶠ t in l, 0 < a t) (hbpos : ∀ᶠ t in l, 0 < b t)
    {f : ℝ → ℝ} {c : ℝ} (hI : Integrable (fun x ↦ f x - c * localPole x)) :
    Tendsto (fun t ↦ (∫ x in exterior (a t) (b t), f x) +
      c * (Real.log (a t) + Real.log (b t))) l (𝓝 (∫ x, f x - c * localPole x)) := by
  refine (tendsto_setIntegral_exterior ha hb hI).congr' ?_
  filter_upwards [hapos, hbpos, ha (gt_mem_nhds zero_lt_one), hb (gt_mem_nhds zero_lt_one)] with
    t ha' hb' ha₁ hb₁
  exact (corrected_cutoff_eq f c hI ha' hb' ha₁.le hb₁.le).symm


private lemma tendsto_leftRadius :
    Tendsto (fun δ : ℝ ↦ -Real.log (1 - δ)) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).comp_of_eq
    (continuousAt_const.sub continuousAt_id : ContinuousAt (fun δ : ℝ ↦ 1 - δ) 0) (by simp)).neg
  simpa [Function.comp_def, Pi.neg_def] using
    h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

private lemma tendsto_rightRadius :
    Tendsto (fun δ : ℝ ↦ Real.log (1 + δ)) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).comp_of_eq
    (continuousAt_const.add continuousAt_id : ContinuousAt (fun δ : ℝ ↦ 1 + δ) 0) (by simp)
  simpa [Function.comp_def, Pi.neg_def] using
    h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

private lemma tendsto_leftRadius_div :
    Tendsto (fun δ : ℝ ↦ -Real.log (1 - δ) / δ) (𝓝[>] 0) (𝓝 1) := by
  have hd := (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).comp_of_eq (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))) (by simp)
  have ht := hd.neg.tendsto_slope_zero_right
  simpa [Function.comp_def, div_eq_inv_mul, add_comm, sub_eq_add_neg] using ht

private lemma tendsto_rightRadius_div :
    Tendsto (fun δ : ℝ ↦ Real.log (1 + δ) / δ) (𝓝[>] 0) (𝓝 1) := by
  have hd := (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).comp_of_eq (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))) (by simp)
  simpa [Function.comp_def, div_eq_inv_mul] using hd.tendsto_slope_zero_right

private lemma eventual_cutoff_radius_positive :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < 1 :=
  by
    have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
    have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
      (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    exact hpos.and hsmall

private lemma leftRadius_pos {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    0 < -Real.log (1 - δ) := by
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hδ₁) (by linarith))

private lemma rightRadius_pos {δ : ℝ} (hδ : 0 < δ) : 0 < Real.log (1 + δ) :=
  Real.log_pos (by linarith)

private lemma tendsto_cutoff_counterterm_error (c : ℝ) :
    Tendsto (fun δ : ℝ ↦ 2 * c * Real.log δ -
      c * (Real.log (-Real.log (1 - δ)) + Real.log (Real.log (1 + δ))))
      (𝓝[>] 0) (𝓝 0) := by
  have hL := (Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_leftRadius_div
  have hR := (Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_rightRadius_div
  have hsum := (hL.add hR).const_mul (-c)
  simp only [Real.log_one, add_zero, mul_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventual_cutoff_radius_positive] with δ hδ
  dsimp only [Function.comp_apply]
  rw [Real.log_div (leftRadius_pos hδ.1 hδ.2).ne' hδ.1.ne',
    Real.log_div (rightRadius_pos hδ.1).ne' hδ.1.ne']
  ring

private lemma exterior_logRadii {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    exterior (-Real.log (1 - δ)) (Real.log (1 + δ)) = {x | δ < |1 - Real.exp x|} := by
  ext x
  change (x < -(-Real.log (1 - δ)) ∨ Real.log (1 + δ) < x) ↔ δ < |1 - Real.exp x|
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ₁
  have hpos' : 0 < 1 + δ := by linarith
  rw [neg_neg, Real.lt_log_iff_exp_lt hpos, Real.log_lt_iff_lt_exp hpos', lt_abs]
  constructor <;> intro h <;> rcases h with h | h <;> first | exact Or.inl (by linarith) |
    exact Or.inr (by linarith)

private lemma exterior_diagonal (δ : ℝ) : exterior δ δ = {x | δ < |x|} := by
  ext x
  change (x < -δ ∨ δ < x) ↔ δ < |x|
  rw [lt_abs]
  constructor <;> rintro (h | h)
  · exact Or.inr (by linarith)
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl (by linarith)

/-- A test kernel with simple pole coefficient `c` has the same finite
part with either the additive cutoff in the original positive real
variable or the symmetric cutoff in its logarithm. -/
theorem real_place_cutoff_conventions_agree (f : ℝ → ℝ) (c : ℝ)
    (hI : Integrable (fun x ↦ f x - c *
      (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x)) :
    let v := ∫ x, f x - c * (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x
    Tendsto (fun δ ↦ (∫ x in {x | δ < |x|}, f x) + 2 * c * Real.log δ)
        (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
    Tendsto (fun δ ↦ (∫ x in {x | δ < |1 - Real.exp x|}, f x) + 2 * c * Real.log δ)
        (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  have hI' : Integrable (fun x ↦ f x - c * localPole x) := hI
  have hId : Tendsto (fun δ : ℝ ↦ δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hIdpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  constructor
  · refine (tendsto_corrected_cutoff hId hId hIdpos hIdpos hI').congr' ?_
    filter_upwards [hIdpos] with δ _
    rw [exterior_diagonal]
    ring
  · have hA : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < -Real.log (1 - δ) :=
      eventual_cutoff_radius_positive.mono fun _ hδ ↦ leftRadius_pos hδ.1 hδ.2
    have hB : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < Real.log (1 + δ) :=
      hIdpos.mono fun _ hδ ↦ rightRadius_pos hδ
    have hLim := (tendsto_corrected_cutoff tendsto_leftRadius tendsto_rightRadius hA hB hI').add
      (tendsto_cutoff_counterterm_error c)
    rw [add_zero] at hLim
    refine hLim.congr' ?_
    filter_upwards [eventual_cutoff_radius_positive] with δ hδ
    rw [exterior_logRadii hδ.1 hδ.2]
    ring


private def expCutoff (δ : ℝ) : Set ℝ := {x | δ < |1 - Real.exp x|}

private def positiveCutoff (δ : ℝ) : Set ℝ := {g | 0 < g ∧ δ < |1 - g|}

private noncomputable def rawKernel (h : ℝ → ℝ) (g : ℝ) : ℝ :=
  h (Real.log |g|) * Real.exp (-Real.log |g| / 2) / |1 - g|

private noncomputable def positiveKernel (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  h x * (Real.exp (x / 2) / |1 - Real.exp x|)

private noncomputable def negativeKernel (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  h x * (Real.exp (x / 2) / (1 + Real.exp x))

private lemma expCutoff_measurable (δ : ℝ) : MeasurableSet (expCutoff δ) :=
  (isOpen_lt continuous_const (continuous_const.sub Real.continuous_exp).abs).measurableSet

private lemma image_expCutoff (δ : ℝ) :
    Real.exp '' expCutoff δ = positiveCutoff δ := by
  ext g
  change g ∈ Real.exp '' expCutoff δ ↔ 0 < g ∧ δ < |1 - g|
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.exp_pos x, hx⟩
  · rintro ⟨hg, hg'⟩
    refine ⟨Real.log g, ?_, Real.exp_log hg⟩
    change δ < |1 - Real.exp (Real.log g)|
    rw [Real.exp_log hg]
    exact hg'

private lemma image_neg_exp : (fun x : ℝ ↦ -Real.exp x) '' univ = Iio 0 := by
  ext g
  rw [mem_image]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact neg_lt_zero.mpr (Real.exp_pos x)
  · intro hg
    refine ⟨Real.log (-g), mem_univ _, ?_⟩
    rw [Real.exp_log (neg_pos.mpr hg), neg_neg]

private lemma substitute_positive (h : ℝ → ℝ) (x : ℝ) :
    |Real.exp x| • rawKernel h (Real.exp x) = positiveKernel h x := by
  rw [rawKernel, positiveKernel, abs_of_pos (Real.exp_pos x), Real.log_exp, smul_eq_mul]
  calc
    _ = h x * ((Real.exp x * Real.exp (-x / 2)) / |1 - Real.exp x|) := by ring
    _ = _ := by rw [← Real.exp_add, show x + -x / 2 = x / 2 by ring]

private lemma substitute_negative (h : ℝ → ℝ) (x : ℝ) :
    |-Real.exp x| • rawKernel h (-Real.exp x) = negativeKernel h x := by
  rw [rawKernel, negativeKernel, abs_neg, abs_of_pos (Real.exp_pos x), Real.log_exp, smul_eq_mul,
    sub_neg_eq_add, abs_of_pos (by positivity : 0 < 1 + Real.exp x)]
  calc
    _ = h x * ((Real.exp x * Real.exp (-x / 2)) / (1 + Real.exp x)) := by ring
    _ = _ := by rw [← Real.exp_add, show x + -x / 2 = x / 2 by ring]

private lemma positive_integral_change (h : ℝ → ℝ) (δ : ℝ) :
    ((∫ g in positiveCutoff δ, rawKernel h g) = ∫ x in expCutoff δ, positiveKernel h x) ∧
    (IntegrableOn (rawKernel h) (positiveCutoff δ) ↔
      IntegrableOn (positiveKernel h) (expCutoff δ)) := by
  have hd : ∀ x ∈ expCutoff δ, HasDerivWithinAt Real.exp (Real.exp x) (expCutoff δ) x :=
    fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (expCutoff δ) := Real.exp_injective.injOn
  have heq := integral_image_eq_integral_abs_deriv_smul (expCutoff_measurable δ) hd hinj (rawKernel h)
  have hint := integrableOn_image_iff_integrableOn_abs_deriv_smul (expCutoff_measurable δ)
    hd hinj (rawKernel h)
  rw [image_expCutoff] at heq hint
  simpa only [substitute_positive] using And.intro heq hint

private lemma negative_integral_change (h : ℝ → ℝ) :
    ((∫ g in Iio 0, rawKernel h g) = ∫ x, negativeKernel h x) ∧
    (IntegrableOn (rawKernel h) (Iio 0) ↔ Integrable (negativeKernel h)) := by
  have hd : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun x : ℝ ↦ -Real.exp x) (-Real.exp x) univ x :=
    fun x _ ↦ (Real.hasDerivAt_exp x).neg.hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ ↦ -Real.exp x) univ :=
    (neg_injective.comp Real.exp_injective).injOn
  have heq := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj (rawKernel h)
  have hint := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    hd hinj (rawKernel h)
  rw [image_neg_exp] at heq hint
  simpa only [substitute_negative, setIntegral_univ, integrableOn_univ] using And.intro heq hint

/-- The real integral of the translated test in (B.4.3.13), expressed in
the original multiplicative coordinate `g = 1 + x`. -/
noncomputable def cutoffRealPlaceAdditive (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ g in {g | g ≠ 0 ∧ δ < |1 - g|}, rawKernel h g) + 2 * h 0 * Real.log δ

private lemma realPlaceAdditive_eq {h : ℝ → ℝ} {δ : ℝ} (hδ₁ : δ < 1)
    (hPos : IntegrableOn (positiveKernel h) (expCutoff δ))
    (hNeg : Integrable (negativeKernel h)) :
    cutoffRealPlaceAdditive h δ =
      (∫ x in expCutoff δ, positiveKernel h x) +
        (∫ x, negativeKernel h x) + 2 * h 0 * Real.log δ := by
  have hSet : {g : ℝ | g ≠ 0 ∧ δ < |1 - g|} = positiveCutoff δ ∪ Iio 0 := by
    ext g
    change (g ≠ 0 ∧ δ < |1 - g|) ↔ (0 < g ∧ δ < |1 - g|) ∨ g < 0
    constructor
    · rintro ⟨hg, hg'⟩
      rcases lt_or_gt_of_ne hg with h | h
      · exact Or.inr h
      · exact Or.inl ⟨h, hg'⟩
    · rintro (⟨hg, hg'⟩ | hg)
      · exact ⟨hg.ne', hg'⟩
      · refine ⟨hg.ne, ?_⟩
        rw [abs_of_pos (by linarith : 0 < 1 - g)]
        linarith
  have hD : Disjoint (positiveCutoff δ) (Iio 0) := by
    rw [Set.disjoint_left]
    intro g hg hn
    exact hg.1.not_gt hn
  rw [cutoffRealPlaceAdditive, hSet, setIntegral_union hD measurableSet_Iio
    ((positive_integral_change h δ).2.mpr hPos) ((negative_integral_change h).2.mpr hNeg),
    (positive_integral_change h δ).1, (negative_integral_change h).1]

/-- The cutoff in the multiplicative coordinate from (B.4.3.13) gives the
same finite part as the log cutoff for the full real-place kernel. -/
theorem real_place_finite_part_additive_cutoff (h : ℝ → ℝ)
    (hPos : Integrable (fun x ↦ h x * (Real.exp (x / 2) / |1 - Real.exp x|) -
      h 0 * (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x))
    (hNeg : Integrable (fun x ↦ h x * (Real.exp (x / 2) / (1 + Real.exp x)))) :
    let v := (∫ x, positiveKernel h x - h 0 * localPole x) + ∫ x, negativeKernel h x
    Tendsto (cutoffRealPlaceAdditive h) (𝓝[>] 0) (𝓝 v) ∧
    Tendsto (fun δ ↦ (∫ x in {x | δ < |x|}, positiveKernel h x + negativeKernel h x) +
        2 * h 0 * Real.log δ) (𝓝[>] 0) (𝓝 v) := by
  have hPos' : Integrable (fun x ↦ positiveKernel h x - h 0 * localPole x) := hPos
  have hNeg' : Integrable (negativeKernel h) := hNeg
  obtain ⟨hLog, hExp⟩ := real_place_cutoff_conventions_agree (positiveKernel h) (h 0) hPos'
  have hA : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < -Real.log (1 - δ) :=
    eventual_cutoff_radius_positive.mono fun _ hδ ↦ leftRadius_pos hδ.1 hδ.2
  have hB : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < Real.log (1 + δ) :=
    eventual_cutoff_radius_positive.mono fun _ hδ ↦ rightRadius_pos hδ.1
  have hPi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) :
      IntegrableOn (positiveKernel h) (exterior a b) := by
    have he : positiveKernel h = fun x ↦
        (positiveKernel h x - h 0 * localPole x) + h 0 * localPole x := by
      funext x
      exact (sub_add_cancel _ _).symm
    nth_rw 1 [he]
    exact hPos'.integrableOn.add ((integrableOn_localPole ha hb ha₁ hb₁).const_mul (h 0))
  constructor
  · refine (hExp.add tendsto_const_nhds).congr' ?_
    filter_upwards [eventual_cutoff_radius_positive, hA, hB, tendsto_leftRadius (gt_mem_nhds zero_lt_one),
      tendsto_rightRadius (gt_mem_nhds zero_lt_one)] with δ hδ ha hb ha₁ hb₁
    have hInt : IntegrableOn (positiveKernel h) (expCutoff δ) := by
      rw [expCutoff, ← exterior_logRadii hδ.1 hδ.2]
      exact hPi ha hb ha₁.le hb₁.le
    rw [realPlaceAdditive_eq hδ.2 hInt hNeg]
    unfold expCutoff
    ring
  · have hId : Tendsto (fun δ : ℝ ↦ δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hNegT : Tendsto (fun δ ↦ ∫ x in {x | δ < |x|}, negativeKernel h x)
        (𝓝[>] 0) (𝓝 (∫ x, negativeKernel h x)) := by
      simpa only [exterior_diagonal] using tendsto_setIntegral_exterior hId hId hNeg'
    refine (hLog.add hNegT).congr' ?_
    filter_upwards [eventual_cutoff_radius_positive] with δ hδ
    rw [← exterior_diagonal, integral_add (hPi hδ.1 hδ.1 hδ.2.le hδ.2.le) hNeg'.integrableOn]
    ring


/-- The ordinary real-variable cutoff has the same limit as the log
cutoff for the compact shrinking tests used in Chapter 13. -/
theorem shrinking_real_place_additive_tendsto {h : ℝ → ℝ} (hh : Measurable h)
    {R M L ε v : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hε : 0 < ε) (hsmall : R * ε ≤ 1 / 2)
    (hbound : ∀ x, |h x| ≤ M) (hsupport : ∀ x, R < |x| → h x = 0)
    (hLip : ∀ x, |x| ≤ 1 → |h x - h 0| ≤ L * |x|)
    (hlog : Tendsto (cutoffRealPlace (fun x ↦ h (x / ε))) (𝓝[>] 0) (𝓝 v)) :
    Tendsto (cutoffRealPlaceAdditive (fun x ↦ h (x / ε))) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨hPos, hNeg⟩ := integrable_shrinking_real_place_branches hh hR hM hL hε hsmall hbound
    hsupport hLip
  let hs : ℝ → ℝ := fun x ↦ h (x / ε)
  have hhs : Integrable (fun x ↦ hs x * (Real.exp (x / 2) / |1 - Real.exp x|) -
      hs 0 * (Icc (-1 : ℝ) 1).indicator (fun x : ℝ ↦ |x|⁻¹) x) := by
    simpa only [hs, zero_div] using hPos
  obtain ⟨hAdd, hLog'⟩ := real_place_finite_part_additive_cutoff hs hhs hNeg
  have heq : (fun x ↦ positiveKernel hs x + negativeKernel hs x) =
      fun x ↦ hs x * realPlaceKernel x := by
    funext x
    unfold positiveKernel negativeKernel
    change hs x * (Real.exp (x / 2) / |1 - Real.exp x|) +
      hs x * (Real.exp (x / 2) / (1 + Real.exp x)) =
      hs x * (Real.exp (x / 2) / |1 - Real.exp x| + Real.exp (x / 2) / (1 + Real.exp x))
    ring
  have hCtr : Tendsto (cutoffRealPlace hs) (𝓝[>] 0)
      (𝓝 ((∫ x, positiveKernel hs x - hs 0 * localPole x) + ∫ x, negativeKernel hs x)) := by
    refine hLog'.congr ?_
    intro δ
    rw [heq]
    rfl
  rw [tendsto_nhds_unique hlog hCtr]
  exact hAdd

/-- Translating the principal-value integral by one gives the same
finite-cutoff expression. Changing inclusion of the two boundary points
has no effect on Lebesgue integration. -/
theorem cutoffRealPlaceTranslated_eq (h : ℝ → ℝ) (δ : ℝ) :
    cutoffRealPlaceTranslated h δ = cutoffRealPlaceAdditive h δ := by
  let S : Set ℝ := {g | g ≠ 0 ∧ δ < |1 - g|}
  let T : Set ℝ := {x | δ < |x|}
  have hS : MeasurableSet S := (isClosed_singleton.measurableSet.compl).inter
    (isOpen_lt continuous_const (continuous_const.sub continuous_id).abs).measurableSet
  have hT : MeasurableSet T := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hae : {x : ℝ | δ ≤ |x|} =ᵐ[volume] T := by
    have h₁ : ∀ᵐ x : ℝ ∂volume, x ≠ δ := by simp [ae_iff]
    have h₂ : ∀ᵐ x : ℝ ∂volume, x ≠ -δ := by simp [ae_iff]
    filter_upwards [h₁, h₂] with x hx hx'
    change (δ ≤ |x|) = (δ < |x|)
    have hne : δ ≠ |x| := by
      intro he
      rcases le_or_gt 0 x with hpos | hneg
      · rw [abs_of_nonneg hpos] at he
        exact hx he.symm
      · rw [abs_of_neg hneg] at he
        exact hx' (by linarith)
    exact propext ⟨fun h ↦ lt_of_le_of_ne h hne, le_of_lt⟩
  unfold cutoffRealPlaceTranslated cutoffRealPlaceAdditive
  rw [setIntegral_congr_set hae, ← integral_indicator hT]
  change (∫ x, T.indicator (fun x ↦ shiftedRealRadialTest h x / |x|) x) +
      2 * h 0 * Real.log δ = (∫ g in S, rawKernel h g) + 2 * h 0 * Real.log δ
  rw [← integral_indicator hS]
  have he := integral_add_left_eq_self (μ := volume) (S.indicator (rawKernel h)) (1 : ℝ)
  rw [← he]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  change T.indicator (fun x ↦ shiftedRealRadialTest h x / |x|) x =
    S.indicator (rawKernel h) (1 + x)
  have heqAbs : |1 - (1 + x)| = |x| := by rw [show 1 - (1 + x) = -x by ring, abs_neg]
  have hmem : 1 + x ∈ S ↔ x ≠ -1 ∧ x ∈ T := by
    change (1 + x ≠ 0 ∧ δ < |1 - (1 + x)|) ↔ x ≠ -1 ∧ δ < |x|
    rw [heqAbs]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun hx ↦ h₁ (by linarith), h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun hx ↦ h₁ (by linarith), h₂⟩
  by_cases hx : x ∈ T
  · rw [indicator_of_mem hx]
    by_cases hz : x = -1
    · have hnot : 1 + x ∉ S := fun hm ↦ (hmem.mp hm).1 hz
      rw [indicator_of_notMem hnot, shiftedRealRadialTest, if_pos hz, zero_div]
    · rw [indicator_of_mem (hmem.mpr ⟨hz, hx⟩), shiftedRealRadialTest, if_neg hz, rawKernel, heqAbs]
  · have hnot : 1 + x ∉ S := fun hm ↦ hx (hmem.mp hm).2
    rw [indicator_of_notMem hx, indicator_of_notMem hnot]


end MasulloAudit

/- The discrete p-adic norm argument is adapted from the Apache-2.0 submission
by lll (41fd4c8f-fb18-4544-94b6-3abef11cea1b) on the rational prime-place trace. -/
namespace MasulloAudit.PadicUnits

variable {p : ℕ} [hp : Fact p.Prime]

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

/-- In `ℚ_[p]`, norms below `1` are at most `p⁻¹`. -/
lemma norm_le_inv_of_lt_one {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖x‖ ≤ (p : ℝ)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rw [Padic.norm_eq_zpow_neg_valuation h0] at hx ⊢
  have h1 : -x.valuation < 0 := by
    by_contra h
    push Not at h
    have := one_le_zpow₀ (one_lt_p (p := p)).le h
    linarith
  calc (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega)
    _ = (p : ℝ)⁻¹ := zpow_neg_one _

end MasulloAudit.PadicUnits

open MeasureTheory Metric Set

namespace MasulloAudit

/-- At a rational finite place a test supported at norms in `(1/2,2)`
is constant on the units and vanishes at every other norm. -/
private lemma short_radial_test_padic {p : ℕ} [hp : Fact p.Prime]
    (φ : ℝ → ℂ) (hφ : ∀ t : ℝ, t ≤ 1 / 2 ∨ 2 ≤ t → φ t = 0) (g : ℚ_[p]) :
    φ ‖g‖ * (Real.exp (-Real.log ‖g‖ / 2) : ℂ) =
      if ‖g‖ = 1 then φ 1 else 0 := by
  rcases lt_trichotomy ‖g‖ 1 with hlo | heq | hhi
  · have hle := PadicUnits.norm_le_inv_of_lt_one hlo
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    have hq := inv_le_inv₀ (PadicUnits.p_pos (p := p)) (show (0 : ℝ) < 2 by norm_num)
    have hnorm := hle.trans ((hq.mpr hp₂).trans_eq (by norm_num : (2 : ℝ)⁻¹ = 1 / 2))
    simp [hφ _ (Or.inl hnorm), hlo.ne]
  · simp [heq]
  · have hg : g ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hhi
      linarith
    have hn := Padic.norm_eq_zpow_neg_valuation hg
    have hval : (1 : ℤ) ≤ -g.valuation := by
      by_contra! h
      have hpow := zpow_le_zpow_right₀ (PadicUnits.one_lt_p (p := p)).le
        (show -g.valuation ≤ 0 by omega)
      rw [zpow_zero, ← hn] at hpow
      exact hhi.not_ge hpow
    have hpow := zpow_le_zpow_right₀ (PadicUnits.one_lt_p (p := p)).le hval
    rw [zpow_one, ← hn] at hpow
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    simp [hφ _ (Or.inr (hp₂.trans hpow)), hhi.ne']

/-- Every rational finite-place Connes–Weil contribution is zero for a
radial test supported at norms in `(1/2,2)`. In particular this applies to
the shrinking compact tests used to compare the terms of Chapter 13. -/
theorem padic_radial_principal_value_zero {p : ℕ} [Fact p.Prime]
    [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ] (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1)
    (φ : ℝ → ℂ) (hφ : ∀ t : ℝ, t ≤ 1 / 2 ∨ 2 ≤ t → φ t = 0) :
    let F : ℚ_[p] → ℂ := fun y ↦ (Real.log ‖y‖ : ℂ) *
      (∫ x, padicShiftedRadialTest φ x * (ψ (x * y) : ℂ) ∂μ)
    Integrable F μ ∧ (∫ y, F y ∂μ) = 0 := by
  have hF (y : ℚ_[p]) :
      (∫ x, padicShiftedRadialTest φ x * (ψ (x * y) : ℂ) ∂μ) =
        φ 1 * (∫ x in {x : ℚ_[p] | ‖1 + x‖ = 1}, (ψ (x * y) : ℂ) ∂μ) := by
    let U : Set ℚ_[p] := {x | ‖1 + x‖ = 1}
    have hU : MeasurableSet U :=
      (isClosed_eq (continuous_const.add continuous_id).norm continuous_const).measurableSet
    have heq : (fun x ↦ padicShiftedRadialTest φ x * (ψ (x * y) : ℂ)) =
        fun x ↦ φ 1 * U.indicator (fun z ↦ (ψ (z * y) : ℂ)) x := by
      funext x
      unfold padicShiftedRadialTest
      rw [short_radial_test_padic φ hφ]
      by_cases hx : x ∈ U
      · have heq : ‖1 + x‖ = 1 := hx
        rw [if_pos heq, indicator_of_mem hx]
      · have hne : ‖1 + x‖ ≠ 1 := hx
        rw [if_neg hne, indicator_of_notMem hx, zero_mul, mul_zero]
    rw [heq, integral_const_mul, integral_indicator hU]
  obtain ⟨hInt, hZero⟩ := MasulloRH.padic_unit_connes_principal_value_zero μ ψ hcont hψ hμ
  dsimp only
  simp_rw [hF]
  have hfun : (fun y ↦ (Real.log ‖y‖ : ℂ) * (φ 1 * (∫ x in {x : ℚ_[p] | ‖1 + x‖ = 1}, (ψ (x * y) : ℂ) ∂μ))) =
      fun y ↦ φ 1 * ((Real.log ‖y‖ : ℂ) * (∫ x in {x : ℚ_[p] | ‖1 + x‖ = 1}, (ψ (x * y) : ℂ) ∂μ)) := by
    funext y
    exact mul_left_comm _ _ _
  rw [hfun, integral_const_mul, hZero, mul_zero]
  exact ⟨hInt.const_mul (φ 1), rfl⟩


end MasulloAudit

/-!
# Chapter 13 of The Music of the Primes over the rationals

This file constructs a compactly supported smooth real test with mean zero
and nonnegative Fourier transform. Its shrinking logarithmic dilates obey
the rational norm-moment condition. For sufficiently small dilation the
capped critical-line sum is strictly below the two polar Mellin values
minus the unhalved real-place finite part in (13.3.1.4).

The statement uses scalar norm coordinates and includes both the symmetric
logarithmic cutoff and the additive cutoff used in Appendix B. It allows
any fixed multiple of the value at the real pole and proves vanishing at
each rational prime for the source’s conductor and Haar normalization.

Source: Alessandro Maria Masullo, The Music of the Primes, 20 November
2026 draft, pp. 519 and 522, equations (12.5.1.1) and (13.3.1.1)–(13.3.1.5).
The shrinking-test argument was identified in Calvin Yost-Wolff’s public
Prove2Me discussion of Theorem 13.3.1.1.
-/

/-!
# Compact mean-zero test with nonnegative Fourier transform

For the Chapter 13 rational normalization audit, use the autocorrelation
of a nonzero real compactly supported smooth function of mean zero.
The Fourier transform is the squared norm of the seed's transform.
Mathlib's Fourier kernel uses exp(-2π i x ξ).
-/

open MeasureTheory Filter Set Complex FourierTransform
open scoped SchwartzMap FourierTransform ComplexConjugate ContDiff

namespace MasulloAudit

private lemma fourier_real_neg_eq_conj (a : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun x ↦ (a x : ℂ)) (-ξ) = conj (𝓕 (fun x ↦ (a x : ℂ)) ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul, ← Complex.exp_conj,
    Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  congr 2
  push_cast
  ring

private lemma fourier_eval_zero_integral (g : ℝ → ℂ) : 𝓕 g 0 = ∫ x, g x := by
  simp [Real.fourier_real_eq]

private lemma integral_real_cast (f : ℝ → ℝ) :
    (∫ x, (f x : ℂ)) = Complex.ofReal (∫ x, f x) := by
  exact integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ)) (f := f)

/-- A compact autocorrelation test and its exact half-line Fourier mass. -/
theorem compact_test_of_real_seed (a : 𝓢(ℝ, ℝ))
    (ha : HasCompactSupport a) (hn : ∃ x : ℝ, a x ≠ 0) (hmean : ∫ x, a x = 0) :
    ∃ h F : 𝓢(ℝ, ℝ), HasCompactSupport h ∧ 0 < h 0 ∧ (∫ x, h x) = 0 ∧
      (∀ ξ : ℝ, 𝓕 (fun x ↦ (h x : ℂ)) ξ = (F ξ : ℂ)) ∧
      (∀ ξ : ℝ, 0 ≤ F ξ) ∧ Function.Even F ∧
      (2 * (∫ ξ in Ioi (0 : ℝ), F ξ)) = h 0 := by
  let aC := a.postcompCLM Complex.ofRealCLM
  let aR := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    ((LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv) aC
  let B := ContinuousLinearMap.mul ℂ ℂ
  let H := SchwartzMap.convolution B aC aR
  let h := H.postcompCLM Complex.reCLM
  let F := (𝓕 H).postcompCLM Complex.reCLM
  have haC (x : ℝ) : aC x = (a x : ℂ) := rfl
  have haR (x : ℝ) : aR x = (a (-x) : ℂ) := rfl
  have hsuppC : HasCompactSupport aC := ha.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)
  have hsuppR : HasCompactSupport aR := hsuppC.comp_homeomorph (Homeomorph.neg ℝ)
  have hHconv : (H : ℝ → ℂ) = MeasureTheory.convolution aC aR B volume :=
    funext fun x ↦ SchwartzMap.convolution_apply B aC aR x
  have hsuppH : HasCompactSupport H := by
    rw [hHconv]
    exact hsuppC.convolution B hsuppR
  have hSup : HasCompactSupport h := hsuppH.comp_left (g := Complex.re) Complex.zero_re
  have hHval (x : ℝ) : H x = Complex.ofReal (∫ t : ℝ, a t * a (t - x)) := by
    calc
      H x = ∫ t : ℝ, (↑(a t * a (t - x)) : ℂ) := by
        rw [show H x = MeasureTheory.convolution aC aR B volume x from congrFun hHconv x,
          MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards with t
        change aC t * aR (x - t) = (↑(a t * a (t - x)) : ℂ)
        rw [haC, haR, neg_sub, Complex.ofReal_mul]
      _ = _ := integral_real_cast _
  have hh : (fun x ↦ (h x : ℂ)) = (H : ℝ → ℂ) := by
    funext x
    change ((H x).re : ℂ) = H x
    rw [hHval]
    simp
  have hpos : 0 < h 0 := by
    obtain ⟨x, hx⟩ := hn
    have hp : 0 < ∫ t : ℝ, a t * a t :=
      (a.continuous.mul a.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        ha.mul_right (fun t ↦ mul_self_nonneg (a t)) (mul_ne_zero hx hx)
    change 0 < (H 0).re
    rw [hHval]
    simpa using hp
  have hA (ξ : ℝ) : 𝓕 aR ξ = conj (𝓕 aC ξ) := by
    have hx := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (aC : ℝ → ℂ) ξ
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    change 𝓕 (fun x ↦ (a (-x) : ℂ)) ξ = conj (𝓕 (fun x ↦ (a x : ℂ)) ξ)
    exact hx.trans (fourier_real_neg_eq_conj a ξ)
  have hsquare (ξ : ℝ) : 𝓕 H ξ = (‖𝓕 aC ξ‖ ^ 2 : ℝ) := by
    dsimp only [H]
    rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
    change (𝓕 aC ξ) * (𝓕 aR ξ) = _
    rw [hA, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hF (ξ : ℝ) : F ξ = ‖𝓕 aC ξ‖ ^ 2 := by
    change (𝓕 H ξ).re = _
    rw [hsquare, Complex.ofReal_re]
  have hFnon (ξ : ℝ) : 0 ≤ F ξ := by rw [hF]; positivity
  have hFeven : Function.Even F := by
    intro ξ
    rw [hF, hF, SchwartzMap.fourier_coe]
    change ‖𝓕 (fun x ↦ (a x : ℂ)) (-ξ)‖ ^ 2 = ‖𝓕 (fun x ↦ (a x : ℂ)) ξ‖ ^ 2
    rw [fourier_real_neg_eq_conj, Complex.norm_conj]
  have hFourier (ξ : ℝ) : 𝓕 (fun x ↦ (h x : ℂ)) ξ = (F ξ : ℂ) := by
    rw [hh, ← SchwartzMap.fourier_coe, hsquare, hF]
  have haZero : 𝓕 aC 0 = 0 := by
    rw [SchwartzMap.fourier_coe, fourier_eval_zero_integral]
    change (∫ x, (a x : ℂ)) = 0
    calc
      _ = (↑(∫ x, a x) : ℂ) := integral_real_cast a
      _ = _ := by rw [hmean, Complex.ofReal_zero]
  have hhInt : (∫ x, h x) = 0 := by
    have hzero : 𝓕 (fun x ↦ (h x : ℂ)) 0 = 0 := by
      rw [hh, ← SchwartzMap.fourier_coe, hsquare, haZero]
      simp
    apply Complex.ofReal_eq_zero.mp
    exact (integral_real_cast h).symm.trans ((fourier_eval_zero_integral _).symm.trans hzero)
  have hInv : (∫ ξ, F ξ) = h 0 := by
    have hi := congrArg (fun t : 𝓢(ℝ, ℂ) ↦ t 0) (FourierPair.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) H)
    change 𝓕⁻ (𝓕 H) 0 = H 0 at hi
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
      fourier_eval_zero_integral] at hi
    have hs (ξ : ℝ) : 𝓕 H ξ = (F ξ : ℂ) := by rw [hsquare, hF]
    simp_rw [hs, integral_real_cast] at hi
    exact congrArg Complex.re hi
  have hHalf : (∫ ξ, F ξ) = 2 * (∫ ξ in Ioi (0 : ℝ), F ξ) := by
    rw [← integral_comp_abs]
    apply integral_congr_ae
    filter_upwards with x
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx.le, hFeven]
  exact ⟨h, F, hSup, hpos, hhInt, hFourier, hFnon, hFeven, hHalf.symm.trans hInv⟩


/-- A compactly supported smooth test satisfying the moment condition and
having a nonnegative even real Fourier transform. -/
theorem exists_compact_mean_zero_test_with_nonnegative_fourier :
    ∃ h F : 𝓢(ℝ, ℝ), HasCompactSupport h ∧ 0 < h 0 ∧ (∫ x, h x) = 0 ∧
      (∀ ξ : ℝ, 𝓕 (fun x ↦ (h x : ℂ)) ξ = (F ξ : ℂ)) ∧
      (∀ ξ : ℝ, 0 ≤ F ξ) ∧ Function.Even F ∧
      (2 * (∫ ξ in Ioi (0 : ℝ), F ξ)) = h 0 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let b : 𝓢(ℝ, ℝ) := bump.hasCompactSupport.toSchwartzMap bump.contDiff
  let a : 𝓢(ℝ, ℝ) := SchwartzMap.derivCLM ℝ ℝ b
  have ha : HasCompactSupport a := by
    change HasCompactSupport (deriv (b : ℝ → ℝ))
    exact bump.hasCompactSupport.deriv
  have hd (x : ℝ) : HasDerivAt b (a x) x := b.hasDerivAt x
  have hBot := b.tendsto_cocompact.mono_left atBot_le_cocompact
  have hTop := b.tendsto_cocompact.mono_left atTop_le_cocompact
  have hmean : ∫ x, a x = 0 := by
    simpa using integral_of_hasDerivAt_of_tendsto hd a.integrable hBot hTop
  have hb0 : b 0 = 1 := by
    change bump 0 = 1
    apply bump.one_of_mem_closedBall
    simp [bump]
  have hb3 : b 3 = 0 := by
    change bump 3 = 0
    apply bump.zero_of_le_dist
    norm_num [bump, Real.dist_eq]
  have hn : ∃ x : ℝ, a x ≠ 0 := by
    by_contra! hz
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := 3) (fun x _ ↦ hd x) (a.continuous.intervalIntegrable 0 3)
    rw [hb3, hb0] at h
    simp [hz] at h
  exact compact_test_of_real_seed a ha hn hmean

end MasulloAudit


/-!
# Mellin transform of a shrinking logarithmic test

This gives the exact Fourier normalization for the zeta spectral terms
and a uniform bound on the two real polar terms in the Chapter 13 audit.
-/

open MeasureTheory Complex FourierTransform Set
open scoped SchwartzMap FourierTransform

namespace MasulloAudit

/-- The positive norm test obtained from h(log t / ε), extended by zero. -/


private lemma fourier_dilate_negative (g : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    𝓕 (fun u ↦ g (-u / ε)) ξ = ε • 𝓕 g (-ε * ξ) := by
  let G : ℝ → ℂ := fun x ↦ Real.fourierChar (-(x * (-ε * ξ))) • g x
  have hg (u : ℝ) : Real.fourierChar (-(u * ξ)) • g (-u / ε) = G (-u / ε) := by
    have he : -(u * ξ) = -((-u / ε) * (-ε * ξ)) := by
      field_simp [hε.ne']
    rw [he]
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  simp_rw [hg]
  calc
    (∫ u, G (-u / ε)) = ∫ u, G (u / ε) :=
      integral_neg_eq_self (fun u : ℝ ↦ G (u / ε)) volume
    _ = _ := by rw [Measure.integral_comp_div, abs_of_pos hε]

/-- Exact Mellin-to-Fourier change of variable for the logarithmic dilation. -/
theorem mellin_shrinkingRadialTest (h : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    mellin (shrinkingRadialTest h ε) s = ε •
      𝓕 (fun x ↦ Real.exp (s.re * ε * x) • (h x : ℂ)) (-ε * (s.im / (2 * Real.pi))) := by
  let g : ℝ → ℂ := fun x ↦ Real.exp (s.re * ε * x) • (h x : ℂ)
  rw [mellin_eq_fourier]
  have he : (fun u : ℝ ↦ Real.exp (-s.re * u) • shrinkingRadialTest h ε (Real.exp (-u))) =
      fun u ↦ g (-u / ε) := by
    funext u
    rw [shrinkingRadialTest, if_pos (Real.exp_pos _), Real.log_exp]
    dsimp only [g]
    have harg : -s.re * u = s.re * ε * (-u / ε) := by field_simp [hε.ne']
    rw [harg]
  rw [he, fourier_dilate_negative g hε]

/-- On the imaginary axis the Mellin value is the dilated Fourier weight. -/
theorem mellin_shrinkingRadialTest_im (h F : ℝ → ℝ)
    (hF : ∀ ξ : ℝ, 𝓕 (fun x ↦ (h x : ℂ)) ξ = (F ξ : ℂ)) (hEven : Function.Even F)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) :
    mellin (shrinkingRadialTest h ε) ((γ : ℂ) * I) =
      ((ε * F (ε * γ / (2 * Real.pi)) : ℝ) : ℂ) := by
  rw [mellin_shrinkingRadialTest h hε]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, add_zero, sub_zero, zero_mul, Real.exp_zero, one_smul]
  rw [hF, show -ε * (γ / (2 * Real.pi)) = -(ε * γ / (2 * Real.pi)) by ring, hEven]
  exact (Complex.ofReal_mul _ _).symm

/-- The values of the Mellin transform at fixed real parameters are O(ε). -/
theorem norm_mellin_shrinkingRadialTest_real_le (h : 𝓢(ℝ, ℝ)) {R ε : ℝ}
    (_hR : 0 ≤ R) (hSupport : ∀ x : ℝ, R < |x| → h x = 0)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (s : ℝ) :
    ‖mellin (shrinkingRadialTest h ε) (s : ℂ)‖ ≤
      ε * Real.exp (|s| * R) * (∫ x, |h x|) := by
  rw [mellin_shrinkingRadialTest h hε]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_div, mul_zero]
  rw [show 𝓕 (fun x ↦ Real.exp (s * ε * x) • (h x : ℂ)) 0 =
      ∫ x, Real.exp (s * ε * x) • (h x : ℂ) by simp [Real.fourier_real_eq] ]
  have hi : Integrable (fun x : ℝ ↦ Real.exp (|s| * R) * |h x|) := by
    simpa only [Real.norm_eq_abs] using h.integrable.norm.const_mul (Real.exp (|s| * R))
  have he : ∀ᵐ x : ℝ ∂volume,
      ‖Real.exp (s * ε * x) • (h x : ℂ)‖ ≤ Real.exp (|s| * R) * |h x| := by
    filter_upwards with x
    by_cases hx : |x| ≤ R
    · have hprod : s * ε * x ≤ |s| * R := by
        calc
          _ ≤ |s * ε * x| := le_abs_self _
          _ = |s| * ε * |x| := by rw [abs_mul, abs_mul, abs_of_pos hε]
          _ ≤ |s| * 1 * R := by gcongr
          _ = _ := by ring
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_real,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hprod) (abs_nonneg _)
    · simp [hSupport x (lt_of_not_ge hx)]
  have hB := norm_integral_le_of_norm_le hi he
  rw [integral_const_mul] at hB
  rw [norm_smul, Real.norm_of_nonneg hε.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left hB hε.le

end MasulloAudit


/-!
# Upper bound for the capped rational critical-line spectrum

The degree of the rational field is one, so each spectral multiplicity in
(13.3.1.3) is one. Distinct critical zeros in the upper and lower half-planes
can each be compared with the full positive-ordinate weighted count.
-/

open MeasureTheory Filter Set Complex
open scoped SchwartzMap ComplexConjugate

namespace MasulloAudit

private abbrev PositiveZetaZeros :=
  {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im}

private lemma critical_nontrivial (ρ : CriticalZetaZeroSet) :
    Zeta23.IsNontrivialZero ρ.val := by
  refine ⟨ρ.property.2, ?_, ?_⟩
  · rw [ρ.property.1]
    norm_num
  · rw [ρ.property.1]
    norm_num

private lemma critical_conj (ρ : CriticalZetaZeroSet) :
    (conj ρ.val) ∈ CriticalZetaZeroSet := by
  refine ⟨by simpa using ρ.property.1, ?_⟩
  rw [riemannZeta_conj, ρ.property.2, map_zero]

private lemma finite_sum_le_of_embedding {ι κ : Type*} (S : Finset ι) (e : (↥S) ↪ κ)
    {f : ι → ℝ} {g : κ → ℝ} (hg : Summable g) (hpos : ∀ y, 0 ≤ g y)
    (hle : ∀ x : (↥S), f x.val ≤ g (e x)) :
    (∑ x ∈ S, f x) ≤ ∑' y, g y := by
  classical
  calc
    _ = ∑ x ∈ S.attach, f x.val := (Finset.sum_attach S f).symm
    _ ≤ ∑ x ∈ S.attach, g (e x) := Finset.sum_le_sum (fun x _ ↦ hle x)
    _ = ∑ y ∈ S.attach.map e, g y := (Finset.sum_map S.attach e g).symm
    _ ≤ _ := hg.sum_le_tsum _ (fun y _ ↦ hpos y)

private lemma capped_critical_trace_le_two_full_positive (F : ℝ → ℝ)
    (hpos : ∀ x, 0 ≤ F x) (hEven : Function.Even F) (hF0 : F 0 = 0) (δ : ℝ)
    (hs : Summable (fun ρ : PositiveZetaZeros ↦ (Zeta23.zeroMult ρ.val : ℝ) * F (δ * ρ.val.im))) :
    Summable (fun ρ : CriticalZetaZeroSet ↦ F (δ * ρ.val.im)) ∧
      (∑' ρ : CriticalZetaZeroSet, F (δ * ρ.val.im)) ≤
        2 * ∑' ρ : PositiveZetaZeros, (Zeta23.zeroMult ρ.val : ℝ) * F (δ * ρ.val.im) := by
  classical
  let f : CriticalZetaZeroSet → ℝ := fun ρ ↦ F (δ * ρ.val.im)
  let g : PositiveZetaZeros → ℝ := fun ρ ↦ (Zeta23.zeroMult ρ.val : ℝ) * F (δ * ρ.val.im)
  have hg (ρ : PositiveZetaZeros) : 0 ≤ g ρ :=
    mul_nonneg (Nat.cast_nonneg _) (hpos _)
  have hone (ρ : PositiveZetaZeros) : F (δ * ρ.val.im) ≤ g ρ := by
    apply le_mul_of_one_le_left (hpos _)
    exact_mod_cast Zeta23.ZetaSeam.one_le_mult_holds ρ.val ρ.property.1
  have hS (S : Finset CriticalZetaZeroSet) : (∑ ρ ∈ S, f ρ) ≤ 2 * ∑' ρ, g ρ := by
    let Spos := S.filter (fun ρ ↦ 0 < ρ.val.im)
    let Sneg := (S.filter (fun ρ ↦ ¬ 0 < ρ.val.im)).filter (fun ρ ↦ ρ.val.im < 0)
    let Szero := (S.filter (fun ρ ↦ ¬ 0 < ρ.val.im)).filter (fun ρ ↦ ¬ ρ.val.im < 0)
    let ep : (↥Spos) ↪ PositiveZetaZeros :=
      ⟨fun ρ ↦ ⟨ρ.val.val, critical_nontrivial ρ.val, (Finset.mem_filter.mp ρ.property).2⟩,
        fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun z : PositiveZetaZeros ↦ z.val) h))⟩
    let en : (↥Sneg) ↪ PositiveZetaZeros :=
      ⟨fun ρ ↦ ⟨conj ρ.val.val, critical_nontrivial ⟨conj ρ.val.val, critical_conj ρ.val⟩, by
          rw [Complex.conj_im]
          exact neg_pos.mpr (Finset.mem_filter.mp ρ.property).2⟩,
        fun _ _ h ↦ Subtype.ext (Subtype.ext ((starRingEnd ℂ).injective (congrArg Subtype.val h)))⟩
    have hp : (∑ ρ ∈ Spos, f ρ) ≤ ∑' ρ, g ρ :=
      finite_sum_le_of_embedding Spos ep hs hg (fun ρ ↦ hone (ep ρ))
    have hn : (∑ ρ ∈ Sneg, f ρ) ≤ ∑' ρ, g ρ := by
      apply finite_sum_le_of_embedding Sneg en hs hg
      intro ρ
      have he : F (δ * (en ρ).val.im) = f ρ.val := by
        change F (δ * (conj ρ.val.val).im) = F (δ * ρ.val.val.im)
        rw [Complex.conj_im, mul_neg, hEven]
      exact he ▸ hone (en ρ)
    have hz : (∑ ρ ∈ Szero, f ρ) = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      have h₁ : ¬ ρ.val.im < 0 := (Finset.mem_filter.mp hρ).2
      have h₂ : ¬ 0 < ρ.val.im := (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2
      have he : ρ.val.im = 0 := le_antisymm (le_of_not_gt h₂) (le_of_not_gt h₁)
      simp [f, he, hF0]
    have hsplit : (∑ ρ ∈ S, f ρ) = (∑ ρ ∈ Spos, f ρ) + (∑ ρ ∈ Sneg, f ρ) := by
      have hs₁ := Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ 0 < ρ.val.im) f
      have hs₂ := Finset.sum_filter_add_sum_filter_not (S.filter (fun ρ ↦ ¬ 0 < ρ.val.im))
        (fun ρ ↦ ρ.val.im < 0) f
      change (∑ ρ ∈ Spos, f ρ) + (∑ ρ ∈ S.filter (fun ρ ↦ ¬ 0 < ρ.val.im), f ρ) =
        ∑ ρ ∈ S, f ρ at hs₁
      change (∑ ρ ∈ Sneg, f ρ) + (∑ ρ ∈ Szero, f ρ) =
        ∑ ρ ∈ S.filter (fun ρ ↦ ¬ 0 < ρ.val.im), f ρ at hs₂
      rw [← hs₁, ← hs₂, hz, add_zero]
    rw [hsplit, two_mul]
    exact add_le_add hp hn
  exact ⟨summable_of_sum_le (fun ρ ↦ hpos _) hS,
    Real.tsum_le_of_sum_le (fun ρ ↦ hpos _) hS⟩

/-- Uniform upper bound on the rational critical-line trace with multiplicities capped at one. -/
theorem rational_capped_spectral_log_upper (F : 𝓢(ℝ, ℝ)) (hpos : ∀ x, 0 ≤ F x)
    (hEven : Function.Even F) (hF0 : F 0 = 0) (v : ℝ)
    (hv : 2 * (∫ x in Ioi (0 : ℝ), F x) = v) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Summable (fun ρ : CriticalZetaZeroSet ↦ F (ε * ρ.val.im / (2 * Real.pi))) ∧
      ε * (∑' ρ : CriticalZetaZeroSet, F (ε * ρ.val.im / (2 * Real.pi))) ≤
        v * Real.log ε⁻¹ + B := by
  let q := 2 * Real.pi
  have hq : 0 < q := by unfold q; positivity
  have hq₁ : 1 ≤ q := by unfold q; linarith [Real.pi_gt_three]
  obtain ⟨C, _hC, hC⟩ := MasulloRH.weighted_positive_zeta_zeros_schwartz_scaling F
  refine ⟨v * Real.log q + 2 * q * C, fun ε hε hε₁ ↦ ?_⟩
  let δ := ε / q
  have hδ : 0 < δ := div_pos hε hq
  have hδ₁ : δ ≤ 1 := (div_le_one_of_le₀ (hε₁.trans hq₁) hq.le)
  obtain ⟨hS, hB⟩ := hC δ hδ hδ₁
  obtain ⟨hSp, hBcrit⟩ := capped_critical_trace_le_two_full_positive F hpos hEven hF0 δ hS
  have hδeval (x : ℝ) : δ * x = ε * x / (2 * Real.pi) := by unfold δ q; ring
  have hεq : ε = q * δ := by unfold δ; field_simp
  have hlog : Real.log δ⁻¹ = Real.log ε⁻¹ + Real.log q := by
    unfold δ
    rw [Real.log_inv, Real.log_div hε.ne' hq.ne', Real.log_inv]
    ring
  have hupper := (abs_le.mp hB).2
  have hqδ : 2 * q * δ * (∑' ρ : PositiveZetaZeros, (Zeta23.zeroMult ρ.val : ℝ) *
      F (δ * ρ.val.im)) ≤ v * Real.log ε⁻¹ + (v * Real.log q + 2 * q * C) := by
    have he := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 2 * q by positivity)
    have hm : 2 * q * ((1 / (2 * Real.pi)) * Real.log δ⁻¹ *
        (∫ x in Ioi (0 : ℝ), F x)) = v * Real.log δ⁻¹ := by
      rw [← hv]
      unfold q
      field_simp
    have ha : 2 * q * (δ * (∑' ρ : PositiveZetaZeros,
        (Zeta23.zeroMult ρ.val : ℝ) * F (δ * ρ.val.im)) -
        (1 / (2 * Real.pi)) * Real.log δ⁻¹ * (∫ x in Ioi (0 : ℝ), F x)) =
        2 * q * δ * (∑' ρ : PositiveZetaZeros, (Zeta23.zeroMult ρ.val : ℝ) *
          F (δ * ρ.val.im)) - v * Real.log δ⁻¹ := by
      rw [mul_sub, hm]
      ring
    rw [ha, hlog, mul_add] at he
    linarith
  refine ⟨by simpa only [hδeval] using hSp, ?_⟩
  simp_rw [← hδeval]
  calc
    _ ≤ ε * (2 * ∑' ρ : PositiveZetaZeros,
        (Zeta23.zeroMult ρ.val : ℝ) * F (δ * ρ.val.im)) :=
      mul_le_mul_of_nonneg_left hBcrit hε.le
    _ = 2 * q * δ * (∑' ρ : PositiveZetaZeros,
        (Zeta23.zeroMult ρ.val : ℝ) * F (δ * ρ.val.im)) := by
      rw [hεq]
      ring
    _ ≤ _ := hqδ

end MasulloAudit


/-!
# Failure of the unhalved real term in the rational scalar model

The capped critical spectrum is smaller than the two polar terms minus
the unhalved real finite part for the shrinking tests below. The real
finite part is in the symmetric logarithmic cutoff convention. Any fixed
multiple of the value at the pole can be added without changing the
conclusion. These tests vanish at every positive norm outside (1/2,2).
-/

open MeasureTheory Filter Set Complex FourierTransform
open scoped SchwartzMap FourierTransform Topology NNReal

namespace MasulloAudit

private lemma compact_schwartz_bounds (h : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport h) :
    ∃ R M L : ℝ, 0 < R ∧ 0 ≤ M ∧ 0 ≤ L ∧
      (∀ x : ℝ, |h x| ≤ M) ∧ (∀ x : ℝ, R < |x| → h x = 0) ∧
      (∀ x : ℝ, |h x - h 0| ≤ L * |x|) := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hc.isBounded
  let R := max R₀ 1
  let M := SchwartzMap.seminorm ℝ 0 0 h
  let d := SchwartzMap.derivCLM ℝ ℝ h
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 d, apply_nonneg _ _⟩
  have hL : LipschitzWith L h := by
    apply lipschitzWith_of_nnnorm_deriv_le h.differentiable
    intro x
    change ‖deriv (h : ℝ → ℝ) x‖ ≤ (L : ℝ)
    exact SchwartzMap.norm_le_seminorm ℝ d x
  refine ⟨R, M, L, zero_lt_one.trans_le (le_max_right _ _), apply_nonneg _ _, L.coe_nonneg,
    fun x ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_⟩
  · exact SchwartzMap.norm_le_seminorm ℝ h x
  · by_contra! hx0
    have hball := hR₀ (subset_tsupport h hx0)
    have hle : |x| ≤ R₀ := by simpa [Metric.mem_closedBall, Real.dist_eq] using hball
    exact (not_le_of_gt hx) (hle.trans (le_max_left _ _))
  · simpa [Real.dist_eq] using hL.dist_le_mul x 0

private lemma outside_small_norm_support {h : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε)
    (hSupport : ∀ x : ℝ, R < |x| → h x = 0) (hsmall : R * ε < Real.log 2)
    {t : ℝ} (ht : 0 < t) (hOutside : t ≤ 1 / 2 ∨ 2 ≤ t) :
    shrinkingRadialTest h ε t = 0 := by
  have hlog : Real.log 2 ≤ |Real.log t| := by
    rcases hOutside with h | h
    · have hi := Real.log_le_log ht h
      rw [one_div, Real.log_inv] at hi
      linarith [neg_le_abs (Real.log t)]
    · exact (Real.log_le_log (by norm_num) h).trans (le_abs_self _)
  have harg : R < |Real.log t / ε| := by
    rw [abs_div, abs_of_pos hε]
    exact (lt_div_iff₀ hε).2 (hsmall.trans_le hlog)
  simp [shrinkingRadialTest, ht, hSupport _ harg]

private lemma rationalCappedSpectralTerm_eq (h F : ℝ → ℝ)
    (hF : ∀ ξ : ℝ, 𝓕 (fun x ↦ (h x : ℂ)) ξ = (F ξ : ℂ)) (hEven : Function.Even F)
    {ε : ℝ} (hε : 0 < ε) (ρ : CriticalZetaZeroSet) :
    rationalCappedSpectralTerm h ε ρ = ε * F (ε * ρ.val.im / (2 * Real.pi)) := by
  have hNz : Zeta23.IsNontrivialZero ρ.val := by
    refine ⟨ρ.property.2, ?_, ?_⟩ <;> rw [ρ.property.1] <;> norm_num
  have hm : 1 ≤ analyticOrderNatAt riemannZeta ρ.val := Zeta23.ZetaSeam.one_le_mult_holds _ hNz
  have he : ρ.val - (1 / 2 : ℂ) = (ρ.val.im : ℂ) * I := by
    apply Complex.ext <;> simp [ρ.property.1]
  rw [rationalCappedSpectralTerm, min_eq_right hm, he,
    mellin_shrinkingRadialTest_im h F hF hEven hε, Complex.ofReal_re, Nat.cast_one, one_mul]

private lemma polarPair_lower (h : 𝓢(ℝ, ℝ)) {R ε : ℝ} (hR : 0 ≤ R)
    (hSupport : ∀ x : ℝ, R < |x| → h x = 0) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    -(2 * (Real.exp (R / 2) * (∫ x, |h x|))) ≤ rationalPolarPair h ε := by
  let P := Real.exp (R / 2) * (∫ x, |h x|)
  have hP : 0 ≤ P := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun x ↦ abs_nonneg (h x))
  have hbound (s : ℝ) (hs : |s| = 1 / 2) :
      ‖mellin (shrinkingRadialTest h ε) (s : ℂ)‖ ≤ P := by
    have hN := norm_mellin_shrinkingRadialTest_real_le h hR hSupport hε hε₁ s
    rw [hs, show 1 / 2 * R = R / 2 by ring, mul_assoc] at hN
    exact hN.trans (mul_le_of_le_one_left hP hε₁)
  have h₁ := (abs_le.mp (Complex.abs_re_le_norm
    (mellin (shrinkingRadialTest h ε) (1 / 2 : ℂ)))).1
  have h₂ := (abs_le.mp (Complex.abs_re_le_norm
    (mellin (shrinkingRadialTest h ε) (-1 / 2 : ℂ)))).1
  have hb₁ := hbound (1 / 2) (by norm_num)
  have hb₂ := hbound (-1 / 2) (by norm_num)
  push_cast at hb₁ hb₂
  rw [rationalPolarPair, Complex.add_re]
  change -(2 * P) ≤ _
  linarith

/-- A shrinking compact mean-zero test violates the unhalved archimedean scalar identity.
The constant k allows for a fixed change of the real finite-part normalization. -/
theorem exists_violation_of_unhalved_rational_trace_model :
    ∃ h : 𝓢(ℝ, ℝ), HasCompactSupport h ∧ 0 < h 0 ∧ (∫ x, h x) = 0 ∧
      ∀ k : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
        (∀ t : ℝ, 0 < t → (t ≤ 1 / 2 ∨ 2 ≤ t) → shrinkingRadialTest h ε t = 0) ∧
        Summable (rationalCappedSpectralTerm h ε) ∧
        ∃ v : ℝ, Tendsto (cutoffRealPlace (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
          (∑' ρ, rationalCappedSpectralTerm h ε ρ) <
            rationalPolarPair h ε - (v + k * h 0) := by
  obtain ⟨h, F, hCompact, h0, hMean, hF, hFnon, hEven, hMass⟩ :=
    exists_compact_mean_zero_test_with_nonnegative_fourier
  obtain ⟨R, M, L, hR, hM, hL, hBound, hSupport, hLip⟩ := compact_schwartz_bounds h hCompact
  have hF0 : F 0 = 0 := by
    have hEq := hF 0
    have heq : 𝓕 (fun x ↦ (h x : ℂ)) 0 = Complex.ofReal (∫ x, h x) := by
      rw [show 𝓕 (fun x ↦ (h x : ℂ)) 0 = (∫ x, (h x : ℂ)) by simp [Real.fourier_real_eq] ]
      exact integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ)) (f := (h : ℝ → ℝ))
    rw [heq, hMean, Complex.ofReal_zero] at hEq
    exact Complex.ofReal_eq_zero.mp hEq.symm
  obtain ⟨B, hB⟩ := rational_capped_spectral_log_upper F hFnon hEven hF0 (h 0) hMass
  refine ⟨h, hCompact, h0, hMean, fun k ↦ ?_⟩
  let A := ∫ x, subtractedRealPole h x
  let P := Real.exp (R / 2) * (∫ x, |h x|)
  let D := (B + 2 * P + A + 10 * M * R + k * h 0) / h 0
  let η := min (min 1 (1 / (2 * R))) (min (Real.log 2 / R) (Real.exp (-D)))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hη : 0 < η := by unfold η; positivity
  refine ⟨η, hη, fun ε hε hεη ↦ ?_⟩
  have hsmall₁ : ε < min 1 (1 / (2 * R)) := hεη.trans_le (min_le_left _ _)
  have hsmall₂ : ε < min (Real.log 2 / R) (Real.exp (-D)) := hεη.trans_le (min_le_right _ _)
  have hε₁ : ε ≤ 1 := (hsmall₁.trans_le (min_le_left _ _)).le
  have hRsmall : R * ε ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * R)).mp
      (hsmall₁.trans_le (min_le_right _ _)).le
    nlinarith
  have hRlog : R * ε < Real.log 2 := by
    have hi := (lt_div_iff₀ hR).mp (hsmall₂.trans_le (min_le_left _ _))
    simpa [mul_comm] using hi
  have hLbig : D < Real.log ε⁻¹ := by
    have he := Real.log_lt_log hε (hsmall₂.trans_le (min_le_right _ _))
    rw [Real.log_exp] at he
    rw [Real.log_inv]
    linarith
  have hlarge : B + 2 * P + A + 10 * M * R + k * h 0 < h 0 * Real.log ε⁻¹ := by
    have hh := mul_lt_mul_of_pos_right hLbig h0
    unfold D at hh
    rw [div_mul_cancel₀ _ h0.ne'] at hh
    simpa [mul_comm] using hh
  obtain ⟨hTs, hSb⟩ := hB ε hε hε₁
  have hterm := rationalCappedSpectralTerm_eq h F hF hEven hε
  have hSumm : Summable (rationalCappedSpectralTerm h ε) :=
    (hTs.mul_left ε).congr fun ρ ↦ (hterm ρ).symm
  have hSpectral : (∑' ρ, rationalCappedSpectralTerm h ε ρ) ≤ h 0 * Real.log ε⁻¹ + B := by
    simp_rw [hterm, tsum_mul_left]
    exact hSb
  obtain ⟨v, hv, hvB⟩ := real_place_finite_part_log_scaling h.continuous.measurable hR.le hM hL
    hε hRsmall hBound hSupport (fun x _ ↦ hLip x)
  have harch := (abs_le.mp hvB).2
  have harchb : v ≤ A + 2 * h 0 * Real.log ε + 10 * M * R := by
    have hle : 10 * M * R * ε ≤ 10 * M * R := mul_le_of_le_one_right (by positivity) hε₁
    change v - (A + 2 * h 0 * Real.log ε) ≤ 10 * M * R * ε at harch
    linarith
  have hpolar : -(2 * P) ≤ rationalPolarPair h ε := polarPair_lower h hR.le hSupport hε hε₁
  refine ⟨fun t ht hout ↦ outside_small_norm_support hε hSupport hRlog ht hout, hSumm, v, hv, ?_⟩
  rw [Real.log_inv] at hlarge hSpectral
  linarith


/-- Radial rational idelic tests automatically satisfy the degree-one
moment condition (13.3.1.2). After canceling the norm character at the
indicated Mellin parameter, the norm-one integral contributes a fixed
scalar. The remaining logarithmic moment is zero. -/
theorem shrinking_radial_norm_moment_zero (h : 𝓢(ℝ, ℝ))
    (hMean : (∫ x, h x) = 0) {ε : ℝ} (hε : 0 < ε) (c : ℂ) :
    c * mellin (shrinkingRadialTest h ε) 0 = 0 := by
  rw [mellin_shrinkingRadialTest h hε]
  have hIntegral : (∫ x : ℝ, (h x : ℂ)) = 0 := by
    rw [integral_complex_ofReal, hMean, ofReal_zero]
  simp [Real.fourier_real_eq, hIntegral]

/-- For a shrinking compact test, the unhalved formula in (13.3.1.3–5)
fails over the rationals when the real place is computed using the
actual additive cutoff of (B.4.3.13). Any fixed finite part constant
times the value at the pole is allowed. At every rational prime the
finite-place logarithmic Fourier integral is zero. -/
theorem exists_violation_of_unhalved_rational_trace_additive_cutoff :
    ∃ h : 𝓢(ℝ, ℝ), HasCompactSupport h ∧ 0 < h 0 ∧ (∫ x, h x) = 0 ∧
      ∀ k : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
        (∀ t : ℝ, t ≤ 1 / 2 ∨ 2 ≤ t → shrinkingRadialTest h ε t = 0) ∧
        Summable (rationalCappedSpectralTerm h ε) ∧
        (∀ (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
            (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[p] Circle),
          Continuous ψ → (∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) →
          μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1 →
          let F : ℚ_[p] → ℂ := fun y ↦ (Real.log ‖y‖ : ℂ) *
            (∫ x, padicShiftedRadialTest (shrinkingRadialTest h ε) x * (ψ (x * y) : ℂ) ∂μ)
          Integrable F μ ∧ (∫ y, F y ∂μ) = 0) ∧
        ∃ v : ℝ, Tendsto (cutoffRealPlaceTranslated (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
          (∑' ρ, rationalCappedSpectralTerm h ε ρ) <
            rationalPolarPair h ε - (v + k * h 0) := by
  obtain ⟨h, hCompact, h0, hMean, hShrink⟩ := exists_violation_of_unhalved_rational_trace_model
  obtain ⟨R, M, L, hR, hM, hL, hBound, hSupport, hLip⟩ := compact_schwartz_bounds h hCompact
  refine ⟨h, hCompact, h0, hMean, fun k ↦ ?_⟩
  obtain ⟨δ, hδ, hδAll⟩ := hShrink k
  refine ⟨min δ (1 / (2 * R)), lt_min hδ (by positivity), fun ε hε hεmin ↦ ?_⟩
  have hε' := hεmin.trans_le (min_le_left _ _)
  have hεR := hεmin.trans_le (min_le_right _ _)
  have hsmall : R * ε ≤ 1 / 2 := by
    have hi := (lt_div_iff₀ (by positivity : 0 < 2 * R)).mp hεR
    nlinarith
  obtain ⟨hZ, hSum, v, hlog, hineq⟩ := hδAll ε hε hε'
  have hSupportShort (t : ℝ) (ht : t ≤ 1 / 2 ∨ 2 ≤ t) : shrinkingRadialTest h ε t = 0 := by
    by_cases ht' : 0 < t
    · exact hZ t ht' ht
    · simp [shrinkingRadialTest, ht']
  refine ⟨hSupportShort, hSum, ?_, v, ?_, hineq⟩
  · intro p _ _ _ μ _ ψ hcont hψ hμ
    exact padic_radial_principal_value_zero μ ψ hcont hψ hμ _ hSupportShort
  · have hA := shrinking_real_place_additive_tendsto h.continuous.measurable hR.le hM hL
      hε hsmall hBound hSupport (fun x _ ↦ hLip x) hlog
    exact hA.congr fun δ ↦ (cutoffRealPlaceTranslated_eq _ δ).symm


end MasulloAudit

open MasulloAudit

theorem solution :
    ∃ h : 𝓢(ℝ, ℝ), HasCompactSupport h ∧ 0 < h 0 ∧ (∫ x, h x) = 0 ∧
      ∀ k : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
        (∀ t : ℝ, t ≤ 1 / 2 ∨ 2 ≤ t → shrinkingRadialTest h ε t = 0) ∧
        Summable (rationalCappedSpectralTerm h ε) ∧
        (∀ (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
            (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[p] Circle),
          Continuous ψ → (∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) →
          μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1 →
          let F : ℚ_[p] → ℂ := fun y ↦ (Real.log ‖y‖ : ℂ) *
            (∫ x, padicShiftedRadialTest (shrinkingRadialTest h ε) x * (ψ (x * y) : ℂ) ∂μ)
          Integrable F μ ∧ (∫ y, F y ∂μ) = 0) ∧
        ∃ v : ℝ, Tendsto (cutoffRealPlaceTranslated (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
          (∑' ρ, rationalCappedSpectralTerm h ε ρ) <
            rationalPolarPair h ε - (v + k * h 0) :=
  exists_violation_of_unhalved_rational_trace_additive_cutoff
