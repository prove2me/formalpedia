-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_literal_short_energy_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:34:35.084729+00:00
-- url     : https://prove2.me/submissions/7fa22b23-7cd6-4a3d-b9c7-a74e67539c75

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial



theorem integrable_inv_one_add_mul_sq {b : ℝ} (hb : b ≠ 0) :
    MeasureTheory.Integrable fun x : ℝ ↦ (1 + (b * x) ^ 2)⁻¹ :=
  (integrable_inv_one_add_sq.comp_mul_left' hb).congr (by simp)

namespace Finset



end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Backport (Mathlib d13f23b). -/
theorem integral_comp_exp (g : ℝ → E) :
    ∫ x, exp x • g (exp x) = ∫ y in Ioi 0, g y := by
  symm
  rw [← range_exp, ← image_univ]
  simpa using integral_image_eq_integral_abs_deriv_smul .univ
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

/-- Backport (Mathlib d13f23b). -/
theorem integrable_comp_exp (g : ℝ → E) :
    Integrable (fun x ↦ exp x • g (exp x)) ↔ IntegrableOn g (Ioi 0) := by
  rw [← integrableOn_univ, ← range_exp, ← image_univ]
  symm
  simpa using integrableOn_image_iff_integrableOn_abs_deriv_smul
    .univ (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

/-- Backport (Mathlib d13f23b): substitution `y = log x` over `Ioi 0`. -/
theorem integral_comp_log_Ioi_zero (g : ℝ → E) :
    ∫ x in Ioi 0, x⁻¹ • g (log x) = ∫ y, g y := by
  simpa using (integral_comp_exp (fun x ↦ x⁻¹ • g (log x))).symm

/-- Backport (Mathlib d13f23b). -/
theorem integrableOn_comp_log_Ioi_zero (g : ℝ → E) :
    IntegrableOn (fun x ↦ x⁻¹ • g (log x)) (Ioi 0) ↔ Integrable g := by
  simpa using (integrable_comp_exp (fun x ↦ x⁻¹ • g (log x))).symm

end LogSubst

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPlancherel
namespace OAI

/-! Agreement of the classical integral Fourier transform with the
library L² transform, in the integrable case needed for finite windows. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.FourierTransform
open scoped _root_.SchwartzMap

theorem mrt_fourier_toL2 {f : ℝ → ℂ} (hf : Integrable f)
    (hf₂ : MemLp f 2) (hF₂ : MemLp (𝓕 f) 2) :
    𝓕 hf₂.toLp = hF₂.toLp := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (E := ℝ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕 hf₂.toLp) =
    Lp.toTemperedDistribution hF₂.toLp
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : ℝ, (𝓕 g) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x : ℝ, g x • (𝓕 f) x := by
      simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner g.integrable hf)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF₂.coeFn_toLp] with x hx
      rw [hx]

lemma mrt_toL2_norm_sq {f : ℝ → ℂ} (hf₂ : MemLp f 2) :
    ‖hf₂.toLp‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf₂.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem mrt_plancherel {f : ℝ → ℂ} (hf : Integrable f)
    (hf₂ : MemLp f 2) (hF₂ : MemLp (𝓕 f) 2) :
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [← mrt_toL2_norm_sq hF₂, ← mrt_fourier_toL2 hf hf₂ hF₂,
    Lp.norm_fourier_eq, mrt_toL2_norm_sq hf₂]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowIdentity
namespace OAI

/-! The exact two-window identity used to remove the moving additive
endpoint before the logarithmic Fourier estimate. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_interval_sum_split (S : Finset ℕ) (a : ℕ → ℂ) {x h w : ℝ}
    (hh : 0 ≤ h) (hw : h ≤ w) :
    mrtIntervalSum S a x w =
      mrtIntervalSum S a x h + mrtIntervalSum S a (x + h) (w - h) := by
  unfold mrtIntervalSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  have he : x + h + (w - h) = x + w := by ring
  rw [he]
  by_cases hx : x < (n : ℝ)
  · by_cases hh' : (n : ℝ) ≤ x + h
    · have hw' : (n : ℝ) ≤ x + w := hh'.trans (by linarith)
      have hn : ¬x + h < (n : ℝ) := not_lt.mpr hh'
      simp [hx, hh', hw', hn]
    · have hn : x + h < (n : ℝ) := lt_of_not_ge hh'
      simp [hx, hh', hn]
  · have hn : ¬x + h < (n : ℝ) := by intro hn; exact hx (by linarith)
    simp [hx, hn]

lemma mrt_interval_sum_difference (S : Finset ℕ) (a : ℕ → ℂ) {x h w : ℝ}
    (hh : 0 ≤ h) (hw : h ≤ w) :
    mrtIntervalSum S a x w - mrtIntervalSum S a (x + h) (w - h) =
      mrtIntervalSum S a x h := by
  rw [mrt_interval_sum_split S a hh hw]
  abel


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogWindow
namespace OAI

/-! The exact finite logarithmic window and its Fourier multiplier. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.FourierTransform _root_.Set
open scoped _root_.ENNReal



lemma mrtLogWindowAtom_memLp (b a : ℝ) (p : ℝ≥0∞) :
    MemLp (mrtLogWindowAtom b a) p := by
  have hs : volume (Ico (b - a) b) ≠ ⊤ :=
    ne_of_lt ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top)
  have hh := memLp_indicator_const p measurableSet_Ico (Real.exp (a - b)) (Or.inr hs)
  apply hh.mono'
  · exact (Continuous.aestronglyMeasurable (by fun_prop :
      Continuous (fun y : ℝ => (Real.exp (-y) : ℂ)))).indicator measurableSet_Ico
  · filter_upwards with y
    by_cases hy : y ∈ Ico (b - a) b
    · simp only [mrtLogWindowAtom, indicator_of_mem hy, norm_real, Real.norm_eq_abs,
        Real.abs_exp]
      exact Real.exp_le_exp.mpr (by linarith [hy.1])
    · simp [mrtLogWindowAtom, hy]

lemma mrtLogWindowAtom_integrable (b a : ℝ) : Integrable (mrtLogWindowAtom b a) :=
  (memLp_one_iff_integrable).mp (mrtLogWindowAtom_memLp b a 1)

lemma mrt_one_add_imaginary_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh

theorem mrt_log_window_fourier (b : ℝ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    𝓕 (mrtLogWindowAtom b a) t =
      Complex.exp (-((1 : ℂ) + (2 * Real.pi * t : ℝ) * I) * b) *
        mrtWindowMultiplier a (2 * Real.pi * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let d : ℂ := 1 + (2 * Real.pi * t : ℝ) * I
  have hd : d ≠ 0 := mrt_one_add_imaginary_ne_zero _
  have he : (fun y : ℝ =>
      Complex.exp ((-2 * Real.pi * y * t : ℝ) * I) • mrtLogWindowAtom b a y) =
      (Ico (b - a) b).indicator (fun y => Complex.exp (-d * y)) := by
    funext y
    by_cases hy : y ∈ Ico (b - a) b
    · simp only [mrtLogWindowAtom, indicator_of_mem hy, smul_eq_mul,
        Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [d]
      push_cast
      ring
    · simp [mrtLogWindowAtom, hy]
  rw [he, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show b - a ≤ b by linarith),
    integral_exp_mul_complex (neg_ne_zero.mpr hd)]
  have hex : -d * ((b - a : ℝ) : ℂ) = -d * b + d * a := by push_cast; ring
  rw [hex, Complex.exp_add]
  change (Complex.exp (-d * b) - Complex.exp (-d * b) * Complex.exp (d * a)) / -d =
    Complex.exp (-d * b) * ((Complex.exp (d * a) - 1) / d)
  field_simp
  ring

lemma mrt_log_window_membership {n : ℕ} (hn : 0 < n) (a y : ℝ) :
    y ∈ Ico (Real.log (n : ℝ) - a) (Real.log (n : ℝ)) ↔
      Real.exp y < n ∧ (n : ℝ) ≤ Real.exp a * Real.exp y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hhi : Real.exp y < n ↔ y < Real.log (n : ℝ) := by
    nth_rewrite 1 [← Real.exp_log hn0]
    exact Real.exp_lt_exp
  have hlo : (n : ℝ) ≤ Real.exp a * Real.exp y ↔ Real.log (n : ℝ) - a ≤ y := by
    rw [← Real.exp_add]
    nth_rewrite 1 [← Real.exp_log hn0]
    rw [Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  simp only [mem_Ico, hhi, hlo, and_comm]


theorem mrt_log_window_interval (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) (v y : ℝ) :
    mrtLogWindow S a v y = (Real.exp (-y) : ℂ) *
      mrtIntervalSum S a (Real.exp y) ((Real.exp v - 1) * Real.exp y) := by
  have he : Real.exp y + (Real.exp v - 1) * Real.exp y = Real.exp v * Real.exp y := by ring
  simp only [mrtLogWindow, mrtIntervalSum, Finset.mul_sum, he]
  apply Finset.sum_congr rfl
  intro n hnS
  have hm := mrt_log_window_membership (hn n hnS) v y
  by_cases hy : y ∈ Ico (Real.log (n : ℝ) - v) (Real.log (n : ℝ))
  · have hi := hm.mp hy
    simp only [mrtLogWindowAtom, indicator_of_mem hy, if_pos hi]
    ring
  · have hi : ¬(Real.exp y < n ∧ (n : ℝ) ≤ Real.exp v * Real.exp y) :=
      fun h => hy (hm.mpr h)
    simp only [mrtLogWindowAtom, indicator_of_notMem hy, if_neg hi, mul_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowMultiplier
namespace OAI

/-! The logarithmic-window multiplier has square-integrable quadratic
decay. These bounds keep the actual finite window width. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.FourierTransform

lemma mrtWindowMultiplier_continuous (a : ℝ) : Continuous (mrtWindowMultiplier a) := by
  unfold mrtWindowMultiplier
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact mrt_one_add_imaginary_ne_zero

lemma mrt_window_multiplier_sq (a t : ℝ) :
    ‖mrtWindowMultiplier a t‖ ^ 2 ≤ (Real.exp a + 1) ^ 2 / (1 + t ^ 2) := by
  have hn : ‖Complex.exp (((1 : ℂ) + (t : ℂ) * I) * a) - 1‖ ≤ Real.exp a + 1 := by
    apply (norm_sub_le _ _).trans
    simp [Complex.norm_exp, mul_re]
  have hd : ‖(1 : ℂ) + (t : ℂ) * I‖ ^ 2 = 1 + t ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  unfold mrtWindowMultiplier
  rw [norm_div, div_pow, hd]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity)

lemma mrt_log_window_atom_fourier_norm (b : ℝ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    ‖𝓕 (mrtLogWindowAtom b a) t‖ ^ 2 =
      Real.exp (-b) ^ 2 * ‖mrtWindowMultiplier a (2 * Real.pi * t)‖ ^ 2 := by
  rw [mrt_log_window_fourier b ha, norm_mul, mul_pow]
  congr 1
  rw [Complex.norm_exp]
  congr 2
  simp

lemma mrt_log_window_atom_fourier_memLp (b : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (𝓕 (mrtLogWindowAtom b a)) 2 := by
  have hc : Continuous (𝓕 (mrtLogWindowAtom b a)) := by
    convert (preTransparency := .instances) (Continuous.mul
      (show Continuous (fun t : ℝ =>
        Complex.exp (-((1 : ℂ) + (2 * Real.pi * t : ℝ) * I) * b)) by fun_prop)
      ((mrtWindowMultiplier_continuous a).comp (by fun_prop :
        Continuous (fun t : ℝ => 2 * Real.pi * t)))) using 1
    ext t
    exact mrt_log_window_fourier b ha t
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hm := (integrable_inv_one_add_mul_sq
    (show (2 : ℝ) * Real.pi ≠ 0 by positivity)).const_mul
      (Real.exp (-b) ^ 2 * (Real.exp a + 1) ^ 2)
  apply hm.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  simp only [Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mrt_log_window_atom_fourier_norm b ha]
  have hh := mul_le_mul_of_nonneg_left (mrt_window_multiplier_sq a (2 * Real.pi * t))
    (sq_nonneg (Real.exp (-b)))
  convert (preTransparency := .instances) hh using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowPlancherel
namespace OAI

/-! Plancherel for the actual finite logarithmic windows. The coefficient
function is arbitrary; multiplicativity plays no role in this bridge. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.FourierTransform _root_.Finset

lemma mrt_fourier_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Integrable (f i)) (t : ℝ) :
    𝓕 (fun x => ∑ i ∈ S, f i x) t = ∑ i ∈ S, 𝓕 (f i) t := by
  simp only [Real.fourier_eq, smul_sum]
  apply integral_finsetSum
  intro i hi
  exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
    (show Continuous (fun p : ℝ × ℝ => (innerₗ ℝ p.1) p.2) from continuous_inner) t).mpr
      (hf i hi)

lemma mrt_fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => c * f x) t = c * 𝓕 f t := by
  simpa only [Pi.smul_apply, smul_eq_mul] using! congrFun
    (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) f c) t


lemma mrt_log_window_integrable (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    Integrable (mrtLogWindow S a v) :=
  integrable_finsetSum S (fun n _ =>
    (mrtLogWindowAtom_integrable (Real.log (n : ℝ)) v).const_mul (a n))

lemma mrt_log_window_memLp (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    MemLp (mrtLogWindow S a v) 2 :=
  memLp_finsetSum S (fun n _ =>
    (mrtLogWindowAtom_memLp (Real.log (n : ℝ)) v 2).const_mul (a n))

theorem mrt_log_window_transform (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    𝓕 (mrtLogWindow S a v) t =
      mrtWindowMultiplier v (2 * Real.pi * t) * mrtLogDirichlet S a (2 * Real.pi * t) := by
  change 𝓕 (fun y => ∑ n ∈ S, a n * mrtLogWindowAtom (Real.log (n : ℝ)) v y) t = _
  rw [mrt_fourier_finsetSum S _ (fun n _ =>
    (mrtLogWindowAtom_integrable (Real.log (n : ℝ)) v).const_mul (a n))]
  simp only [mrt_fourier_const_mul, mrt_log_window_fourier _ hv,
    mrtLogDirichlet, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

lemma mrt_log_window_fourier_memLp (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) : MemLp (𝓕 (mrtLogWindow S a v)) 2 := by
  have hh := memLp_finsetSum S (fun n _ =>
    (mrt_log_window_atom_fourier_memLp (Real.log (n : ℝ)) hv).const_mul (a n))
  convert (preTransparency := .instances) hh using 1
  ext t
  change 𝓕 (fun y => ∑ n ∈ S, a n * mrtLogWindowAtom (Real.log (n : ℝ)) v y) t = _
  rw [mrt_fourier_finsetSum S _ (fun n _ =>
    (mrtLogWindowAtom_integrable (Real.log (n : ℝ)) v).const_mul (a n))]
  simp only [mrt_fourier_const_mul]

theorem mrt_log_window_plancherel (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ y : ℝ, ‖mrtLogWindow S a v y‖ ^ 2) =
      ∫ t : ℝ, ‖mrtWindowMultiplier v (2 * Real.pi * t) *
        mrtLogDirichlet S a (2 * Real.pi * t)‖ ^ 2 := by
  have hh := (mrt_plancherel (mrt_log_window_integrable S a v)
    (mrt_log_window_memLp S a v) (mrt_log_window_fourier_memLp S a hv)).symm
  simpa only [mrt_log_window_transform S a hv] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowBounds
namespace OAI

/-! Uniform short-window bounds for the explicit Fourier multiplier. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Set

lemma mrt_window_multiplier_integral (a t : ℝ) :
    mrtWindowMultiplier a t =
      ∫ y in (0 : ℝ)..a, Complex.exp (((1 : ℂ) + (t : ℂ) * I) * y) := by
  rw [integral_exp_mul_complex (mrt_one_add_imaginary_ne_zero t)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mrtWindowMultiplier]

lemma mrt_window_multiplier_small {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    ‖mrtWindowMultiplier a t‖ ≤ a * Real.exp a := by
  rw [mrt_window_multiplier_integral]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := a) (C := Real.exp a)
    (f := fun y : ℝ => Complex.exp (((1 : ℂ) + (t : ℂ) * I) * y)) (fun y hy => ?_)
  · simpa only [sub_zero, abs_of_nonneg ha, mul_comm] using hh
  · rw [uIoc_of_le ha] at hy
    have he : ‖Complex.exp (((1 : ℂ) + (t : ℂ) * I) * y)‖ = Real.exp y := by
      rw [Complex.norm_exp]
      simp
    rw [he]
    exact Real.exp_le_exp.mpr hy.2

theorem mrt_relative_window_multiplier {u : ℝ} (hu : 0 ≤ u) (hu3 : u ≤ 3) (t : ℝ) :
    ‖mrtWindowMultiplier (Real.log (1 + u)) t‖ ^ 2 ≤
      min (16 * u ^ 2) (25 / (1 + t ^ 2)) := by
  have hu0 : 0 < 1 + u := by linarith
  have hlog : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hlogu : Real.log (1 + u) ≤ u := by
    have hh := Real.log_le_sub_one_of_pos hu0
    linarith
  have hsmall : ‖mrtWindowMultiplier (Real.log (1 + u)) t‖ ≤ 4 * u := by
    apply (mrt_window_multiplier_small hlog t).trans
    rw [Real.exp_log hu0]
    nlinarith [mul_le_mul_of_nonneg_right hlogu hu0.le]
  have hlarge := mrt_window_multiplier_sq (Real.log (1 + u)) t
  rw [Real.exp_log hu0] at hlarge
  apply le_min
  · have hh := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
    nlinarith
  · apply hlarge.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith

theorem mrt_log_window_energy_angular (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ y : ℝ, ‖mrtLogWindow S a v y‖ ^ 2) =
      (2 * Real.pi)⁻¹ *
        ∫ t : ℝ, ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖ ^ 2 := by
  rw [mrt_log_window_plancherel S a hv]
  simpa only [abs_of_pos (inv_pos.mpr (show (0 : ℝ) < 2 * Real.pi by positivity)),
    smul_eq_mul] using Measure.integral_comp_mul_left
      (fun t : ℝ => ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖ ^ 2)
      (2 * Real.pi)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAdditiveWindows
namespace OAI

/-! Bounded measurable finite interval sums and the squared two-window
inequality. These statements allow arbitrary complex coefficients. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

lemma mrt_interval_sum_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset ℕ) (a : ℕ → ℂ) {x h : α → ℝ}
    (hx : Measurable x) (hh : Measurable h) :
    Measurable (fun t => mrtIntervalSum S a (x t) (h t)) := by
  apply Finset.measurable_sum
  intro n _
  exact Measurable.ite
    ((measurableSet_lt hx measurable_const).inter
      (measurableSet_le measurable_const (hx.add hh)))
    measurable_const measurable_const

lemma mrt_interval_sum_norm (S : Finset ℕ) (a : ℕ → ℂ) (x h : ℝ) :
    ‖mrtIntervalSum S a x h‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  unfold mrtIntervalSum
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using (norm_nonneg (a n))

lemma mrt_interval_sum_sq_integrableOn {α : Type*} [MeasurableSpace α]
    (S : Finset ℕ) (a : ℕ → ℂ) {μ : Measure α} {s : Set α}
    (hs : μ s ≠ ⊤) {x h : α → ℝ} (hx : Measurable x) (hh : Measurable h) :
    IntegrableOn (fun t => ‖mrtIntervalSum S a (x t) (h t)‖ ^ 2) s μ := by
  apply Measure.integrableOn_of_bounded hs
    (((mrt_interval_sum_measurable S a hx hh).norm.pow_const 2).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (mrt_interval_sum_norm S a (x t) (h t)) 2

lemma mrt_interval_sum_sq_intervalIntegrable (S : Finset ℕ) (a : ℕ → ℂ)
    {x h : ℝ → ℝ} (hx : Measurable x) (hh : Measurable h) (b c : ℝ) :
    IntervalIntegrable (fun t => ‖mrtIntervalSum S a (x t) (h t)‖ ^ 2)
      volume b c := by
  rw [intervalIntegrable_iff]
  apply mrt_interval_sum_sq_integrableOn S a _ hx hh
  exact measure_Ioc_lt_top.ne

lemma mrt_interval_sum_sq_split (S : Finset ℕ) (a : ℕ → ℂ) {x h w : ℝ}
    (hh : 0 ≤ h) (hw : h ≤ w) :
    ‖mrtIntervalSum S a x h‖ ^ 2 ≤
      2 * ‖mrtIntervalSum S a x w‖ ^ 2 +
        2 * ‖mrtIntervalSum S a (x + h) (w - h)‖ ^ 2 := by
  rw [← mrt_interval_sum_difference S a hh hw]
  have hn := norm_sub_le (mrtIntervalSum S a x w)
    (mrtIntervalSum S a (x + h) (w - h))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖mrtIntervalSum S a x w‖ -
    ‖mrtIntervalSum S a (x + h) (w - h)‖)]

theorem mrt_interval_sum_averaged_sq (S : Finset ℕ) (a : ℕ → ℂ)
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖mrtIntervalSum S a x h‖ ^ 2 ≤ h⁻¹ *
      ((∫ w in h..3 * h, ‖mrtIntervalSum S a x w‖ ^ 2) +
        ∫ w in h..3 * h, ‖mrtIntervalSum S a (x + h) (w - h)‖ ^ 2) := by
  have hi₁ := mrt_interval_sum_sq_intervalIntegrable S a (x := fun _ => x) (h := id)
    measurable_const measurable_id h (3 * h)
  have hi₂ := mrt_interval_sum_sq_intervalIntegrable S a
    (x := fun _ => x+h) (h := fun w => w-h)
    measurable_const (measurable_id.sub measurable_const) h (3 * h)
  have hm := intervalIntegral.integral_mono_on (show h ≤ 3 * h by linarith)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ‖mrtIntervalSum S a x h‖ ^ 2) volume h (3 * h))
    ((hi₁.const_mul 2).add (hi₂.const_mul 2))
    (fun w hw => mrt_interval_sum_sq_split S a hh.le hw.1)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hi₁.const_mul 2) (hi₂.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  simp only [smul_eq_mul, id_eq] at hm
  apply (le_inv_mul_iff₀ hh).mpr
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowAveraging
namespace OAI

/-! Rectangular integration of the finite additive windows. The two-window
inequality pays its error once before logarithmic Fourier analysis. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

lemma mrt_interval_sum_sq_box (S : Finset ℕ) (a : ℕ → ℂ)
    (b c d e : ℝ) :
    Integrable (fun z : ℝ × ℝ => ‖mrtIntervalSum S a z.1 z.2‖ ^ 2)
      ((volume.restrict (Ioc b c)).prod (volume.restrict (Ioc d e))) := by
  apply integrableOn_univ.mp
  exact mrt_interval_sum_sq_integrableOn S a (measure_ne_top _ _)
    measurable_fst measurable_snd

lemma mrt_interval_sum_sq_inner (S : Finset ℕ) (a : ℕ → ℂ)
    (b c : ℝ) {d e : ℝ} (hde : d ≤ e) :
    IntervalIntegrable (fun x => ∫ w in d..e, ‖mrtIntervalSum S a x w‖ ^ 2)
      volume b c := by
  rw [intervalIntegrable_iff]
  simp_rw [intervalIntegral.integral_of_le hde]
  exact (mrt_interval_sum_sq_box S a (min b c) (max b c) d e).integral_prod_left


theorem mrt_additive_window_rectangular (S : Finset ℕ) (a : ℕ → ℂ)
    {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2 * N, ‖mrtIntervalSum S a x h‖ ^ 2) ≤
      (2 / h) * ∫ x in N..3 * N, ∫ w in 0..3 * h,
        ‖mrtIntervalSum S a x w‖ ^ 2 := by
  let A : ℝ → ℝ := fun x => ∫ w in 0..3 * h, ‖mrtIntervalSum S a x w‖ ^ 2
  have hAi (b c : ℝ) : IntervalIntegrable A volume b c :=
    mrt_interval_sum_sq_inner S a b c (by positivity)
  have hApos (x : ℝ) : 0 ≤ A x :=
    intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _)
  have hp (x : ℝ) : ‖mrtIntervalSum S a x h‖ ^ 2 ≤ h⁻¹ * (A x + A (x + h)) := by
    apply (mrt_interval_sum_averaged_sq S a x hh).trans
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
    apply add_le_add
    · exact intervalIntegral.integral_mono_interval hh.le (by linarith) le_rfl
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (mrt_interval_sum_sq_intervalIntegrable S a measurable_const measurable_id 0 (3*h))
    · rw [show (∫ w in h..3*h, ‖mrtIntervalSum S a (x+h) (w-h)‖ ^ 2) =
          ∫ w in 0..2*h, ‖mrtIntervalSum S a (x+h) w‖ ^ 2 by
          have he : 3*h-h = 2*h := by ring
          simpa only [sub_self, he] using intervalIntegral.integral_comp_sub_right
            (a := h) (b := 3*h)
            (fun w => ‖mrtIntervalSum S a (x+h) w‖ ^ 2) h]
      exact intervalIntegral.integral_mono_interval le_rfl (by positivity) (by linarith)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (mrt_interval_sum_sq_intervalIntegrable S a measurable_const measurable_id 0 (3*h))
  have hshift : (∫ x in N..2*N, A (x+h)) = ∫ x in N+h..2*N+h, A x := by
    exact intervalIntegral.integral_comp_add_right A h
  have hshiftI : IntervalIntegrable (fun x => A (x+h)) volume N (2*N) := by
    simpa only [add_sub_cancel_right] using (hAi (N+h) (2*N+h)).comp_add_right h
  have hi := intervalIntegral.integral_mono_on (by linarith : N ≤ 2*N)
    (mrt_interval_sum_sq_intervalIntegrable S a measurable_id measurable_const N (2*N))
    (((hAi N (2*N)).add hshiftI).const_mul h⁻¹) (fun x _ => hp x)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (hAi N (2*N)) hshiftI, hshift] at hi
  have h₁ : (∫ x in N..2*N, A x) ≤ ∫ x in N..3*N, A x :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall hApos) (hAi N (3*N))
  have h₂ : (∫ x in N+h..2*N+h, A x) ≤ ∫ x in N..3*N, A x :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hApos) (hAi N (3*N))
  calc
    _ ≤ h⁻¹ * ((∫ x in N..2*N, A x) + ∫ x in N+h..2*N+h, A x) := hi
    _ ≤ h⁻¹ * (2 * ∫ x in N..3*N, A x) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
      linarith
    _ = _ := by dsimp [A]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowSubstitution
namespace OAI

/-! Conversion of relative additive windows to the logarithmic window,
including the physical-variable Jacobian. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

lemma mrt_log_window_measurable (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    Measurable (mrtLogWindow S a v) := by
  apply Finset.measurable_sum
  intro n _
  apply measurable_const.mul
  exact (show Measurable (fun y : ℝ => (Real.exp (-y) : ℂ)) by fun_prop).indicator
    measurableSet_Ico

lemma mrt_relative_interval_identity (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    mrtIntervalSum S a x (x * u) =
      (x : ℂ) * mrtLogWindow S a (Real.log (1 + u)) (Real.log x) := by
  rw [mrt_log_window_interval S hn a, Real.exp_neg,
    Real.exp_log hx, Real.exp_log (by linarith : 0 < 1 + u)]
  have he : ((1 + u) - 1) * x = x * u := by ring
  rw [he]
  have hc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma mrt_relative_interval_sq (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    ‖mrtIntervalSum S a x (x * u)‖ ^ 2 =
      x ^ 2 * ‖mrtLogWindow S a (Real.log (1 + u)) (Real.log x)‖ ^ 2 := by
  rw [mrt_relative_interval_identity S hn a hx hu, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx, mul_pow]

lemma mrt_log_weight_integral_bound {g : ℝ → ℝ} (hgm : Measurable g)
    (hgi : Integrable g) (hgn : ∀ y, 0 ≤ g y) {N : ℝ} (hN : 0 < N) :
    (∫ x in N..3 * N, x ^ 3 * g (Real.log x)) ≤
      (3 * N) ^ 4 * ∫ y : ℝ, g y := by
  let b : ℝ → ℝ := fun x => x⁻¹ * g (Real.log x)
  have hbi : IntegrableOn b (Ioi 0) := by
    exact (integrableOn_comp_log_Ioi_zero g).mpr hgi
  have hs : Ioc N (3*N) ⊆ Ioi (0:ℝ) := fun x hx => lt_trans hN hx.1
  have hbn : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ b x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (inv_nonneg.mpr hx.le) (hgn _)
  have hpoly (x : ℝ) (hx : x ∈ Ioc N (3*N)) :
      x ^ 3 * g (Real.log x) ≤ (3*N)^4 * b x := by
    have hx0 : 0 < x := lt_trans hN hx.1
    calc
      x ^ 3 * g (Real.log x) = x ^ 4 * b x := by
        dsimp [b]
        field_simp
      _ ≤ (3*N)^4 * b x := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hx0.le hx.2 4) (mul_nonneg (inv_nonneg.mpr hx0.le) (hgn _))
  have hdom : IntegrableOn (fun x => (3*N)^4 * b x) (Ioc N (3*N)) :=
    (hbi.mono_set hs).const_mul _
  have hleft : IntegrableOn (fun x => x^3 * g (Real.log x)) (Ioc N (3*N)) := by
    apply hdom.mono' (((measurable_id.pow_const 3).mul
      (hgm.comp Real.measurable_log)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change ‖x^3 * g (Real.log x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (lt_trans hN hx.1).le _) (hgn _))]
    exact hpoly x hx
  rw [intervalIntegral.integral_of_le (by linarith : N ≤ 3*N)]
  calc
    _ ≤ ∫ x in Ioc N (3*N), (3*N)^4 * b x :=
      setIntegral_mono_on hleft hdom measurableSet_Ioc hpoly
    _ = (3*N)^4 * ∫ x in Ioc N (3*N), b x := integral_const_mul _ _
    _ ≤ (3*N)^4 * ∫ x in Ioi (0:ℝ), b x := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hbi hbn hs.eventuallyLE) (by positivity)
    _ = _ := by
      rw [show (∫ x in Ioi (0:ℝ), b x) = ∫ y : ℝ, g y by
        exact integral_comp_log_Ioi_zero g]

theorem mrt_relative_window_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N u : ℝ} (hN : 0 < N) (hu : 0 ≤ u) :
    (∫ x in N..3*N, x * ‖mrtIntervalSum S a x (x*u)‖ ^ 2) ≤
      (3*N)^4 * ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖ ^ 2 := by
  calc
    _ = ∫ x in N..3*N,
        x^3 * ‖mrtLogWindow S a (Real.log (1+u)) (Real.log x)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      change x * ‖mrtIntervalSum S a x (x*u)‖ ^ 2 = _
      rw [uIcc_of_le (by linarith : N ≤ 3*N)] at hx
      rw [mrt_relative_interval_sq S hn a (lt_of_lt_of_le hN hx.1) hu]
      ring
    _ ≤ _ := mrt_log_weight_integral_bound
      ((mrt_log_window_measurable S a _).norm.pow_const 2)
      ((mrt_log_window_memLp S a _).integrable_norm_pow (by norm_num))
      (fun _ => sq_nonneg _) hN

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowKernel
namespace OAI

/-! A uniform Fourier kernel for all relative windows up to a given size.
No multiplicativity assumptions enter this finite analytic estimate. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical


lemma mrt_log_dirichlet_norm (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖mrtLogDirichlet S a t‖ ≤
      ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ)) := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, neg_one_mul, le_refl]


lemma mrt_window_kernel_integrable (S : Finset ℕ) (a : ℕ → ℂ) (r : ℝ) :
    Integrable (fun t => mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2) := by
  let C := ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ))
  have hm : Measurable (fun t => mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2) := by
    unfold mrtWindowKernel mrtLogDirichlet
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (25*C^2)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  have hn : 0 ≤ mrtWindowKernel r t := le_min (by positivity) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (sq_nonneg _))]
  have hC : ‖mrtLogDirichlet S a t‖^2 ≤ C^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm S a t) 2
  calc
    _ ≤ (25/(1+t^2))*C^2 := mul_le_mul (min_le_right _ _) hC (sq_nonneg _)
      (by positivity)
    _ = _ := by ring

lemma mrt_window_frequency_integrable (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    Integrable (fun t => ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖^2) := by
  let C := ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ))
  have hm : Measurable (fun t => ‖mrtWindowMultiplier v t * mrtLogDirichlet S a t‖^2) := by
    unfold mrtWindowMultiplier mrtLogDirichlet
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul ((Real.exp v+1)^2*C^2)).mono'
    hm.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  have hC : ‖mrtLogDirichlet S a t‖^2 ≤ C^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm S a t) 2
  calc
    _ ≤ ((Real.exp v+1)^2/(1+t^2))*C^2 :=
      mul_le_mul (mrt_window_multiplier_sq v t) hC (sq_nonneg _) (by positivity)
    _ = _ := by ring

theorem mrt_log_window_uniform_kernel (S : Finset ℕ) (a : ℕ → ℂ)
    {u r : ℝ} (hu : 0 ≤ u) (hur : u ≤ r) (hr : r ≤ 3) :
    (∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) ≤
      (2*Real.pi)⁻¹ *
        ∫ t : ℝ, mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2 := by
  rw [mrt_log_window_energy_angular S a (Real.log_nonneg (by linarith))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (mrt_window_frequency_integrable S a _)
    (mrt_window_kernel_integrable S a r)
  intro t
  change ‖mrtWindowMultiplier (Real.log (1+u)) t * mrtLogDirichlet S a t‖^2 ≤ _
  rw [norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply (mrt_relative_window_multiplier hu (hur.trans hr) t).trans
  exact min_le_min (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hu hur 2) (by norm_num)) le_rfl

lemma mrt_log_window_joint_measurable (S : Finset ℕ) (a : ℕ → ℂ) :
    Measurable (fun z : ℝ × ℝ => mrtLogWindow S a (Real.log (1+z.1)) z.2) := by
  apply Finset.measurable_sum
  intro n _
  apply measurable_const.mul
  unfold mrtLogWindowAtom
  simp only [indicator_apply]
  apply Measurable.ite _ (by fun_prop) measurable_const
  exact (measurableSet_le (by fun_prop) measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_const)

lemma mrt_log_window_energy_measurable (S : Finset ℕ) (a : ℕ → ℂ) :
    Measurable (fun u : ℝ => ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) := by
  exact ((mrt_log_window_joint_measurable S a).norm.pow_const 2).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

lemma mrt_log_window_energy_intervalIntegrable (S : Finset ℕ) (a : ℕ → ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr3 : r ≤ 3) :
    IntervalIntegrable
      (fun u => ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) volume 0 r := by
  let C := (2*Real.pi)⁻¹ *
    ∫ t : ℝ, mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2
  rw [intervalIntegrable_iff, uIoc_of_le hr0]
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (mrt_log_window_energy_measurable S a).aestronglyMeasurable (M := C)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact mrt_log_window_uniform_kernel S a hu.1.le hu.2 hr3

theorem mrt_log_window_kernel_average (S : Finset ℕ) (a : ℕ → ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr3 : r ≤ 3) :
    (∫ u in 0..r, ∫ y : ℝ, ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) ≤
      r * (2*Real.pi)⁻¹ *
        ∫ t : ℝ, mrtWindowKernel r t * ‖mrtLogDirichlet S a t‖^2 := by
  have hb := intervalIntegral.integral_mono_on hr0
    (mrt_log_window_energy_intervalIntegrable S a hr0 hr3) intervalIntegrable_const
    (fun u hu => mrt_log_window_uniform_kernel S a hu.1 hu.2 hr3)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowTransfer
namespace OAI

/-! The fixed additive-window mean square is controlled by the actual
finite logarithmic Dirichlet polynomial. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

private lemma relative_box_integrable (S : Finset ℕ) (a : ℕ → ℂ)
    {N : ℝ} (hN : 0 < N) (r : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.1 * ‖mrtIntervalSum S a z.1 (z.1*z.2)‖^2)
      ((volume.restrict (Ioc N (3*N))).prod (volume.restrict (Ioc 0 r))) := by
  rw [Measure.prod_restrict]
  apply Measure.integrableOn_of_bounded
    (by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne)
    (by
      exact (measurable_fst.mul
        ((mrt_interval_sum_measurable S a measurable_fst
          (measurable_fst.mul measurable_snd)).norm.pow_const 2)).aestronglyMeasurable)
    (M := 3*N*(∑ n ∈ S, ‖a n‖)^2)
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  have hx : 0 < z.1 := lt_trans hN hz.1.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le (sq_nonneg _))]
  exact mul_le_mul hz.1.2
    (pow_le_pow_left₀ (norm_nonneg _) (mrt_interval_sum_norm S a _ _) 2)
    (sq_nonneg _) (by positivity)

private lemma relative_rescale (S : Finset ℕ) (a : ℕ → ℂ)
    {x H r : ℝ} (hH : 0 ≤ H) (hHr : H ≤ x*r) :
    (∫ w in 0..H, ‖mrtIntervalSum S a x w‖^2) ≤
      ∫ u in 0..r, x * ‖mrtIntervalSum S a x (x*u)‖^2 := by
  calc
    _ ≤ ∫ w in 0..x*r, ‖mrtIntervalSum S a x w‖^2 :=
      intervalIntegral.integral_mono_interval le_rfl hH hHr
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (mrt_interval_sum_sq_intervalIntegrable S a (x := fun _ => x) (h := id)
          measurable_const measurable_id _ _)
    _ = x * ∫ u in 0..r, ‖mrtIntervalSum S a x (x*u)‖^2 := by
      simpa only [mul_zero, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (a := 0) (b := r) (fun w => ‖mrtIntervalSum S a x w‖^2) x).symm
    _ = _ := (intervalIntegral.integral_const_mul _ _).symm

theorem mrt_fixed_window_log_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2*N, ‖mrtIntervalSum S a x h‖^2) ≤
      (162 * N^4 / h) *
        ∫ u in 0..(3*h/N), ∫ y : ℝ,
          ‖mrtLogWindow S a (Real.log (1+u)) y‖^2 := by
  let r : ℝ := 3*h/N
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr3 : r ≤ 3 := by dsimp [r]; apply (div_le_iff₀ hN).mpr; linarith
  have hi := relative_box_integrable S a hN r
  have hleft : IntervalIntegrable
      (fun x => ∫ w in 0..3*h, ‖mrtIntervalSum S a x w‖^2) volume N (3*N) :=
    mrt_interval_sum_sq_inner S a _ _ (by positivity)
  have hright : IntervalIntegrable
      (fun x => ∫ u in 0..r, x * ‖mrtIntervalSum S a x (x*u)‖^2)
      volume N (3*N) := by
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : N ≤ 3*N)]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hr0] using! hi.integral_prod_left
  have hres := intervalIntegral.integral_mono_on (by linarith : N ≤ 3*N)
    hleft hright (fun x hx => relative_rescale S a
      (by positivity) (by
        dsimp [r]
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hN).mpr
        have := mul_le_mul_of_nonneg_right hx.1 (show 0 ≤ 3*h by positivity)
        nlinarith))
  have hswap :
      (∫ x in N..3*N, ∫ u in 0..r, x * ‖mrtIntervalSum S a x (x*u)‖^2) =
      ∫ u in 0..r, ∫ x in N..3*N, x * ‖mrtIntervalSum S a x (x*u)‖^2 := by
    simp_rw [intervalIntegral.integral_of_le (by linarith : N ≤ 3*N),
      intervalIntegral.integral_of_le hr0]
    exact integral_integral_swap hi
  have houter : IntervalIntegrable
      (fun u => ∫ x in N..3*N, x * ‖mrtIntervalSum S a x (x*u)‖^2)
      volume 0 r := by
    rw [intervalIntegrable_iff, uIoc_of_le hr0]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le (by linarith : N ≤ 3*N)] using!
      hi.integral_prod_right
  have hlog := intervalIntegral.integral_mono_on hr0 houter
    ((mrt_log_window_energy_intervalIntegrable S a hr0 hr3).const_mul ((3*N)^4))
    (fun u hu => mrt_relative_window_energy S hn a hN hu.1)
  rw [intervalIntegral.integral_const_mul] at hlog
  calc
    _ ≤ (2/h) * ∫ x in N..3*N, ∫ w in 0..3*h,
        ‖mrtIntervalSum S a x w‖^2 := mrt_additive_window_rectangular S a hN hh hhN
    _ ≤ (2/h) * ∫ x in N..3*N, ∫ u in 0..r,
        x * ‖mrtIntervalSum S a x (x*u)‖^2 :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ = (2/h) * ∫ u in 0..r, ∫ x in N..3*N,
        x * ‖mrtIntervalSum S a x (x*u)‖^2 := by rw [hswap]
    _ ≤ (2/h) * ((3*N)^4 * ∫ u in 0..r, ∫ y : ℝ,
        ‖mrtLogWindow S a (Real.log (1+u)) y‖^2) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by dsimp [r]; ring

theorem mrt_fixed_window_fourier_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2*N, ‖mrtIntervalSum S a x h‖^2) ≤
      (486 * N^3 / (2*Real.pi)) *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2 := by
  have hr0 : 0 ≤ 3*h/N := by positivity
  have hr3 : 3*h/N ≤ 3 := by apply (div_le_iff₀ hN).mpr; linarith
  calc
    _ ≤ (162*N^4/h) * ∫ u in 0..(3*h/N), ∫ y : ℝ,
        ‖mrtLogWindow S a (Real.log (1+u)) y‖^2 :=
      mrt_fixed_window_log_energy S hn a hN hh hhN
    _ ≤ (162*N^4/h) * ((3*h/N)*(2*Real.pi)⁻¹ *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) :=
      mul_le_mul_of_nonneg_left (mrt_log_window_kernel_average S a hr0 hr3) (by positivity)
    _ = _ := by field_simp; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortEnergy
namespace OAI

/-! The normalized fixed-h Fourier estimate, in the usual low/high
frequency kernel, and its exact finite Dirichlet-polynomial form. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical


lemma mrt_short_kernel_integrable (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    Integrable (fun t => mrtShortKernel T t * ‖mrtLogDirichlet S a t‖^2) := by
  let C := ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ))
  have hm : Measurable (fun t => mrtShortKernel T t * ‖mrtLogDirichlet S a t‖^2) := by
    unfold mrtShortKernel mrtLogDirichlet
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (T^2*C^2)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  have hn : 0 ≤ mrtShortKernel T t := le_min (by norm_num) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (sq_nonneg _))]
  calc
    _ ≤ (T^2/(1+t^2))*C^2 := mul_le_mul (min_le_right _ _)
      (pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm S a t) 2)
      (sq_nonneg _) (by positivity)
    _ = _ := by ring

lemma mrt_scaled_window_kernel {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (t : ℝ) :
    (N/h)^2 * mrtWindowKernel (3*h/N) t ≤ 144 * mrtShortKernel (N/h) t := by
  have he : (N/h)^2 * (16*(3*h/N)^2) = 144 := by field_simp; ring
  have h₁ : (N/h)^2 * mrtWindowKernel (3*h/N) t ≤ 144 := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
  have h₂ : (N/h)^2 * mrtWindowKernel (3*h/N) t ≤
      144 * ((N/h)^2/(1+t^2)) := by
    calc
      _ ≤ (N/h)^2 * (25/(1+t^2)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
      _ ≤ _ := by
        have hp : 0 ≤ (N/h)^2/(1+t^2) := by positivity
        calc
          _ = 25*((N/h)^2/(1+t^2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num : (25:ℝ) ≤ 144) hp
  unfold mrtShortKernel
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 144), mul_one]
  exact le_min h₁ h₂

theorem mrt_normalized_short_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2*N, ‖mrtIntervalSum S a x h‖^2) / (N*h^2) ≤
      (69984/(2*Real.pi)) *
        ∫ t : ℝ, mrtShortKernel (N/h) t * ‖mrtLogDirichlet S a t‖^2 := by
  have hbase := mrt_fixed_window_fourier_energy S hn a hN hh hhN
  have hk := integral_mono
    ((mrt_window_kernel_integrable S a (3*h/N)).const_mul ((N/h)^2))
    ((mrt_short_kernel_integrable S a (N/h)).const_mul 144) (fun t => by
      change (N/h)^2 * (mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) ≤
        144 * (mrtShortKernel (N/h) t * ‖mrtLogDirichlet S a t‖^2)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (mrt_scaled_window_kernel hN hh t) (sq_nonneg _))
  rw [integral_const_mul, integral_const_mul] at hk
  calc
    _ ≤ ((486*N^3/(2*Real.pi)) *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) / (N*h^2) :=
      div_le_div_of_nonneg_right hbase (by positivity)
    _ = (486/(2*Real.pi)) * (((N/h)^2) *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) := by
      field_simp
    _ ≤ (486/(2*Real.pi)) * (144 *
        ∫ t : ℝ, mrtShortKernel (N/h) t * ‖mrtLogDirichlet S a t‖^2) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by ring

lemma mrt_log_dirichlet_polynomial (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) (t : ℝ) :
    mrtLogDirichlet S a t =
      mrtExponentialPolynomial S (fun n => a n/(n:ℂ))
        (fun n => -Real.log (n:ℝ)) t := by
  unfold mrtLogDirichlet mrtExponentialPolynomial
  apply sum_congr rfl
  intro n hnS
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn n hnS
  have he : -((1:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n:ℝ):ℂ) =
      ((-Real.log (n:ℝ):ℝ):ℂ) + ((-Real.log (n:ℝ)*t:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn0]
  push_cast
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFiniteWindows
namespace OAI

/-! The finite-support Fourier estimate applies to short exponential
sums with exact floor endpoints. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

lemma mrt_finite_window_eq_short_sum (b : ℕ → ℂ) {N H : ℕ}
    (hHN : H ≤ N) {x : ℝ} (hx : x ∈ Icc (N:ℝ) (2*N)) (α : ℝ) :
    mrtIntervalSum (Finset.Ioc N (4*N)) (fun n => b n * additiveCharacter α n)
      x H = shortExponentialSum b H α x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg N).trans hx.1
  have hxH : 0 ≤ x+(H:ℝ) := add_nonneg hx0 (Nat.cast_nonneg H)
  have hfilter : (Finset.Ioc N (4*N)).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+H) =
      Finset.Icc (Nat.floor x+1) (Nat.floor (x+(H:ℝ))) := by
    ext n
    simp only [mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hnlo, hnhi⟩
      exact ⟨Nat.succ_le_iff.mpr ((Nat.floor_lt hx0).mpr hnlo),
        (Nat.le_floor_iff hxH).mpr hnhi⟩
    · rintro ⟨hnlo, hnhi⟩
      have hnrlo : x < (n:ℝ) := (Nat.floor_lt hx0).mp (by omega)
      have hnrhi : (n:ℝ) ≤ x+H := (Nat.le_floor_iff hxH).mp hnhi
      have hNr : (N:ℝ) < n := hx.1.trans_lt hnrlo
      have hHNr : (H:ℝ) ≤ N := by exact_mod_cast hHN
      have hn4 : (n:ℝ) ≤ (4*N:ℕ) := by push_cast; nlinarith [hx.2]
      exact ⟨⟨by exact_mod_cast hNr, by exact_mod_cast hn4⟩, hnrlo, hnrhi⟩
  unfold mrtIntervalSum
  rw [← sum_filter, hfilter]
  rfl


lemma mrt_log_dirichlet_two_dyadic (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    mrtLogDirichlet (Finset.Ioc N (4*N)) b t =
      mrtDyadicPolynomial b N t + mrtDyadicPolynomial b (2*N) t := by
  have hn : ∀ n ∈ Finset.Ioc N (4*N), 0 < n :=
    fun n hn => lt_trans hN (Finset.mem_Ioc.mp hn).1
  rw [mrt_log_dirichlet_polynomial _ hn]
  have hs : Finset.Ioc N (4*N) = Finset.Ioc N (2*N) ∪ Finset.Ioc (2*N) (4*N) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)).symm
  have hd : Disjoint (Finset.Ioc N (2*N)) (Finset.Ioc (2*N) (4*N)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := (Finset.mem_Ioc.mp hn).2
    have := (Finset.mem_Ioc.mp hn').1
    omega
  simp only [mrtDyadicPolynomial, mrtExponentialPolynomial]
  rw [show 2*(2*N) = 4*N by omega, hs, sum_union hd]

theorem mrt_literal_short_energy_dyadic_oai (b : ℕ → ℂ) {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤
      (139968/(2*Real.pi)) *
        ((∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b N t‖^2) +
          ∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b (2*N) t‖^2) := by
  have hN : 0 < N := lt_of_lt_of_le hH hHN
  have hn (n k : ℕ) (hk : 0 < k) (hn : n ∈ Finset.Ioc k (2*k)) : 0 < n :=
    lt_trans hk (Finset.mem_Ioc.mp hn).1
  have hid (k : ℕ) (hk : 0 < k) :
      Integrable (fun t => mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b k t‖^2) := by
    have hi := mrt_short_kernel_integrable (Finset.Ioc k (2*k)) b ((N:ℝ)/H)
    simpa only [mrt_log_dirichlet_polynomial _ (fun n hn' => hn n k hk hn'),
      mrtDyadicPolynomial] using hi
  have hi := integral_mono (mrt_short_kernel_integrable (Finset.Ioc N (4*N)) b ((N:ℝ)/H))
    (((hid N hN).const_mul 2).add ((hid (2*N) (by omega)).const_mul 2)) (fun t => by
      change mrtShortKernel ((N:ℝ)/H) t * ‖mrtLogDirichlet (Finset.Ioc N (4*N)) b t‖^2 ≤
        2*(mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b N t‖^2) +
          2*(mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b (2*N) t‖^2)
      rw [mrt_log_dirichlet_two_dyadic b hN]
      have he := norm_add_le (mrtDyadicPolynomial b N t) (mrtDyadicPolynomial b (2*N) t)
      have hp := pow_le_pow_left₀ (norm_nonneg _) he 2
      have hsq : ‖mrtDyadicPolynomial b N t + mrtDyadicPolynomial b (2*N) t‖^2 ≤
          2*‖mrtDyadicPolynomial b N t‖^2 + 2*‖mrtDyadicPolynomial b (2*N) t‖^2 := by
        nlinarith [sq_nonneg (‖mrtDyadicPolynomial b N t‖-‖mrtDyadicPolynomial b (2*N) t‖)]
      have hk0 : 0 ≤ mrtShortKernel ((N:ℝ)/H) t := le_min (by norm_num) (by positivity)
      simpa only [mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left hsq hk0)
  simp only [Pi.add_apply] at hi
  rw [integral_add ((hid N hN).const_mul 2) ((hid (2*N) (by omega)).const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  have hb := mrt_normalized_short_energy (Finset.Ioc N (4*N))
    (fun n hn' => lt_trans hN (Finset.mem_Ioc.mp hn').1) b
    (N := (N:ℝ)) (h := (H:ℝ))
    (by exact_mod_cast hN) (by exact_mod_cast hH) (by exact_mod_cast hHN)
  have hl : (∫ x in (N:ℝ)..(2*N), ‖mrtIntervalSum (Finset.Ioc N (4*N)) b x H‖^2) =
      ∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (N:ℝ) ≤ 2*N)] at hx
    have he := mrt_finite_window_eq_short_sum b hHN hx 0
    simpa only [additiveCharacter, mul_zero, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one] using congrArg (fun z : ℂ => ‖z‖^2) he
  rw [hl] at hb
  calc
    _ ≤ _ := hb
    _ ≤ _ := (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_literal_short_energy_dyadic_oai := @OAI.TwoPointCorrelations.mrt_literal_short_energy_dyadic_oai
