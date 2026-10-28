-- Prove2me | solution 1 for OAI.SK.Analytic.sharedFieldEnergy_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:16:23.484028+00:00
-- url     : https://prove2.me/submissions/7cd696eb-4b83-4bdf-92b2-d867ea059e56

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_BilinearSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem bilinear_schur_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
    (hH : ∀ u v, H u v = H v u)
    (q : E → ℝ) (hq : q 0 = 0) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u s, c * (q u + s^2) ≤ H (u,s) (u,s)) (u : E) :
    0 < H (0,1) (0,1) ∧
    c * q u ≤ H (u,0) (u,0) - H (0,1) (u,0)^2 / H (0,1) (0,1) := by
  have hD : c ≤ H (0,1) (0,1) := by simpa [hq] using hlower 0 1
  have hD₀ := hc.trans_le hD
  refine ⟨hD₀, ?_⟩
  let A := H (u,0) (u,0)
  let B := H (0,1) (u,0)
  let D := H (0,1) (0,1)
  have heq (s : ℝ) : H (u,s) (u,s) = A + 2*s*B + s^2*D := by
    have hvec : (u,s) = (u,0) + s • (0,1) := by simp
    rw [hvec]
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    rw [hH (u,0) (0,1)]
    dsimp [A,B,D]
    ring
  have h := hlower u (-B/D)
  rw [heq] at h
  have hR : A + 2*(-B/D)*B + (-B/D)^2*D = A-B^2/D := by
    field_simp
    ring
  rw [hR] at h
  have hh : 0 ≤ c * (-B/D)^2 := mul_nonneg hc.le (sq_nonneg _)
  change c*q u ≤ A-B^2/D
  nlinarith

theorem hasDerivAt_affine_comp
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Differentiable ℝ f) (x u : E) (t : ℝ) :
    HasDerivAt (fun s => f (x+s • u)) (fderiv ℝ f (x+t • u) u) t := by
  have h := (hf (x+t • u)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const u |>.const_add x)
  simpa only [Function.comp_def, one_smul, id_eq] using h

theorem hasDerivAt_affine_score
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (x u v : E) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ V (x+s • u) v) (Hessian V (x+t • u) u v) t := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := hasDerivAt_affine_comp (fderiv ℝ V) hd x u t
  simpa only [map_zero, add_zero, Hessian] using h.clm_apply (hasDerivAt_const t v)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_BrascampLieb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem stein_brascampLieb_interval
    {a b : ℝ} (hab : a ≤ b) (f f₁ p V₁ V₂ g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hp : ∀ x, HasDerivAt p (-V₁ x * p x) x)
    (hV : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hg : ∀ x, HasDerivAt g (f x + V₁ x * g x) x)
    (hf₁c : Continuous f₁) (hV₂c : Continuous V₂)
    (hga : g a = 0) (hgb : g b = 0)
    (hp₀ : ∀ x, 0 ≤ p x) (hV₂ : ∀ x, 0 < V₂ x) :
    (∫ x in a..b, f x ^ 2 * p x) ≤
      ∫ x in a..b, f₁ x ^ 2 / V₂ x * p x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun x => (hp x).continuousAt
  have hVc : Continuous V₁ := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hgpc : Continuous (fun x => g x * p x) := hgc.mul hpc
  have hgp : ∀ x, HasDerivAt (fun x => g x * p x) (f x * p x) x := by
    intro x
    convert! (hg x).fun_mul (hp x) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hfirst : (∫ x in a..b, f x ^ 2 * p x) =
      -(∫ x in a..b, f₁ x * g x * p x) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun x _ => hf x) (fun x _ => hgp x)
      (hf₁c.intervalIntegrable a b) ((hfc.mul hpc).intervalIntegrable a b)
    simp only [hga, hgb, zero_mul, mul_zero, sub_self, zero_sub] at h
    simpa only [pow_two, mul_assoc] using h
  have hdg : ∀ x, HasDerivAt (fun x => g x ^ 2 * p x)
      ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x) x := by
    intro x
    convert! ((hg x).pow 2).fun_mul (hp x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.pow_apply]
    ring
  have hdc : Continuous (fun x =>
      (2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x) := by fun_prop
  have hboundary : (∫ x in a..b,
      V₂ x * (g x ^ 2 * p x) +
      V₁ x * ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x)) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (fun x _ => hV x) (fun x _ => hdg x)
      (hV₂c.intervalIntegrable a b) (hdc.intervalIntegrable a b)
    simpa [hga, hgb] using h
  have hAc : Continuous (fun x => V₂ x * g x ^ 2 * p x) := by fun_prop
  have hBc : Continuous (fun x => (f x + V₁ x * g x) ^ 2 * p x) := by fun_prop
  have hIc : Continuous (fun x => f x ^ 2 * p x) := by fun_prop
  have hDc : Continuous (fun x => V₂ x * (g x ^ 2 * p x) +
      V₁ x * ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x)) := by fun_prop
  have henergy : (∫ x in a..b, V₂ x * g x ^ 2 * p x) +
      (∫ x in a..b, (f x + V₁ x * g x) ^ 2 * p x) =
      ∫ x in a..b, f x ^ 2 * p x := by
    calc
      _ = (∫ x in a..b, V₂ x * (g x ^ 2 * p x) +
          V₁ x * ((2 * g x * (f x + V₁ x * g x) - V₁ x * g x ^ 2) * p x)) +
          ∫ x in a..b, f x ^ 2 * p x := by
        rw [← intervalIntegral.integral_add (hAc.intervalIntegrable a b) (hBc.intervalIntegrable a b),
          ← intervalIntegral.integral_add (hDc.intervalIntegrable a b) (hIc.intervalIntegrable a b)]
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by rw [hboundary, zero_add]
  have hB₀ : 0 ≤ ∫ x in a..b, (f x + V₁ x * g x) ^ 2 * p x :=
    intervalIntegral.integral_nonneg hab (fun x _ => mul_nonneg (sq_nonneg _) (hp₀ x))
  have hAle : (∫ x in a..b, V₂ x * g x ^ 2 * p x) ≤
      ∫ x in a..b, f x ^ 2 * p x := by linarith
  have hYc : Continuous (fun x => f₁ x ^ 2 / V₂ x * p x) := by
    exact ((hf₁c.pow 2).div hV₂c (fun x => ne_of_gt (hV₂ x))).mul hpc
  have hY : ∀ x, -2 * (f₁ x * g x * p x) ≤
      f₁ x ^ 2 / V₂ x * p x + V₂ x * g x ^ 2 * p x := by
    intro x
    have hsq : 0 ≤ (f₁ x + V₂ x * g x) ^ 2 / V₂ x :=
      div_nonneg (sq_nonneg _) (le_of_lt (hV₂ x))
    have heq : (f₁ x + V₂ x * g x) ^ 2 / V₂ x =
        f₁ x ^ 2 / V₂ x + 2 * f₁ x * g x + V₂ x * g x ^ 2 := by
      field_simp [ne_of_gt (hV₂ x)]
      ring
    rw [heq] at hsq
    have hprod := mul_nonneg hsq (hp₀ x)
    nlinarith
  have htwice : 2 * (∫ x in a..b, f x ^ 2 * p x) ≤
      (∫ x in a..b, f₁ x ^ 2 / V₂ x * p x) +
      ∫ x in a..b, V₂ x * g x ^ 2 * p x := by
    calc
      _ = ∫ x in a..b, -2 * (f₁ x * g x * p x) := by
        rw [intervalIntegral.integral_const_mul, hfirst]
        ring
      _ ≤ ∫ x in a..b, f₁ x ^ 2 / V₂ x * p x + V₂ x * g x ^ 2 * p x := by
        apply intervalIntegral.integral_mono_on hab
        · exact (((hf₁c.mul hgc).mul hpc).const_mul (-2)).intervalIntegrable a b
        · exact (hYc.add hAc).intervalIntegrable a b
        · intro x _
          exact hY x
      _ = _ := intervalIntegral.integral_add (hYc.intervalIntegrable a b) (hAc.intervalIntegrable a b)
  linarith

theorem intervalPartition_pos {V : ℝ → ℝ} (hV : Continuous V) {a b : ℝ} (hab : a < b) :
    0 < intervalPartition V a b := by
  apply intervalIntegral.integral_pos hab ((Real.continuous_exp.comp hV.neg).continuousOn)
  · intro x _
    exact le_of_lt (Real.exp_pos _)
  · exact ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩

theorem brascampLieb_interval
    {a b : ℝ} (hab : a < b) (V V₁ V₂ f f₁ : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hV₂c : Continuous V₂) (hf₁c : Continuous f₁)
    (hV₂ : ∀ x, 0 < V₂ x) :
    (∫ x in a..b, (f x - intervalMean V f a b) ^ 2 * Real.exp (-V x)) ≤
      ∫ x in a..b, f₁ x ^ 2 / V₂ x * Real.exp (-V x) := by
  let p : ℝ → ℝ := fun x => Real.exp (-V x)
  let m : ℝ := intervalMean V f a b
  let q : ℝ → ℝ := fun x => f x - m
  let U : ℝ → ℝ := fun x => ∫ y in a..x, q y * p y
  let g : ℝ → ℝ := fun x => U x / p x
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hpc : Continuous p := Real.continuous_exp.comp hVc.neg
  have hqc : Continuous q := hfc.sub continuous_const
  have hp₀ : ∀ x, 0 < p x := fun x => Real.exp_pos _
  have hp' : ∀ x, HasDerivAt p (-V₁ x * p x) x := by
    intro x
    convert! (hV x).neg.exp using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [p, Pi.neg_apply]
    ring
  have hq : ∀ x, HasDerivAt q (f₁ x) x := fun x => (hf x).sub_const m
  have hU : ∀ x, HasDerivAt U (q x * p x) x := fun x =>
    ((hqc.mul hpc).integral_hasStrictDerivAt a x).hasDerivAt
  have hg : ∀ x, HasDerivAt g (q x + V₁ x * g x) x := by
    intro x
    convert! (hU x).fun_div (hp' x) (ne_of_gt (hp₀ x)) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    field_simp [ne_of_gt (hp₀ x)]
    ring
  have hcentered : (∫ x in a..b, q x * p x) = 0 := by
    change (∫ x in a..b, (f x - m) * p x) = 0
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub ((show Continuous (fun x => f x * p x) from hfc.mul hpc).intervalIntegrable a b)
      ((show Continuous (fun x => m * p x) from hpc.const_mul m).intervalIntegrable a b), intervalIntegral.integral_const_mul]
    have hZ : (∫ x in a..b, p x) ≠ 0 := ne_of_gt (intervalPartition_pos hVc hab)
    dsimp only [m, intervalMean, intervalPartition, p]
    rw [div_mul_cancel₀ _ hZ, sub_self]
  have hga : g a = 0 := by simp [g, U]
  have hgb : g b = 0 := by
    change (∫ x in a..b, q x * p x) / p b = 0
    rw [hcentered, zero_div]
  exact stein_brascampLieb_interval hab.le q f₁ p V₁ V₂ g hq hp' hV₁ hg
    hf₁c hV₂c hga hgb (fun x => (hp₀ x).le) hV₂

theorem interval_centered_square (V f : ℝ → ℝ) (hV : Continuous V)
    (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, (f x - intervalMean V f a b) ^ 2 * Real.exp (-V x)) =
      (∫ x in a..b, f x ^ 2 * Real.exp (-V x)) -
      (∫ x in a..b, f x * Real.exp (-V x)) ^ 2 / intervalPartition V a b := by
  let m := intervalMean V f a b
  let p := fun x => Real.exp (-V x)
  have hp : Continuous p := Real.continuous_exp.comp hV.neg
  have hi₁ : IntervalIntegrable (fun x => f x ^ 2 * p x) volume a b :=
    ((hf.pow 2).mul hp).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun x => 2 * m * (f x * p x)) volume a b :=
    ((hf.mul hp).const_mul (2*m)).intervalIntegrable a b
  have hi₃ : IntervalIntegrable (fun x => m ^ 2 * p x) volume a b :=
    (hp.const_mul (m^2)).intervalIntegrable a b
  change (∫ x in a..b, (f x - m)^2*p x) = _
  simp_rw [show ∀ x, (f x-m)^2*p x = f x^2*p x - 2*m*(f x*p x) + m^2*p x by intro x; ring]
  rw [intervalIntegral.integral_add (hi₁.sub hi₂) hi₃,
    intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hZ := ne_of_gt (intervalPartition_pos hV hab)
  dsimp only [m, intervalMean, p]
  change _ = _ - _ / (∫ x in a..b, Real.exp (-V x))
  dsimp only [intervalPartition] at *
  field_simp
  ring

theorem brascampLieb_interval_variance
    {a b : ℝ} (hab : a < b) (V V₁ V₂ f f₁ : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hV₂c : Continuous V₂) (hf₁c : Continuous f₁)
    (hV₂ : ∀ x, 0 < V₂ x) :
    intervalMean V (fun x => f x ^ 2) a b - (intervalMean V f a b) ^ 2 ≤
      intervalMean V (fun x => f₁ x ^ 2 / V₂ x) a b := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hZ := intervalPartition_pos hVc hab
  have h := brascampLieb_interval hab V V₁ V₂ f f₁ hV hV₁ hf hV₂c hf₁c hV₂
  rw [interval_centered_square V f hVc hfc hab] at h
  have hdiv := div_le_div_of_nonneg_right h hZ.le
  convert! hdiv using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [intervalMean]
  field_simp

theorem brascampLieb_interval_schur
    {a b c : ℝ} (hab : a < b) (V V₁ V₂ f f₁ A : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, HasDerivAt V₁ (V₂ x) x)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hV₂c : Continuous V₂) (hf₁c : Continuous f₁) (hAc : Continuous A)
    (hV₂ : ∀ x, 0 < V₂ x)
    (hschur : ∀ x, c ≤ A x - f₁ x ^ 2 / V₂ x) :
    c ≤ intervalMean V A a b -
      (intervalMean V (fun x => f x ^ 2) a b - (intervalMean V f a b) ^ 2) := by
  have hBL := brascampLieb_interval_variance hab V V₁ V₂ f f₁ hV hV₁ hf hV₂c hf₁c hV₂
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt
  have hp : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp hVc.neg
  have hZ := intervalPartition_pos hVc hab
  have hFc : Continuous (fun x => f₁ x ^ 2 / V₂ x) :=
    (hf₁c.pow 2).div hV₂c (fun x => ne_of_gt (hV₂ x))
  have hmono : c * intervalPartition V a b ≤
      (∫ x in a..b, A x * Real.exp (-V x)) -
      (∫ x in a..b, (f₁ x ^ 2 / V₂ x) * Real.exp (-V x)) := by
    rw [intervalPartition, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((show Continuous (fun x => A x * Real.exp (-V x)) from hAc.mul hp).intervalIntegrable a b)
        ((show Continuous (fun x => (f₁ x^2/V₂ x) * Real.exp (-V x)) from hFc.mul hp).intervalIntegrable a b)]
    apply intervalIntegral.integral_mono_on hab.le
    · exact (hp.const_mul c).intervalIntegrable a b
    · exact ((hAc.mul hp).sub (hFc.mul hp)).intervalIntegrable a b
    · intro x _
      nlinarith [mul_le_mul_of_nonneg_right (hschur x) (Real.exp_pos (-V x)).le]
  have hS : c ≤ intervalMean V A a b - intervalMean V (fun x => f₁ x^2/V₂ x) a b := by
    dsimp only [intervalMean]
    rw [← sub_div, le_div_iff₀ hZ]
    exact hmono
  linarith

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_IntervalDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace SK.Analytic

theorem hasFDerivAt_intervalIntegral
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → ℝ → F) (f₁ : E → ℝ → E →L[ℝ] F)
    (hf : Continuous (Function.uncurry f)) (hf₁ : Continuous (Function.uncurry f₁))
    (hd : ∀ x y, HasFDerivAt (fun z => f z y) (f₁ x y) x)
    (a b : ℝ) (x : E) :
    HasFDerivAt (fun z => ∫ y in a..b, f z y) (∫ y in a..b, f₁ x y) x := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (show IsCompact (uIcc a b) from isCompact_uIcc)).exists_bound_of_continuousOn
    hf₁.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := f₁) (bound := fun _ => C) (s := Metric.closedBall x 1)
    (Metric.closedBall_mem_nhds x (by norm_num))
  · exact Filter.Eventually.of_forall fun z => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y hy z hz => hC (z, y) ⟨hz, uIoc_subset_uIcc hy⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun y _ z _ => hd z y

theorem contDiff_intervalIntegral
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : E × ℝ → F) (hf : ContDiff ℝ n f) (a b : ℝ) :
    ContDiff ℝ n (fun x => ∫ y in a..b, f (x, y)) := by
  induction n generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x y => f (x,y)) (by convert! hf.continuous using 1) a b
  | succ n ih =>
    let f₁ : E × ℝ → E →L[ℝ] F := fun p =>
      (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hf₁ : ContDiff ℝ n f₁ := by
      apply ContDiff.clm_comp _ contDiff_const
      exact hf.fderiv_right (by simp)
    have hdiff : ∀ x y, HasFDerivAt (fun z => f (z, y)) (f₁ (x,y)) x := by
      intro x y
      have hd := (hf.differentiable (by simp) (x, y)).hasFDerivAt
      exact hd.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
    have hI : ∀ x, HasFDerivAt (fun z => ∫ y in a..b, f (z,y))
        (∫ y in a..b, f₁ (x,y)) x := by
      intro x
      exact hasFDerivAt_intervalIntegral (fun x y => f (x,y))
        (fun x y => f₁ (x,y)) hf.continuous hf₁.continuous hdiff a b x
    rw [show (↑(n + 1) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hI x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun z => ∫ y in a..b, f (z,y)) =
          (fun x => ∫ y in a..b, f₁ (x,y)) := funext fun x => (hI x).fderiv
      rw [heq]
      exact ih f₁ hf₁

theorem hasDerivAt_intervalIntegral
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f f₁ : ℝ → ℝ → F)
    (hf : Continuous (Function.uncurry f)) (hf₁ : Continuous (Function.uncurry f₁))
    (hd : ∀ x y, HasDerivAt (fun z => f z y) (f₁ x y) x)
    (a b x : ℝ) :
    HasDerivAt (fun z => ∫ y in a..b, f z y) (∫ y in a..b, f₁ x y) x := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (show IsCompact (uIcc a b) from isCompact_uIcc)).exists_bound_of_continuousOn hf₁.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := f₁) (bound := fun _ => C) (s := Metric.closedBall x 1)
    (Metric.closedBall_mem_nhds x (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun z => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y hy z hz => hC (z, y) ⟨hz, uIoc_subset_uIcc hy⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun y _ z _ => hd z y

end SK.Analytic

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_MarginalVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem hasDerivAt_neg_log_intervalPartition
    (V V₁ : ℝ → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    (hV₁ : Continuous (Function.uncurry V₁))
    (hd : ∀ x y, HasDerivAt (fun z => V z y) (V₁ x y) x)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    HasDerivAt (fun z => -Real.log (intervalPartition (V z) a b))
      (intervalMean (V x) (V₁ x) a b) x := by
  let p : ℝ → ℝ → ℝ := fun x y => Real.exp (-V x y)
  have hp : Continuous (Function.uncurry p) := Real.continuous_exp.comp hV.neg
  have hp₁ : Continuous (fun z : ℝ × ℝ => -V₁ z.1 z.2 * p z.1 z.2) := hV₁.neg.mul hp
  have hpd : ∀ z y, HasDerivAt (fun w => p w y) (-V₁ z y * p z y) z := by
    intro z y
    convert! (hd z y).neg.exp using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [p]
    ring
  have hZ := hasDerivAt_intervalIntegral p (fun z y => -V₁ z y * p z y) hp hp₁ hpd a b x
  have hZ₀ : 0 < intervalPartition (V x) a b :=
    intervalPartition_pos (hV.comp (continuous_const.prodMk continuous_id)) hab
  have heq : (∫ y in a..b, -V₁ x y * p x y) = -(∫ y in a..b, V₁ x y * p x y) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  rw [heq] at hZ
  convert! (hZ.log (ne_of_gt hZ₀)).neg using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [intervalMean, intervalPartition, p]
  ring

theorem hasDerivAt_interval_score
    (V V₁ V₂ : ℝ → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    (hV₁ : Continuous (Function.uncurry V₁)) (hV₂ : Continuous (Function.uncurry V₂))
    (hd : ∀ x y, HasDerivAt (fun z => V z y) (V₁ x y) x)
    (hd₁ : ∀ x y, HasDerivAt (fun z => V₁ z y) (V₂ x y) x)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    HasDerivAt (fun z => intervalMean (V z) (V₁ z) a b)
      (intervalMean (V x) (V₂ x) a b -
        (intervalMean (V x) (fun y => V₁ x y ^ 2) a b -
          (intervalMean (V x) (V₁ x) a b)^2)) x := by
  let p : ℝ → ℝ → ℝ := fun x y => Real.exp (-V x y)
  have hp : Continuous (Function.uncurry p) := Real.continuous_exp.comp hV.neg
  have hp₁ : Continuous (fun z : ℝ × ℝ => -V₁ z.1 z.2 * p z.1 z.2) := hV₁.neg.mul hp
  have hpd : ∀ z y, HasDerivAt (fun w => p w y) (-V₁ z y * p z y) z := by
    intro z y
    convert! (hd z y).neg.exp using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [p]
    ring
  have hA : Continuous (fun z : ℝ × ℝ => V₁ z.1 z.2 * p z.1 z.2) := hV₁.mul hp
  have hA₁ : Continuous (fun z : ℝ × ℝ => (V₂ z.1 z.2 - V₁ z.1 z.2^2)*p z.1 z.2) :=
    (hV₂.sub (hV₁.pow 2)).mul hp
  have hAd : ∀ z y, HasDerivAt (fun w => V₁ w y * p w y)
      ((V₂ z y - V₁ z y^2)*p z y) z := by
    intro z y
    convert! (hd₁ z y).fun_mul (hpd z y) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hZ := hasDerivAt_intervalIntegral p (fun z y => -V₁ z y * p z y) hp hp₁ hpd a b x
  have hN := hasDerivAt_intervalIntegral (fun z y => V₁ z y*p z y)
    (fun z y => (V₂ z y - V₁ z y^2)*p z y) hA hA₁ hAd a b x
  have hZ₀ : 0 < intervalPartition (V x) a b :=
    intervalPartition_pos (hV.comp (continuous_const.prodMk continuous_id)) hab
  have heqZ : (∫ y in a..b, -V₁ x y * p x y) = -(∫ y in a..b, V₁ x y * p x y) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  have heqN : (∫ y in a..b, (V₂ x y - V₁ x y^2)*p x y) =
      (∫ y in a..b, V₂ x y*p x y) - (∫ y in a..b, V₁ x y^2*p x y) := by
    simp_rw [sub_mul]
    apply intervalIntegral.integral_sub
    · exact ((hV₂.comp (continuous_const.prodMk continuous_id)).mul
        (hp.comp (continuous_const.prodMk continuous_id))).intervalIntegrable a b
    · exact (((hV₁.comp (continuous_const.prodMk continuous_id)).pow 2).mul
        (hp.comp (continuous_const.prodMk continuous_id))).intervalIntegrable a b
  rw [heqZ] at hZ
  rw [heqN] at hN
  convert! hN.fun_div hZ (ne_of_gt hZ₀) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [intervalMean, intervalPartition, p]
  field_simp
  ring
end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_MarginalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
 theorem hasDerivAt_score_comp
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) {g : ℝ → E} {u : E} {t : ℝ}
    (hg : HasDerivAt g u t) (v : E) :
    HasDerivAt (fun s => fderiv ℝ V (g s) v) (Hessian V (g t) u v) t := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := (hd (g t)).hasFDerivAt.comp_hasDerivAt t hg
  simpa only [map_zero, add_zero, Function.comp_def, Hessian] using
    h.clm_apply (hasDerivAt_const t v)

theorem contDiff_marginalPotential
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E × ℝ → ℝ) (n : ℕ) (hV : ContDiff ℝ n V) {a b : ℝ} (hab : a < b) :
    ContDiff ℝ n (marginalPotential V a b) := by
  have hp : ContDiff ℝ n (fun z => Real.exp (-V z)) := hV.neg.exp
  have hZ := contDiff_intervalIntegral n (fun z => Real.exp (-V z)) hp a b
  exact (hZ.log (fun x => ne_of_gt (intervalPartition_pos
    (hV.continuous.comp (continuous_const.prodMk continuous_id)) hab))).neg

theorem marginal_hessian_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E × ℝ → ℝ) (hV : ContDiff ℝ 2 V)
    (q : E → ℝ) (hq : q 0 = 0) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ z u s, c * (q u + s^2) ≤ Hessian V z (u,s) (u,s))
    {a b : ℝ} (hab : a < b) (x u : E) :
    c*q u ≤ Hessian (marginalPotential V a b) x u u := by
  let g : ℝ × ℝ → E × ℝ := fun z => (x+z.1 • u, z.2)
  let e₁ : E × ℝ := (u,0)
  let e₂ : E × ℝ := (0,1)
  let v : ℝ → ℝ → ℝ := fun t y => V (g (t,y))
  let v₁ : ℝ → ℝ → ℝ := fun t y => fderiv ℝ V (g (t,y)) e₁
  let v₂ : ℝ → ℝ → ℝ := fun t y => Hessian V (g (t,y)) e₁ e₁
  let w₁ : ℝ → ℝ → ℝ := fun t y => fderiv ℝ V (g (t,y)) e₂
  let w₂ : ℝ → ℝ → ℝ := fun t y => Hessian V (g (t,y)) e₂ e₂
  let hxy : ℝ → ℝ → ℝ := fun t y => Hessian V (g (t,y)) e₂ e₁
  have hg : ContDiff ℝ 2 g := by dsimp only [g]; fun_prop
  have hd : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hdd : Continuous (fderiv ℝ (fderiv ℝ V)) := hd.continuous_fderiv (by norm_num)
  have hvc : Continuous (Function.uncurry v) := hV.continuous.comp hg.continuous
  have hdcont (e : E × ℝ) : Continuous (fun z => fderiv ℝ V (g z) e) :=
    (hd.continuous.comp hg.continuous).clm_apply continuous_const
  have hddcont (e e' : E × ℝ) : Continuous (fun z => Hessian V (g z) e e') :=
    ((hdd.comp hg.continuous).clm_apply continuous_const).clm_apply continuous_const
  have hg₁ (t y : ℝ) : HasDerivAt (fun s => g (s,y)) e₁ t := by
    simpa only [g, e₁, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const u).const_add x).prodMk (hasDerivAt_const t y)
  have hg₂ (t y : ℝ) : HasDerivAt (fun s => g (t,s)) e₂ y := by
    simpa only [g, e₂, id_eq] using
      (hasDerivAt_const y (x+t • u)).prodMk (hasDerivAt_id y)
  have hvd (t y : ℝ) : HasDerivAt (fun s => v s y) (v₁ t y) t := by
    exact (hV.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hg₁ t y)
  have hv₁d (t y : ℝ) : HasDerivAt (fun s => v₁ s y) (v₂ t y) t :=
    hasDerivAt_score_comp V hV (hg₁ t y) e₁
  have hwd (t y : ℝ) : HasDerivAt (v t) (w₁ t y) y := by
    exact (hV.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt y (hg₂ t y)
  have hw₁d (t y : ℝ) : HasDerivAt (w₁ t) (w₂ t y) y :=
    hasDerivAt_score_comp V hV (hg₂ t y) e₂
  have hv₁yd (t y : ℝ) : HasDerivAt (v₁ t) (hxy t y) y :=
    hasDerivAt_score_comp V hV (hg₂ t y) e₁
  have hs (t y : ℝ) : 0 < w₂ t y ∧ c*q u ≤ v₂ t y - hxy t y^2/w₂ t y := by
    apply bilinear_schur_lower (fderiv ℝ (fderiv ℝ V) (g (t,y)))
      (hV.contDiffAt.isSymmSndFDerivAt (by norm_num)) q hq hc
      (hlower (g (t,y))) u
  have hBL := brascampLieb_interval_schur hab (v 0) (w₁ 0) (w₂ 0) (v₁ 0)
    (hxy 0) (v₂ 0) (hwd 0) (hw₁d 0) (hv₁yd 0)
    ((hddcont e₂ e₂).comp (continuous_const.prodMk continuous_id))
    ((hddcont e₂ e₁).comp (continuous_const.prodMk continuous_id))
    ((hddcont e₁ e₁).comp (continuous_const.prodMk continuous_id))
    (fun y => (hs 0 y).1) (fun y => (hs 0 y).2)
  have hW := contDiff_marginalPotential V 2 hV hab
  have hfirst (t : ℝ) := hasDerivAt_neg_log_intervalPartition v v₁ hvc
    (hdcont e₁) hvd hab t
  have hsecond := hasDerivAt_interval_score v v₁ v₂ hvc (hdcont e₁)
    (hddcont e₁ e₁) hvd hv₁d hab 0
  have hscore : (fun t => fderiv ℝ (marginalPotential V a b) (x+t • u) u) =
      (fun t => intervalMean (v t) (v₁ t) a b) := by
    ext t
    exact (hasDerivAt_affine_comp (marginalPotential V a b)
      (hW.differentiable (by norm_num)) x u t).unique (hfirst t)
  have hsecond' := hasDerivAt_affine_score (marginalPotential V a b) hW x u u 0
  rw [hscore] at hsecond'
  have heq := hsecond'.unique hsecond
  simp only [zero_smul, add_zero] at heq
  rw [heq]
  exact hBL
end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterSpace
attribute [-instance] _root_.OAI.SK.Analytic.cubeFiniteMeasure _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem coordinateSquare_nonneg (n : ℕ) (z : ParameterSpace n) :
    0 ≤ coordinateSquare n z := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact add_nonneg (ih z.1) (sq_nonneg z.2)

theorem cubePotential_hessian_lower (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {c : ℝ} (hc : 0 < c)
    (hH : ∀ z u, c * coordinateSquare n u ≤ Hessian V z u u)
    {a b : ℝ} (hab : a < b) :
    ContDiff ℝ 2 (cubePotential n V a b) ∧
      ∀ x u, 0 ≤ Hessian (cubePotential n V a b) x u u := by
  induction n with
  | zero =>
    refine ⟨hV, ?_⟩
    intro x u
    change 0 ≤ Hessian V x u u
    simpa only [coordinateSquare, mul_zero] using hH x u
  | succ n ih =>
    apply ih (marginalPotential V a b) (contDiff_marginalPotential V 2 hV hab)
    intro z u
    apply marginal_hessian_lower V hV (coordinateSquare n) (coordinateSquare_zero n) hc
      (fun z u s => hH z (u,s)) hab

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterCalculus
attribute [-instance] _root_.OAI.SK.Analytic.cubeFiniteMeasure _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem parameterDerivative_intervalIntegral (n : ℕ) (f : ParameterSpace (n+1) → ℝ)
    (hf : ContDiff ℝ 1 f) (a b : ℝ) (x : ParameterSpace n) :
    parameterDerivative n (fun x => ∫ y in a..b, f (x,y)) x =
      ∫ y in a..b, parameterDerivative (n+1) f (x,y) := by
  let f₁ : ParameterSpace n × ℝ → ParameterSpace n →L[ℝ] ℝ := fun z =>
    (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ (ParameterSpace n) ℝ)
  have hf₁ : Continuous f₁ := (hf.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hd (x : ParameterSpace n) (y : ℝ) : HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x := by
    exact (hf.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  have hI := hasFDerivAt_intervalIntegral (fun x y => f (x,y)) (fun x y => f₁ (x,y))
    hf.continuous hf₁ hd a b x
  have hInt : IntervalIntegrable (fun y => f₁ (x,y)) volume a b :=
    (hf₁.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  rw [parameterDerivative, hI.fderiv, ContinuousLinearMap.intervalIntegral_apply hInt]
  rfl

theorem hasDerivAt_cubeIntegral (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 1 f) (a b x : ℝ) :
    HasDerivAt (cubeIntegral n f a b) (cubeIntegral n (parameterDerivative n f) a b x) x := by
  induction n with
  | zero => exact (hf.differentiable (by norm_num) x).hasFDerivAt.hasDerivAt
  | succ n ih =>
    have hh := ih (fun z => ∫ y in a..b, f (z,y)) (contDiff_intervalIntegral 1 f hf a b)
    have he : parameterDerivative n (fun z => ∫ y in a..b, f (z,y)) =
        fun z => ∫ y in a..b, parameterDerivative (n+1) f (z,y) := by
      funext z
      exact parameterDerivative_intervalIntegral n f hf a b z
    rw [he] at hh
    exact hh

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CubeMeasures
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem cubeSupport_compact (n : ℕ) (x a b : ℝ) : IsCompact (cubeSupport n x a b) := by
  induction n with
  | zero => exact isCompact_singleton
  | succ n ih => exact ih.prod isCompact_Icc

theorem ae_mem_cubeSupport (n : ℕ) (x a b : ℝ) :
    ∀ᵐ z ∂cubeMeasure n x a b, z ∈ cubeSupport n x a b := by
  induction n with
  | zero => simp [cubeMeasure, cubeSupport]
  | succ n ih =>
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (cubeSupport_compact (n+1) x a b).measurableSet).mpr
    filter_upwards [ih] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact ⟨hz, ⟨hy.1.le, hy.2⟩⟩

theorem integrable_cubeMeasure (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Continuous f) (x a b : ℝ) : Integrable f (cubeMeasure n x a b) := by
  obtain ⟨C, hC⟩ := (cubeSupport_compact n x a b).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [ae_mem_cubeSupport n x a b] with z hz
  exact hC z hz

theorem cubeIntegral_eq_measureIntegral (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    cubeIntegral n f a b x = ∫ z, f z ∂cubeMeasure n x a b := by
  induction n with
  | zero => exact (integral_dirac _ _).symm
  | succ n ih =>
    change cubeIntegral n (fun z => ∫ y in a..b, f (z,y)) a b x =
      ∫ z, f z ∂(cubeMeasure n x a b).prod (volume.restrict (Ioc a b))
    rw [integral_prod f (integrable_cubeMeasure (n+1) f hf x a b)]
    rw [ih _ (contDiff_zero.mp (contDiff_intervalIntegral 0 f (contDiff_zero.mpr hf) a b))]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => intervalIntegral.integral_of_le hab)

theorem cubeSet_measurable (n : ℕ) (a b : ℝ) : MeasurableSet (cubeSet n a b) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact ih.prod measurableSet_Ioc

theorem cubeMeasure_eq_restrict (n : ℕ) (x a b : ℝ) :
    cubeMeasure n x a b = (fiberMeasure n x).restrict (cubeSet n a b) := by
  induction n with
  | zero => simp [cubeMeasure, fiberMeasure, cubeSet]
  | succ n ih =>
    change (cubeMeasure n x a b).prod (volume.restrict (Ioc a b)) = _
    rw [ih, Measure.prod_restrict]
    rfl

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_HessianBounds
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem hessian_tangent_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (x u : E) {C : ℝ}
    (hH : ∀ t : ℝ, C ≤ Hessian V (x+t • u) u u) :
    V x + fderiv ℝ V x u + C/2 ≤ V (x+u) := by
  let f : ℝ → ℝ := fun t => V (x+t • u) - C/2*t^2
  let f₁ : ℝ → ℝ := fun t => fderiv ℝ V (x+t • u) u - C*t
  have hd (t : ℝ) : HasDerivAt f (f₁ t) t := by
    have hq : HasDerivAt (fun s : ℝ => C/2*s^2) (C*t) t := by
      convert! (((hasDerivAt_id t).pow 2).const_mul (C/2)) using 1
      all_goals try with_reducible_and_instances rfl
      dsimp
      ring
    exact (hasDerivAt_affine_comp V (hV.differentiable (by norm_num)) x u t).sub hq
  have hd₁ (t : ℝ) : HasDerivAt f₁ (Hessian V (x+t • u) u u-C) t := by
    convert! (hasDerivAt_affine_score V hV x u u t).sub ((hasDerivAt_id t).const_mul C) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have he : deriv f = f₁ := funext (fun t => (hd t).deriv)
  have hconv : ConvexOn ℝ univ f := convexOn_univ_of_deriv2_nonneg
    (fun t => (hd t).differentiableAt)
    (by rw [he]; exact fun t => (hd₁ t).differentiableAt)
    (by intro t; change 0 ≤ deriv (deriv f) t; rw [he, (hd₁ t).deriv]; exact sub_nonneg.mpr (hH t))
  have hs := hconv.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
      (by norm_num : (0 : ℝ) < 1) (hd 0)
  dsimp [slope, f, f₁] at hs
  simp only [zero_smul, add_zero, one_smul, zero_pow (by omega : 2 ≠ 0),
    one_pow, mul_zero, mul_one, sub_zero, inv_one, one_mul] at hs
  linarith

theorem integrable_coordinateGaussian (n : ℕ) (x : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z => Real.exp (-c*coordinateSquare n z)) (fiberMeasure n x) := by
  induction n with
  | zero => simp [coordinateSquare, fiberMeasure]
  | succ n ih =>
    have hi := ih.mul_prod (integrable_exp_neg_mul_sq hc)
    convert! hi using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    change Real.exp (-c*(coordinateSquare n z.1+z.2^2)) =
      Real.exp (-c*coordinateSquare n z.1)*Real.exp (-c*z.2^2)
    rw [mul_add, Real.exp_add]

theorem integrable_coordinateSquare_gaussian (n : ℕ) (x : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z => coordinateSquare n z * Real.exp (-c*coordinateSquare n z))
      (fiberMeasure n x) := by
  induction n with
  | zero => simp [coordinateSquare]
  | succ n ih =>
    have hi₀ := integrable_coordinateGaussian n x hc
    have hi₁ := integrable_exp_neg_mul_sq hc
    have hi₂ : Integrable (fun y : ℝ => y^2*Real.exp (-c*y^2)) := by
      simpa only [Real.rpow_natCast] using
        (integrable_rpow_mul_exp_neg_mul_sq hc (s := (2 : ℕ)) (by norm_num))
    have hi := (ih.mul_prod hi₁).add (hi₀.mul_prod hi₂)
    convert! hi using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    change (coordinateSquare n z.1+z.2^2)*Real.exp (-c*(coordinateSquare n z.1+z.2^2)) = _
    rw [mul_add, Real.exp_add]
    dsimp only [Pi.add_apply]
    ring

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateBounds
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem norm_sq_le_parameter_sq_add_coordinateSquare (n : ℕ) (z : ParameterSpace n) :
    ‖z‖^2 ≤ (parameter n z)^2 + coordinateSquare n z := by
  induction n with
  | zero => simp [coordinateSquare, parameter, Real.norm_eq_abs, sq_abs]
  | succ n ih =>
    change ‖(z.1,z.2)‖^2 ≤ (parameter n z.1)^2 + (coordinateSquare n z.1+z.2^2)
    rw [Prod.norm_def, max_def]
    split_ifs with hh
    · rw [Real.norm_eq_abs, sq_abs]
      nlinarith [coordinateSquare_nonneg n z.1, sq_nonneg (parameter n z.1)]
    · nlinarith [ih z.1, sq_nonneg z.2]

theorem ae_parameter_eq (n : ℕ) (x : ℝ) :
    ∀ᵐ z ∂fiberMeasure n x, parameter n z = x := by
  induction n with
  | zero => simp [fiberMeasure, parameter]
  | succ n ih =>
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      ((isClosed_eq (parameter (n+1)).continuous continuous_const).measurableSet)).mpr
    filter_upwards [ih] with z hz
    exact ae_of_all _ (fun _ => hz)

theorem potential_gaussian_lower (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {c : ℝ} (hc : 0 < c)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    (z : ParameterSpace n) (hz : parameter n z = 0) :
    V 0 - ‖fderiv ℝ V 0‖^2/c + c/4*coordinateSquare n z ≤ V z := by
  have ht := hessian_tangent_lower V hV 0 z (fun t => hH (0+t • z) z)
  rw [zero_add] at ht
  have hn := norm_sq_le_parameter_sq_add_coordinateSquare n z
  rw [hz, zero_pow (by omega : 2 ≠ 0), zero_add] at hn
  have hop := (fderiv ℝ V 0).le_opNorm z
  rw [Real.norm_eq_abs] at hop
  have hlo := (neg_le_abs (fderiv ℝ V 0 z)).trans hop
  have hy : ‖fderiv ℝ V 0‖*‖z‖ ≤ ‖fderiv ℝ V 0‖^2/c + c/4*coordinateSquare n z := by
    have hs : 0 ≤ (‖fderiv ℝ V 0‖ - c/2*‖z‖)^2/c := div_nonneg (sq_nonneg _) hc.le
    have he : (‖fderiv ℝ V 0‖ - c/2*‖z‖)^2/c =
        ‖fderiv ℝ V 0‖^2/c - ‖fderiv ℝ V 0‖*‖z‖ + c/4*‖z‖^2 := by
      field_simp
      ring
    rw [he] at hs
    nlinarith
  linarith

theorem continuous_coordinateSquare (n : ℕ) : Continuous (coordinateSquare n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (ih.comp continuous_fst).add (continuous_snd.pow 2)

theorem integrable_stronglyConvex_density (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {c : ℝ} (hc : 0 < c)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u) :
    Integrable (fun z => Real.exp (-V z)) (fiberMeasure n 0) ∧
    Integrable (fun z => coordinateSquare n z*Real.exp (-V z)) (fiberMeasure n 0) := by
  let K := Real.exp (‖fderiv ℝ V 0‖^2/c-V 0)
  have hqcont := continuous_coordinateSquare n
  have hbound : ∀ᵐ z ∂fiberMeasure n 0,
      Real.exp (-V z) ≤ K*Real.exp (-(c/4)*coordinateSquare n z) := by
    filter_upwards [ae_parameter_eq n 0] with z hz
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by have := potential_gaussian_lower n V hV hc hH z hz; linarith)
  constructor
  · apply ((integrable_coordinateGaussian n 0 (div_pos hc (by norm_num : (0:ℝ)<4))).const_mul K).mono'
      hV.neg.exp.continuous.aestronglyMeasurable
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz
  · apply ((integrable_coordinateSquare_gaussian n 0 (div_pos hc (by norm_num : (0:ℝ)<4))).const_mul K).mono'
      (hqcont.mul hV.neg.exp.continuous).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    change ‖coordinateSquare n z * Real.exp (-V z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coordinateSquare_nonneg n z) (Real.exp_pos _).le)]
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hz (coordinateSquare_nonneg n z)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_HessianAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
section HessianAlgebra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hessian_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x u v : E) : Hessian (fun z => f z+g z) x u v = Hessian f x u v + Hessian g x u v := by
  have hD : fderiv ℝ (fun z => f z+g z) = fun z => fderiv ℝ f z + fderiv ℝ g z := by
    funext z
    exact fderiv_add (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdSum : HasFDerivAt (fun z => fderiv ℝ f z + fderiv ℝ g z)
      (fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x) x :=
    (hdf x).hasFDerivAt.add (hdg x).hasFDerivAt
  rw [Hessian, hD, hdSum.fderiv]
  rfl

theorem hessian_const_mul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ)
    (x u v : E) : Hessian (fun z => c*f z) x u v = c * Hessian f x u v := by
  have hD : fderiv ℝ (fun z => c*f z) = fun z => c • fderiv ℝ f z := by
    funext z
    exact ((hf.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdMul : HasFDerivAt (fun z => c • fderiv ℝ f z)
      (c • fderiv ℝ (fderiv ℝ f) x) x := (hdf x).hasFDerivAt.const_smul c
  rw [Hessian, hD, hdMul.fderiv]
  rfl

theorem hessian_linear_product (a b : E →L[ℝ] ℝ) (x u v : E) :
    Hessian (fun z => a z*b z) x u v = a u*b v + b u*a v := by
  have hD : fderiv ℝ (fun z => a z*b z) = fun z => a z • b + b z • a := by
    funext z
    exact (a.hasFDerivAt.mul b.hasFDerivAt).fderiv
  have hdProd : HasFDerivAt (fun z => a z • b + b z • a)
      (a.smulRight b + b.smulRight a) x :=
    (a.hasFDerivAt.smul_const b).add (b.hasFDerivAt.smul_const a)
  rw [Hessian, hD, hdProd.fderiv]
  rfl

theorem hessian_tilt_lower {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (p L : E →L[ℝ] ℝ) (q : E → ℝ) {c ε A : ℝ}
    (hε : ε < c) (hA : 0 ≤ A) (hq : ∀ u, 0 ≤ q u)
    (hL : ∀ u, (L u)^2 ≤ A*q u)
    (hH : ∀ z u, c*q u ≤ Hessian V z u u) (z u : E) :
    ε*q u ≤ Hessian (fun z => V z - p z * L z + (A/(c-ε)/2)*(p z*p z)) z u u := by
  have hpL : ContDiff ℝ 2 (fun z => p z * L z) := p.contDiff.mul L.contDiff
  have hpp : ContDiff ℝ 2 (fun z => p z * p z) := p.contDiff.mul p.contDiff
  have heq : (fun z => V z-p z*L z+(A/(c-ε)/2)*(p z*p z)) =
      (fun z => (V z+(-1)*(p z*L z))+(A/(c-ε)/2)*(p z*p z)) := by funext z; ring
  rw [heq, hessian_add (hV.add (contDiff_const.mul hpL)) (contDiff_const.mul hpp),
    hessian_add hV (contDiff_const.mul hpL), hessian_const_mul hpL,
    hessian_const_mul hpp, hessian_linear_product, hessian_linear_product]
  have hd : 0 < c-ε := sub_pos.mpr hε
  have hbound : 2*(p u*L u) ≤ (c-ε)*q u + A/(c-ε)*(p u)^2 := by
    by_cases hAz : A = 0
    · have hLu : L u = 0 := by have := hL u; rw [hAz, zero_mul] at this; nlinarith [sq_nonneg (L u)]
      rw [hAz, zero_div, zero_mul, hLu, mul_zero, mul_zero, add_zero]
      exact mul_nonneg hd.le (hq u)
    · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
      have hC : 0 ≤ q u - (L u)^2/A := sub_nonneg.mpr ((div_le_iff₀ hAp).mpr (by simpa only [mul_comm] using hL u))
      have hF : 0 ≤ (c-ε)*(q u-(L u)^2/A) +
          (A*p u-(c-ε)*L u)^2/(A*(c-ε)) :=
        add_nonneg (mul_nonneg hd.le hC)
          (div_nonneg (sq_nonneg _) (mul_pos hAp hd).le)
      have he : (c-ε)*(q u-(L u)^2/A) +
          (A*p u-(c-ε)*L u)^2/(A*(c-ε)) =
          (c-ε)*q u + A/(c-ε)*(p u)^2 - 2*(p u*L u) := by
        field_simp
        ring
      linarith [he]
  have hVz := hH z u
  nlinarith
end HessianAlgebra
end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CubeDifferentiation
attribute [-instance] _root_.OAI.SK.Analytic.cubeFiniteMeasure _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem cubeIntegral_congr_parameter (n : ℕ) (f g : ParameterSpace n → ℝ)
    (a b x : ℝ) (he : ∀ z, parameter n z = x → f z = g z) :
    cubeIntegral n f a b x = cubeIntegral n g a b x := by
  induction n with
  | zero => exact he x rfl
  | succ n ih =>
    apply ih
    intro z hz
    apply intervalIntegral.integral_congr
    intro y _
    exact he (z,y) hz

theorem cubeIntegral_pos (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Continuous f) (hpos : ∀ z, 0 < f z) {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 < cubeIntegral n f a b x := by
  induction n with
  | zero => exact hpos x
  | succ n ih =>
    apply ih _ (contDiff_zero.mp (contDiff_intervalIntegral 0 f (contDiff_zero.mpr hf) a b))
    intro z
    apply intervalIntegral.integral_pos hab
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    · exact fun y _ => (hpos (z,y)).le
    · exact ⟨a, ⟨le_rfl, hab.le⟩, hpos (z,a)⟩

theorem cubeIntegral_const_mul (n : ℕ) (f : ParameterSpace n → ℝ) (c a b x : ℝ) :
    cubeIntegral n (fun z => c*f z) a b x = c*cubeIntegral n f a b x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cubeIntegral n (fun z => ∫ y in a..b, c*f (z,y)) a b x = _
    simp_rw [intervalIntegral.integral_const_mul]
    exact ih _

theorem cubeIntegral_sub (n : ℕ) (f g : ParameterSpace n → ℝ)
    (hf : Continuous f) (hg : Continuous g) (a b x : ℝ) :
    cubeIntegral n (fun z => f z-g z) a b x = cubeIntegral n f a b x-cubeIntegral n g a b x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hiF (z : ParameterSpace n) : IntervalIntegrable (fun y => f (z,y)) volume a b :=
      (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    have hiG (z : ParameterSpace n) : IntervalIntegrable (fun y => g (z,y)) volume a b :=
      (hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    change cubeIntegral n (fun z => ∫ y in a..b, f (z,y)-g (z,y)) a b x = _
    simp_rw [intervalIntegral.integral_sub (hiF _) (hiG _)]
    exact ih _ _ (contDiff_zero.mp (contDiff_intervalIntegral 0 f (contDiff_zero.mpr hf) a b))
      (contDiff_zero.mp (contDiff_intervalIntegral 0 g (contDiff_zero.mpr hg) a b))

theorem cubePotential_exp_eq (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) (x : ℝ) :
    Real.exp (-cubePotential n V a b x) = cubeIntegral n (fun z => Real.exp (-V z)) a b x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Real.exp (-cubePotential n (marginalPotential V a b) a b x) = _
    rw [ih _ (contDiff_marginalPotential _ 2 hV hab)]
    congr 1
    funext z
    dsimp only [marginalPotential]
    have hc : Continuous (fun y => V (z,y)) :=
      hV.continuous.comp (continuous_const.prodMk continuous_id)
    rw [neg_neg, Real.exp_log (intervalPartition_pos hc hab)]
    rfl

theorem cubePotential_eq_neg_log (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) :
    cubePotential n V a b = fun x => -Real.log (cubeIntegral n (fun z => Real.exp (-V z)) a b x) := by
  funext x
  rw [← cubePotential_exp_eq n V hV hab x, Real.log_exp, neg_neg]

theorem contDiff_cubePotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) :
    ContDiff ℝ 2 (cubePotential n V a b) := by
  induction n with
  | zero => exact hV
  | succ n ih => exact ih _ (contDiff_marginalPotential _ 2 hV hab)

theorem contDiff_parameterDerivative (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (parameterDerivative n f) :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem cubePotential_hessian_formula (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) (x : ℝ) :
    let w := fun z => Real.exp (-V z)
    let Z := cubeIntegral n w a b x
    let Z₁ := cubeIntegral n (parameterDerivative n w) a b x
    let Z₂ := cubeIntegral n (parameterDerivative n (parameterDerivative n w)) a b x
    Hessian (cubePotential n V a b) x 1 1 = (Z₁/Z)^2-Z₂/Z := by
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  have hw : ContDiff ℝ 2 w := hV.neg.exp
  let Z := cubeIntegral n w a b
  let Z₁ := cubeIntegral n (parameterDerivative n w) a b
  let Z₂ := cubeIntegral n (parameterDerivative n (parameterDerivative n w)) a b
  have hZpos (t : ℝ) : 0 < Z t := cubeIntegral_pos n w hw.continuous
    (fun _ => Real.exp_pos _) hab t
  have hD (t : ℝ) : HasDerivAt Z (Z₁ t) t :=
    hasDerivAt_cubeIntegral n w (hw.of_le (by norm_num)) a b t
  have hD₁ (t : ℝ) : HasDerivAt Z₁ (Z₂ t) t :=
    hasDerivAt_cubeIntegral n _ (contDiff_parameterDerivative n w hw) a b t
  have hM (t : ℝ) : HasDerivAt (cubePotential n V a b) (-(Z₁ t/Z t)) t := by
    rw [cubePotential_eq_neg_log n V hV hab]
    exact ((hD t).log (ne_of_gt (hZpos t))).neg
  have he : (fun t => fderiv ℝ (cubePotential n V a b) t 1) = fun t => -(Z₁ t/Z t) := by
    funext t
    exact (hM t).deriv
  have hH := hasDerivAt_score_comp (cubePotential n V a b)
    (contDiff_cubePotential n V hV hab) (hasDerivAt_id x) 1
  change HasDerivAt (fun t => fderiv ℝ (cubePotential n V a b) t 1)
    (Hessian (cubePotential n V a b) x 1 1) x at hH
  rw [he] at hH
  have hq := ((hD₁ x).div (hD x) (ne_of_gt (hZpos x))).neg
  have hh := hH.unique hq
  change Hessian (cubePotential n V a b) x 1 1 = (Z₁ x/Z x)^2-Z₂ x/Z x
  rw [hh]
  field_simp
  ring

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterProducts
attribute [-instance] _root_.OAI.SK.Analytic.cubeFiniteMeasure _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem parameterDerivative_mul (n : ℕ) (f g : ParameterSpace n → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (z : ParameterSpace n) :
    parameterDerivative n (fun z => f z*g z) z =
      f z*parameterDerivative n g z + g z*parameterDerivative n f z := by
  have hh : HasFDerivAt (fun z => f z*g z)
      (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    (hf z).hasFDerivAt.mul (hg z).hasFDerivAt
  rw [parameterDerivative, hh.fderiv]
  rfl

theorem parameterDerivative_exp_neg (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : Differentiable ℝ V) (z : ParameterSpace n) :
    parameterDerivative n (fun z => Real.exp (-V z)) z =
      -parameterDerivative n V z * Real.exp (-V z) := by
  have hh : HasFDerivAt (fun z => Real.exp (-V z))
      (Real.exp (-V z) • -fderiv ℝ V z) z := (hV z).hasFDerivAt.neg.exp
  rw [parameterDerivative, hh.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul]
  dsimp only [parameterDerivative]
  ring

theorem parameterDerivative2_exp_neg (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (z : ParameterSpace n) :
    parameterDerivative n (parameterDerivative n (fun z => Real.exp (-V z))) z =
      ((parameterDerivative n V z)^2 - parameterDerivative n (parameterDerivative n V) z) *
        Real.exp (-V z) := by
  have hvd := hV.differentiable (by norm_num)
  have hdv := (contDiff_parameterDerivative n V hV).differentiable (by norm_num)
  have he : parameterDerivative n (fun z => Real.exp (-V z)) =
      fun z => -parameterDerivative n V z * Real.exp (-V z) :=
    funext fun z => parameterDerivative_exp_neg n V hvd z
  have hneg : Differentiable ℝ (fun z => -parameterDerivative n V z) := hdv.neg
  rw [he, parameterDerivative_mul n _ _ hneg (hV.neg.exp.differentiable (by norm_num))]
  rw [parameterDerivative_exp_neg n V hvd z]
  have hn : parameterDerivative n (fun z => -parameterDerivative n V z) z =
      -parameterDerivative n (parameterDerivative n V) z := by
    have hh : HasFDerivAt (fun z => -parameterDerivative n V z)
        (-fderiv ℝ (parameterDerivative n V) z) z := (hdv z).hasFDerivAt.neg
    rw [parameterDerivative, hh.fderiv]
    rfl
  rw [hn]
  ring

theorem contDiff_tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (L : ParameterSpace n →L[ℝ] ℝ) (K : ℝ) :
    ContDiff ℝ 2 (tiltedPotential n V L K) :=
  (hV.sub ((parameter n).contDiff.mul L.contDiff)).add
    (contDiff_const.mul ((parameter n).contDiff.mul (parameter n).contDiff))

theorem parameterDerivative_tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : Differentiable ℝ V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL : L (parameterAxis n) = 0) (K : ℝ)
    (z : ParameterSpace n) :
    parameterDerivative n (tiltedPotential n V L K) z = K*parameter n z-L z := by
  let p := parameter n
  have hh : HasFDerivAt (tiltedPotential n V L K)
      (fderiv ℝ V z-(p z • L+L z • p)+(K/2) • (p z • p+p z • p)) z :=
    ((hV z).hasFDerivAt.sub (p.hasFDerivAt.mul L.hasFDerivAt)).add
      ((p.hasFDerivAt.mul p.hasFDerivAt).const_mul (K/2))
  rw [parameterDerivative, hh.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul,
    show p (parameterAxis n) = 1 from parameter_axis n, hL, mul_zero, mul_one]
  have hz := hV₀ z
  dsimp only [parameterDerivative] at hz
  rw [hz]
  dsimp only [p]
  ring

theorem parameterDerivative2_tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : Differentiable ℝ V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL : L (parameterAxis n) = 0) (K : ℝ)
    (z : ParameterSpace n) :
    parameterDerivative n (parameterDerivative n (tiltedPotential n V L K)) z = K := by
  have he : parameterDerivative n (tiltedPotential n V L K) = fun z => K*parameter n z-L z :=
    funext fun z => parameterDerivative_tiltedPotential n V hV hV₀ L hL K z
  rw [he]
  have hh : HasFDerivAt (fun z => K*parameter n z-L z) (K • parameter n - L) z :=
    ((parameter n).hasFDerivAt.const_mul K).sub L.hasFDerivAt
  rw [parameterDerivative, hh.fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul, parameter_axis, hL,
    mul_one, sub_zero]

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CubeVariance
attribute [-instance] _root_.OAI.SK.Analytic.cubeFiniteMeasure _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem cube_linear_variance_le_aux (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c ε A : ℝ} (hε : 0 < ε) (hεc : ε < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    {a b : ℝ} (hab : a < b) :
    let w := fun z => Real.exp (-V z)
    let Z := cubeIntegral n w a b 0
    cubeIntegral n (fun z => (L z)^2*w z) a b 0/Z -
      (cubeIntegral n (fun z => L z*w z) a b 0/Z)^2 ≤ A/(c-ε) := by
  let K := A/(c-ε)
  let T := tiltedPotential n V L K
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  let W : ParameterSpace n → ℝ := fun z => Real.exp (-T z)
  let Z := cubeIntegral n w a b 0
  let I₁ := cubeIntegral n (fun z => L z*w z) a b 0
  let I₂ := cubeIntegral n (fun z => (L z)^2*w z) a b 0
  have hT : ContDiff ℝ 2 T := contDiff_tiltedPotential n V hV L K
  have hessianT (z u : ParameterSpace n) : ε*coordinateSquare n u ≤ Hessian T z u u := by
    exact hessian_tilt_lower hV (parameter n) L (coordinateSquare n) hεc hA
      (coordinateSquare_nonneg n) hL hH z u
  have hpos := (cubePotential_hessian_lower n T hT hε hessianT hab).2 0 1
  have hformula := cubePotential_hessian_formula n T hT hab 0
  have hW (z : ParameterSpace n) (hz : parameter n z = 0) : W z = w z := by
    simp only [W, T, tiltedPotential, hz, zero_mul, sub_zero, mul_zero, add_zero, w]
  have hZ : 0 < Z := cubeIntegral_pos n w hV.neg.exp.continuous
    (fun _ => Real.exp_pos _) hab 0
  have hZeq : cubeIntegral n W a b 0 = Z :=
    cubeIntegral_congr_parameter n W w a b 0 hW
  have hZ₁eq : cubeIntegral n (parameterDerivative n W) a b 0 = I₁ := by
    apply cubeIntegral_congr_parameter
    intro z hz
    rw [parameterDerivative_exp_neg n T (hT.differentiable (by norm_num)),
      parameterDerivative_tiltedPotential n V (hV.differentiable (by norm_num)) hV₀ L hL₀]
    change -(K*parameter n z-L z)*W z = L z*w z
    rw [hz, mul_zero, zero_sub, neg_neg, hW z hz]
  have hZ₂eq : cubeIntegral n (parameterDerivative n (parameterDerivative n W)) a b 0 = I₂-K*Z := by
    have he := cubeIntegral_congr_parameter n
      (parameterDerivative n (parameterDerivative n W))
      (fun z => (L z)^2*w z-K*w z) a b 0 (by
        intro z hz
        rw [parameterDerivative2_exp_neg n T hT,
          parameterDerivative_tiltedPotential n V (hV.differentiable (by norm_num)) hV₀ L hL₀,
          parameterDerivative2_tiltedPotential n V (hV.differentiable (by norm_num)) hV₀ L hL₀]
        change ((K*parameter n z-L z)^2-K)*W z = _
        rw [hz, hW z hz]
        ring)
    have hcF : Continuous (fun z => (L z)^2*w z) := (L.continuous.pow 2).mul hV.neg.exp.continuous
    have hcG : Continuous (fun z => K*w z) := hV.neg.exp.continuous.const_mul K
    rw [he, cubeIntegral_sub n _ _ hcF hcG, cubeIntegral_const_mul]
  change Hessian (cubePotential n T a b) 0 1 1 =
    (cubeIntegral n (parameterDerivative n W) a b 0/cubeIntegral n W a b 0)^2 -
      cubeIntegral n (parameterDerivative n (parameterDerivative n W)) a b 0/cubeIntegral n W a b 0
    at hformula
  rw [hZeq, hZ₁eq, hZ₂eq] at hformula
  change I₂/Z-(I₁/Z)^2 ≤ K
  have he : (I₁/Z)^2-(I₂-K*Z)/Z = K-(I₂/Z-(I₁/Z)^2) := by
    field_simp
    ring
  rw [he] at hformula
  linarith

theorem cube_linear_variance_le (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    {a b : ℝ} (hab : a < b) :
    let w := fun z => Real.exp (-V z)
    let Z := cubeIntegral n w a b 0
    cubeIntegral n (fun z => (L z)^2*w z) a b 0/Z -
      (cubeIntegral n (fun z => L z*w z) a b 0/Z)^2 ≤ A/c := by
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  let Z := cubeIntegral n w a b 0
  let v := cubeIntegral n (fun z => (L z)^2*w z) a b 0/Z -
    (cubeIntegral n (fun z => L z*w z) a b 0/Z)^2
  change v ≤ A/c
  by_contra hh
  have hv : A/c < v := lt_of_not_ge hh
  have hvpos := lt_of_le_of_lt (div_nonneg hA hc.le) hv
  have hAv : A < v*c := (div_lt_iff₀ hc).mp hv
  have hAc : A/v < c := (div_lt_iff₀ hvpos).mpr (by nlinarith)
  let ε := (c-A/v)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεc : ε < c := by dsimp [ε]; have := div_nonneg hA hvpos.le; linarith
  have hbound := cube_linear_variance_le_aux n V hV hV₀ L hL₀ hε hεc hA hL hH hab
  change v ≤ A/(c-ε) at hbound
  have hstrict : A/(c-ε) < v := by
    apply (div_lt_iff₀ (sub_pos.mpr hεc)).mpr
    have he : A/v*v = A := div_mul_cancel₀ A (ne_of_gt hvpos)
    dsimp only [ε]
    nlinarith
  exact (lt_irrefl v) (hbound.trans_lt hstrict)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CubeMoments
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem cubeSet_mono (n : ℕ) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    cubeSet n a b ⊆ cubeSet n a' b' := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    intro z hz
    exact ⟨ih hz.1, ⟨ha.trans_lt hz.2.1, hz.2.2.trans hb⟩⟩

theorem mem_cubeSet_of_norm_lt (n : ℕ) (z : ParameterSpace n) {R : ℝ} (hR : ‖z‖ < R) :
    z ∈ cubeSet n (-R) R := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih z.1 ((norm_fst_le z).trans_lt hR), ?_⟩
    have hh := (norm_snd_le z).trans_lt hR
    rw [Real.norm_eq_abs] at hh
    exact ⟨(abs_lt.mp hh).1, (abs_lt.mp hh).2.le⟩

theorem cubeSet_iUnion (n : ℕ) : (⋃ R : ℕ, cubeSet n (-(R : ℝ)) R) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨R, hR⟩ := exists_nat_gt ‖z‖
  exact mem_iUnion.mpr ⟨R, mem_cubeSet_of_norm_lt n z hR⟩

theorem tendsto_cubeIntegral (n : ℕ) (f : ParameterSpace n → ℝ) (hf : Continuous f)
    (x : ℝ) (hi : Integrable f (fiberMeasure n x)) :
    Tendsto (fun R : ℕ => cubeIntegral n f (-(R : ℝ)) R x) atTop
      (𝓝 (∫ z, f z ∂fiberMeasure n x)) := by
  have hmono : Monotone (fun R : ℕ => cubeSet n (-(R : ℝ)) R) := by
    intro R S hRS
    exact cubeSet_mono n (neg_le_neg (Nat.cast_le.mpr hRS)) (Nat.cast_le.mpr hRS)
  have h := tendsto_setIntegral_of_monotone (fun R : ℕ => cubeSet_measurable n (-(R : ℝ)) R)
    hmono (hi.integrableOn : IntegrableOn f (⋃ R : ℕ, cubeSet n (-(R : ℝ)) R) (fiberMeasure n x))
  rw [cubeSet_iUnion, Measure.restrict_univ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext R
  rw [cubeIntegral_eq_measureIntegral n f hf (by linarith [Nat.cast_nonneg (α := ℝ) R]), cubeMeasure_eq_restrict]

theorem linear_variance_le (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    (hI₀ : Integrable (fun z => Real.exp (-V z)) (fiberMeasure n 0))
    (hI₁ : Integrable (fun z => L z*Real.exp (-V z)) (fiberMeasure n 0))
    (hI₂ : Integrable (fun z => (L z)^2*Real.exp (-V z)) (fiberMeasure n 0)) :
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A/c := by
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  have hw : Continuous w := hV.neg.exp.continuous
  have hw₁ : Continuous (fun z => L z*w z) := L.continuous.mul hw
  have hw₂ : Continuous (fun z => (L z)^2*w z) := (L.continuous.pow 2).mul hw
  have ht₀ := tendsto_cubeIntegral n w hw 0 hI₀
  have ht₁ := tendsto_cubeIntegral n (fun z => L z*w z) hw₁ 0 hI₁
  have ht₂ := tendsto_cubeIntegral n (fun z => (L z)^2*w z) hw₂ 0 hI₂
  have hZ : 0 < ∫ z, w z ∂fiberMeasure n 0 := integral_exp_pos hI₀
  apply le_of_tendsto ((ht₂.div ht₀ (ne_of_gt hZ)).sub
    ((ht₁.div ht₀ (ne_of_gt hZ)).pow 2))
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hRp : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  exact cube_linear_variance_le n V hV hV₀ L hL₀ hc hA hL hH (by linarith)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_StronglyConvexVariance
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem stronglyConvex_linear_variance_le (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u) :
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A/c := by
  obtain ⟨hI₀,hIq⟩ := integrable_stronglyConvex_density n V hV hc hH
  have hI₂ : Integrable (fun z => (L z)^2*Real.exp (-V z)) (fiberMeasure n 0) := by
    apply (hIq.const_mul A).mono' ((L.continuous.pow 2).mul hV.neg.exp.continuous).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(L z)^2*Real.exp (-V z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_right (hL z) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _)
  have hI₁ : Integrable (fun z => L z*Real.exp (-V z)) (fiberMeasure n 0) := by
    apply (hI₀.add hI₂).mono' (L.continuous.mul hV.neg.exp.continuous).aestronglyMeasurable
    filter_upwards [] with z
    change ‖L z*Real.exp (-V z)‖ ≤ Real.exp (-V z)+(L z)^2*Real.exp (-V z)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : |L z| ≤ 1+(L z)^2 := by nlinarith [sq_nonneg (|L z|-1), sq_abs (L z)]
    nlinarith [mul_le_mul_of_nonneg_right hle (Real.exp_pos (-V z)).le]
  exact linear_variance_le n V hV hV₀ L hL₀ hc hA hL hH hI₀ hI₁ hI₂

section HessianComposition
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hessian_comp_linear (V : F → ℝ) (hV : ContDiff ℝ 2 V) (T : E →L[ℝ] F)
    (x u v : E) : Hessian (fun z => V (T z)) x u v = Hessian V (T x) (T u) (T v) := by
  have hD : fderiv ℝ (fun z => V (T z)) = fun z => (fderiv ℝ V (T z)).comp T := by
    funext z
    exact ((hV.differentiable (by norm_num) (T z)).hasFDerivAt.comp z T.hasFDerivAt).fderiv
  have hdV := (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd := ((hdV (T x)).hasFDerivAt.comp x T.hasFDerivAt).clm_comp (hasFDerivAt_const T x)
  simp only [Function.comp_def] at hd
  rw [Hessian, hD, hd.fderiv]
  simp [Hessian]

theorem hessian_linear (L : E →L[ℝ] ℝ) (x u v : E) : Hessian L x u v = 0 := by
  have hD : fderiv ℝ (fun z => L z) = fun _ => L := funext (fun _ => L.hasFDerivAt.fderiv)
  change Hessian (fun z => L z) x u v = 0
  simp [Hessian, hD]

end HessianComposition

theorem contDiff_coordinateSquare (n : ℕ) : ContDiff ℝ 2 (coordinateSquare n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact (ih.comp contDiff_fst).add (contDiff_snd.pow 2)

theorem hessian_coordinateSquare (n : ℕ) (x u : ParameterSpace n) :
    Hessian (coordinateSquare n) x u u = 2*coordinateSquare n u := by
  induction n with
  | zero => simp [coordinateSquare, Hessian]
  | succ n ih =>
    let fst := ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
    let snd := ContinuousLinearMap.snd ℝ (ParameterSpace n) ℝ
    change Hessian (fun z => coordinateSquare n (fst z)+(snd z)^2) x u u = _
    have hf : ContDiff ℝ 2 (fun z => coordinateSquare n (fst z)) := (contDiff_coordinateSquare n).comp fst.contDiff
    rw [hessian_add hf (snd.contDiff.pow 2),
      hessian_comp_linear _ (contDiff_coordinateSquare n) fst]
    have hsq : (fun z => (snd z)^2) = fun z => snd z*snd z := by funext z; ring
    rw [hsq, hessian_linear_product, ih]
    change 2*coordinateSquare n u.1 + (u.2*u.2+u.2*u.2) = 2*(coordinateSquare n u.1+u.2^2)
    ring

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_HessianConvexity
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem hessian_nonneg_of_convex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V) (x u : E) :
    0 ≤ Hessian V x u u := by
  let f : ℝ → ℝ := fun t => V (x+t • u)
  have hfc : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    have h := hc.2 (mem_univ (x+a • u)) (mem_univ (x+b • u)) hs ht hst
    have he : s • (x+a • u)+t • (x+b • u) = x+(s*a+t*b) • u := by
      simp only [smul_add, smul_smul]
      rw [add_add_add_comm, ← add_smul, ← add_smul, hst, one_smul]
    simpa only [he, f, smul_eq_mul] using h
  have hdf (t : ℝ) := hasDerivAt_affine_comp V (hV.differentiable (by norm_num)) x u t
  have hd : deriv f = fun t => fderiv ℝ V (x+t • u) u := funext (fun t => (hdf t).deriv)
  have hm : Monotone (deriv f) := fun a b hab =>
    hfc.monotoneOn_deriv (fun t _ => (hdf t).differentiableAt) (mem_univ a) (mem_univ b) hab
  have hh := hm.deriv_nonneg (x := 0)
  rw [hd, (hasDerivAt_affine_score V hV x u u 0).deriv] at hh
  simpa only [zero_smul, add_zero] using hh

theorem coordinateSquare_add_parameterAxis (n : ℕ) (z : ParameterSpace n) (t : ℝ) :
    coordinateSquare n (z+t • parameterAxis n) = coordinateSquare n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change coordinateSquare n (z.1+t • parameterAxis n)+(z.2+t*(0:ℝ))^2 =
      coordinateSquare n z.1+z.2^2
    rw [ih, mul_zero, add_zero]

theorem parameterDerivative_coordinateSquare (n : ℕ) (z : ParameterSpace n) :
    parameterDerivative n (coordinateSquare n) z = 0 := by
  have hh := hasDerivAt_affine_comp (coordinateSquare n)
    ((contDiff_coordinateSquare n).differentiable (by norm_num)) z (parameterAxis n) 0
  have he : (fun t : ℝ => coordinateSquare n (z+t • parameterAxis n)) =
      fun _ => coordinateSquare n z := funext (coordinateSquare_add_parameterAxis n z)
  rw [he, zero_smul, add_zero] at hh
  exact hh.unique (hasDerivAt_const 0 (coordinateSquare n z))

theorem gaussian_convex_tilt_linear_variance (n : ℕ) (G : ParameterSpace n → ℝ)
    (hG : ContDiff ℝ 2 G) (hGc : ConvexOn ℝ univ G)
    (hG₀ : ∀ z, parameterDerivative n G z = 0)
    (U L : ParameterSpace n →L[ℝ] ℝ)
    (hU₀ : U (parameterAxis n) = 0) (hL₀ : L (parameterAxis n) = 0)
    {A : ℝ} (hA : 0 ≤ A) (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u) :
    let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A := by
  let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
  have hq := contDiff_coordinateSquare n
  have hV : ContDiff ℝ 2 V := ((contDiff_const.mul hq).sub U.contDiff).add hG
  have hV₀ : ∀ z, parameterDerivative n V z = 0 := by
    intro z
    have hd : HasFDerivAt V ((1/2 : ℝ) • fderiv ℝ (coordinateSquare n) z - U + fderiv ℝ G z) z :=
      (((hq.differentiable (by norm_num) z).hasFDerivAt.const_mul (1/2 : ℝ)).sub
        U.hasFDerivAt).add (hG.differentiable (by norm_num) z).hasFDerivAt
    change fderiv ℝ V z (parameterAxis n) = 0
    rw [hd.fderiv]
    change (1/2 : ℝ)*parameterDerivative n (coordinateSquare n) z - U (parameterAxis n) +
      parameterDerivative n G z = 0
    rw [parameterDerivative_coordinateSquare, hU₀, hG₀]
    ring
  have hH : ∀ z u, (1:ℝ)*coordinateSquare n u ≤ Hessian V z u u := by
    intro z u
    have he : V = fun z => ((1/2 : ℝ)*coordinateSquare n z + (-1)*U z)+G z := by
      funext z; dsimp only [V]; ring
    rw [he, hessian_add ((contDiff_const.mul hq).add (contDiff_const.mul U.contDiff)) hG,
      hessian_add (contDiff_const.mul hq) (contDiff_const.mul U.contDiff),
      hessian_const_mul hq, hessian_const_mul U.contDiff, hessian_linear,
      hessian_coordinateSquare]
    nlinarith [hessian_nonneg_of_convex G hG hGc z u]
  simpa only [div_one] using stronglyConvex_linear_variance_le n V hV hV₀ L hL₀
    (by norm_num : (0:ℝ)<1) hA hL hH

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LogIntegralConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section LogIntegralConvexity
variable {E Ω : Type} [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace Ω]

theorem convexOn_log_integral_exp (μ : Measure Ω) [NeZero μ]
    (f : E → Ω → ℝ) (hi : ∀ x, Integrable (fun y => Real.exp (f x y)) μ)
    (hc : ∀ y, ConvexOn ℝ univ (fun x => f x y)) :
    ConvexOn ℝ univ (fun x => Real.log (∫ y, Real.exp (f x y) ∂μ)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  let X := ∫ y, Real.exp (f x y) ∂μ
  let Z := ∫ y, Real.exp (f z y) ∂μ
  have hX : 0 < X := integral_exp_pos (hi x)
  have hZ : 0 < Z := integral_exp_pos (hi z)
  let c := a*Real.log X+b*Real.log Z
  have hbnd : ∀ y, Real.exp (f (a • x+b • z) y) ≤
      Real.exp c*(a*(Real.exp (f x y)/X)+b*(Real.exp (f z y)/Z)) := by
    intro y
    have hfc := (hc y).2 (mem_univ x) (mem_univ z) ha hb hab
    simp only [smul_eq_mul] at hfc
    have he := convexOn_exp.2 (mem_univ (f x y-Real.log X))
      (mem_univ (f z y-Real.log Z)) ha hb hab
    simp only [smul_eq_mul] at he
    have hcmp : f (a • x+b • z) y-c ≤
        a*(f x y-Real.log X)+b*(f z y-Real.log Z) := by dsimp [c]; linarith
    have hpre := (Real.exp_le_exp.mpr hcmp).trans he
    rw [Real.exp_sub (f x y) (Real.log X), Real.exp_log hX,
      Real.exp_sub (f z y) (Real.log Z), Real.exp_log hZ] at hpre
    calc
      Real.exp (f (a • x+b • z) y) = Real.exp c * Real.exp (f (a • x+b • z) y-c) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpre (Real.exp_pos _).le
  have hbint : Integrable (fun y => Real.exp c*(a*(Real.exp (f x y)/X)+
      b*(Real.exp (f z y)/Z))) μ :=
    (((hi x).div_const X).const_mul a |>.add (((hi z).div_const Z).const_mul b)).const_mul _
  have hh := integral_mono (hi (a • x+b • z)) hbint hbnd
  have hright : (∫ y, Real.exp c*(a*(Real.exp (f x y)/X)+
      b*(Real.exp (f z y)/Z)) ∂μ) = Real.exp c := by
    rw [integral_const_mul, integral_add (((hi x).div_const X).const_mul a)
      (((hi z).div_const Z).const_mul b), integral_const_mul, integral_const_mul,
      integral_div, integral_div]
    change Real.exp c*(a*(X/X)+b*(Z/Z)) = Real.exp c
    rw [div_self hX.ne', div_self hZ.ne', mul_one, mul_one, hab, mul_one]
  rw [hright] at hh
  have hp : 0 < ∫ y, Real.exp (f (a • x+b • z) y) ∂μ :=
    integral_exp_pos (hi _)
  change Real.log (∫ y, Real.exp (f (a • x+b • z) y) ∂μ) ≤ c
  apply Real.exp_le_exp.mp
  simpa only [Real.exp_log hp] using hh

end LogIntegralConvexity
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section SmoothRecursion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positiveGaussianLogStep_convex {f : E × ℝ → ℝ} (hc : ConvexOn ℝ univ f)
    (hd : Differentiable ℝ f) (C : ℝ) (hC₀ : 0 ≤ C)
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) {m : ℝ} (hm : 0 < m) :
    ConvexOn ℝ univ (positiveGaussianLogStep m f) := by
  have hi : ∀ x, Integrable (fun y => Real.exp (m*f (x,y))) (gaussianReal 0 1) :=
    (exp_mul_growth_of_fderiv_bound f hd C hC₀ hC m).integrable_gaussian_section
      (Real.continuous_exp.comp (continuous_const.mul hd.continuous))
  have hcx : ∀ y, ConvexOn ℝ univ (fun x => m*f (x,y)) := by
    intro y
    refine ⟨convex_univ, ?_⟩
    intro x _ z _ a b ha hb hab
    have hh := hc.2 (mem_univ (x,y)) (mem_univ (z,y)) ha hb hab
    have he : a • (x,y)+b • (z,y) = (a • x+b • z,y) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    rw [he] at hh
    simp only [smul_eq_mul] at hh ⊢
    nlinarith [mul_le_mul_of_nonneg_left hh hm.le]
  have hg := convexOn_log_integral_exp (gaussianReal 0 1) (fun x y => m*f (x,y)) hi hcx
  have hi := hg.smul (inv_nonneg.mpr hm.le)
  change ConvexOn ℝ univ (fun x => Real.log
    (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) / m)
  simpa only [div_eq_mul_inv, mul_comm, smul_eq_mul] using hi

end SmoothRecursion
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianZeroMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section ZeroMass
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussian_integral_convex {f : E × ℝ → ℝ} (hc : ConvexOn ℝ univ f)
    (hf : BoundedDerivs f) : ConvexOn ℝ univ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hg := growth_of_fderiv_bound f (hf.differentiable (by norm_num)) hC hb
  have hi := hg.integrable_gaussian_section hf.continuous
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi x).const_mul a) ((hi z).const_mul b)]
  apply integral_mono (hi _) (((hi x).const_mul a).add ((hi z).const_mul b))
  intro y
  have hh := hc.2 (mem_univ (x,y)) (mem_univ (z,y)) ha hb hab
  have he : a • (x,y)+b • (z,y) = (a • x+b • z,y) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  simpa only [he, smul_eq_mul, Pi.add_apply] using hh

theorem RegularConvex.gaussianStep {f : E × ℝ → ℝ} (hf : RegularConvex f) {m : ℝ} (hm : 0 ≤ m) :
    RegularConvex (gaussianStep m f) := by
  rcases eq_or_lt_of_le hm with he | hm
  · subst m
    have heq : SK.Analytic.gaussianStep 0 f = (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
      funext x
      simp only [SK.Analytic.gaussianStep, ite_true]
    rw [heq]
    exact ⟨hf.1.gaussian_integral, gaussian_integral_convex hf.2 hf.1⟩
  · have hne := hm.ne'
    have hb := hf.1.positiveGaussianLogStep m
    obtain ⟨hd,C,D,hC,hD,hb₁,hb₂⟩ := hf.1
    have hc := positiveGaussianLogStep_convex hf.2 (hd.differentiable (by norm_num)) C hC hb₁ hm
    have heq : SK.Analytic.gaussianStep m f = positiveGaussianLogStep m f := by
      funext x
      simp only [SK.Analytic.gaussianStep, ite_eq_right_iff.mpr fun he => (hne he).elim]
    rw [heq]
    exact ⟨hb,hc⟩

end ZeroMass
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_RegularAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section RegularAlgebra
variable {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem RegularConvex.add {f g : E → ℝ} (hf : RegularConvex f) (hg : RegularConvex g) :
    RegularConvex (fun x => f x+g x) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem RegularConvex.const_mul {f : E → ℝ} (hf : RegularConvex f) {m : ℝ} (hm : 0 ≤ m) :
    RegularConvex (fun x => m*f x) := by
  refine ⟨hf.1.const_mul m, ?_⟩
  simpa only [smul_eq_mul] using hf.2.smul hm

theorem RegularConvex.compCLM {f : E → ℝ} (hf : RegularConvex f) (L : D →L[ℝ] E) :
    RegularConvex (fun x => f (L x)) := by
  refine ⟨hf.1.compCLM L, ?_⟩
  exact hf.2.comp_linearMap L.toLinearMap

end RegularAlgebra
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section FinitePartition
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem affineLogPartition_convex (c : S → ℝ) (L : S → E →L[ℝ] ℝ) :
    ConvexOn ℝ univ (affineLogPartition c L) := by
  let : MeasurableSpace S := ⊤
  have hc : ∀ s, ConvexOn ℝ univ (fun x => c s+L s x) := by
    intro s
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t * c s) hab]
  have h := convexOn_log_integral_exp (Measure.count : Measure S)
    (fun x s => c s+L s x) (fun _ => Integrable.of_finite) hc
  change ConvexOn ℝ univ (fun x => Real.log (∑ s, Real.exp (c s+L s x)))
  simpa only [integral_count] using h

end FinitePartition
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPenalty
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem hierarchyPenalty_regular (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : RegularConvex f) :
    RegularConvex (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero => exact hf.const_mul hu
  | succ n ih =>
    have hg := hf.gaussianStep (hm (Fin.last n))
    have hmg : Monotone (fun i : Fin n => m i.castSucc) := by
      intro i j hij
      exact hmono (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hp := ih (fun i => m i.castSucc) (m (Fin.last n)) (hm (Fin.last n))
      (fun i => hm i.castSucc) (fun i => hmono (Fin.le_last _)) hmg
      (gaussianStep (m (Fin.last n)) f) hg
    exact ((hf.const_mul (sub_nonneg.mpr (hmu (Fin.last n)))).add
      (hp.compCLM (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)))

theorem hierarchy_fixed_spin_density (n : ℕ) (m : Fin n → ℝ)
    (f U : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z * Real.exp (U z-f z) =
      Real.exp (U z-hierarchyPenalty n m 1 f z) := by
  rw [hierarchyPathWeight_eq n m f 1, ← Real.exp_add]
  apply congrArg Real.exp
  ring

theorem parameterDerivative_zero_of_invariant (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Differentiable ℝ f) (hfi : ParameterInvariant n f) :
    ∀ z, parameterDerivative n f z = 0 := by
  intro z
  have hd := hasDerivAt_affine_comp f hf z (parameterAxis n) 0
  have he : (fun t : ℝ => f (z+t • parameterAxis n)) = fun _ => f z := funext (hfi z)
  rw [he] at hd
  simpa only [parameterDerivative,zero_smul,add_zero] using
    hd.unique (hasDerivAt_const 0 (f z))

theorem ParameterInvariant.gaussianStep {n : ℕ} {f : ParameterSpace (n+1) → ℝ}
    (hf : ParameterInvariant (n+1) f) (m : ℝ) :
    ParameterInvariant n (gaussianStep m f) := by
  intro z t
  have he (y : ℝ) : f (z+t • parameterAxis n,y) = f (z,y) := by
    simpa only [parameterAxis,Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hf (z,y) t
  unfold SK.Analytic.gaussianStep positiveGaussianLogStep
  simp only [he]

theorem hierarchyPenalty_invariant (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : ParameterInvariant n f) :
    ParameterInvariant n (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero =>
    intro z t
    simp only [hierarchyPenalty,hf z t]
  | succ n ih =>
    have hp := ih (fun i => m i.castSucc) (m (Fin.last n)) _ (hf.gaussianStep (m (Fin.last n)))
    intro z t
    change (u-m (Fin.last n))*f (z+t • parameterAxis (n+1)) +
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) (z.1+t • parameterAxis n) = _
    rw [hf z t, hp z.1 t]
    rfl

theorem hierarchy_fixed_spin_linear_variance
    {S : Type} [Fintype S] [Nonempty S] (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, U s (parameterAxis n) = 0) (s : S)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {A : ℝ} (hA : 0 ≤ A) (hL : ∀ z, (L z)^2 ≤ A*coordinateSquare n z) :
    let f := affineLogPartition c U
    let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U s z+hierarchyPenalty n m 1 f z
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A := by
  let f := affineLogPartition c U
  have hf : RegularConvex f := ⟨affineLogPartition_boundedDerivs c U,affineLogPartition_convex c U⟩
  have hfi : ParameterInvariant n f := by
    intro z t
    unfold f affineLogPartition
    simp only [map_add,map_smul,hU,smul_eq_mul,mul_zero,add_zero]
  have hg := hierarchyPenalty_regular n m 1 zero_le_one hm hmu hmono f hf
  exact gaussian_convex_tilt_linear_variance n _ hg.1.1 hg.2
    (parameterDerivative_zero_of_invariant n _ (hg.1.1.differentiable (by norm_num))
      (hierarchyPenalty_invariant n m 1 f hfi)) (U s) L (hU s) hL₀ hA hL

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateSigns
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem scalarSign_gaussian (b : Bool) :
    MeasurePreserving (scalarSign b) (gaussianReal 0 1) (gaussianReal 0 1) := by
  refine ⟨(scalarSign_continuous b).measurable, ?_⟩
  cases b
  · simp only [scalarSign_false,Measure.map_id]
  · simpa only [scalarSign_true,neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))

theorem scalarSign_volume (b : Bool) :
    MeasurePreserving (scalarSign b) (volume : Measure ℝ) volume := by
  cases b
  · simpa only [scalarSign_false] using
      (MeasurePreserving.id (volume : Measure ℝ))
  · simpa only [scalarSign_true] using Measure.measurePreserving_neg (volume : Measure ℝ)

theorem coordinateSign_square (n : ℕ) (b : Fin n → Bool) (z : ParameterSpace n) :
    coordinateSquare n (coordinateSign n b z) = coordinateSquare n z := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [coordinateSign,coordinateSquare,ih,scalarSign_square]

theorem coordinateSign_fiber (n : ℕ) (b : Fin n → Bool) (t : ℝ) :
    MeasurePreserving (coordinateSign n b) (fiberMeasure n t) (fiberMeasure n t) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    exact (ih (fun i => b i.castSucc)).prod (scalarSign_volume (b (Fin.last n)))

theorem gaussianStep_sign {n : ℕ} {f : ParameterSpace (n+1) → ℝ} (b : Fin (n+1) → Bool)
    (hf : ∀ z, f (coordinateSign (n+1) b z) = f z) (m : ℝ) (z : ParameterSpace n) :
    gaussianStep m f (coordinateSign n (fun i => b i.castSucc) z) = gaussianStep m f z := by
  have he (y : ℝ) : f (coordinateSign n (fun i => b i.castSucc) z,y) =
      f (z,scalarSign (b (Fin.last n)) y) := by
    simpa only [coordinateSign,scalarSign_involutive] using
      hf (z,scalarSign (b (Fin.last n)) y)
  have hi (g : ℝ → ℝ) : (∫ y, g (scalarSign (b (Fin.last n)) y) ∂gaussianReal 0 1) =
      ∫ y, g y ∂gaussianReal 0 1 :=
    (scalarSign_gaussian _).integral_comp (scalarSignEquiv _).measurableEmbedding g
  unfold gaussianStep positiveGaussianLogStep
  simp only [he]
  rw [hi (fun y => f (z,y)), hi (fun y => Real.exp (m*f (z,y)))]

theorem hierarchyPenalty_sign (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (b : Fin n → Bool)
    (hf : ∀ z, f (coordinateSign n b z) = f z) (z : ParameterSpace n) :
    hierarchyPenalty n m u f (coordinateSign n b z) = hierarchyPenalty n m u f z := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    change (u-m (Fin.last n))*f (coordinateSign (n+1) b z) +
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) (coordinateSign n (fun i => b i.castSucc) z.1) = _
    rw [hf, ih _ _ _ _ (gaussianStep_sign b hf (m (Fin.last n)))]
    rfl

theorem affineLogPartition_sign {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (b : Fin n → Bool) (p : Equiv.Perm S)
    (hc : ∀ s, c (p s) = c s) (hU : ∀ s z, U s (coordinateSign n b z) = U (p s) z)
    (z : ParameterSpace n) :
    affineLogPartition c U (coordinateSign n b z) = affineLogPartition c U z := by
  unfold affineLogPartition
  congr 1
  have he : (fun s => Real.exp (c s+U s (coordinateSign n b z))) =
      fun s => Real.exp (c (p s)+U (p s) z) := by
    funext s; rw [hc,hU]
  rw [he]
  exact Equiv.sum_comp p (fun s : S => Real.exp (c s+U s z))

theorem fixed_spin_gauge_integral (n : ℕ) (m : Fin n → ℝ)
    {S : Type} [Fintype S] [Nonempty S]
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (b : Fin n → Bool) (p : Equiv.Perm S)
    (hc : ∀ s, c (p s) = c s) (hU : ∀ s z, U s (coordinateSign n b z) = U (p s) z)
    (s : S) (g g' : ParameterSpace n → ℝ)
    (hg : ∀ z, g (coordinateSign n b z) = g' z) :
    (∫ z, g z * Real.exp (-(1/2 : ℝ)*coordinateSquare n z + U s z -
        hierarchyPenalty n m 1 (affineLogPartition c U) z) ∂fiberMeasure n 0) =
    (∫ z, g' z * Real.exp (-(1/2 : ℝ)*coordinateSquare n z + U (p s) z -
        hierarchyPenalty n m 1 (affineLogPartition c U) z) ∂fiberMeasure n 0) := by
  have hfs := affineLogPartition_sign n c U b p hc hU
  have hp := hierarchyPenalty_sign n m 1 (affineLogPartition c U) b hfs
  have hi := (coordinateSign_fiber n b 0).integral_comp
    (coordinateSignEquiv n b).measurableEmbedding
    (fun z => g z * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s z-
      hierarchyPenalty n m 1 (affineLogPartition c U) z))
  rw [← hi]
  congr 1
  funext z
  rw [hg,coordinateSign_square,hU,hp]

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_FiberGaussian
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem fiberGaussianDensity_pos (n : ℕ) (z : ParameterSpace n) :
    0 < fiberGaussianDensity n z := by
  unfold fiberGaussianDensity
  positivity

theorem fiberGaussianDensity_continuous (n : ℕ) : Continuous (fiberGaussianDensity n) := by
  exact continuous_const.mul (Real.continuous_exp.comp
    ((continuous_coordinateSquare n).neg.div_const 2))

theorem fiberGaussianDensity_succ (n : ℕ) (z : ParameterSpace (n+1)) :
    fiberGaussianDensity (n+1) z = fiberGaussianDensity n z.1*gaussianPDFReal 0 1 z.2 := by
  unfold fiberGaussianDensity gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero,coordinateSquare]
  rw [pow_succ _ n]
  rw [show -(coordinateSquare n z.1+z.2^2)/2 = -coordinateSquare n z.1/2 + -z.2^2/2 by ring,
    Real.exp_add]
  ring

theorem fiberGaussian_eq_withDensity (n : ℕ) (x : ℝ) :
    fiberGaussian n x = (fiberMeasure n x).withDensity
      (fun z => ENNReal.ofReal (fiberGaussianDensity n z)) := by
  induction n with
  | zero => simp [fiberGaussian,fiberMeasure,fiberGaussianDensity,coordinateSquare]
  | succ n ih =>
    rw [fiberGaussian,ih,gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
      prod_withDensity (fiberGaussianDensity_continuous n).measurable.ennreal_ofReal
        (measurable_gaussianPDF _ _)]
    apply congrArg ((fiberMeasure (n+1) x).withDensity)
    funext z
    rw [fiberGaussianDensity_succ,ENNReal.ofReal_mul (fiberGaussianDensity_pos n z.1).le]
    rfl

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyJointMoment
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem hierarchy_gauge_linear_variance
    {S : Type} [Fintype S] [Nonempty S] (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    (hU₀ : ∀ s, U s (parameterAxis n) = 0)
    (hL₀ : ∀ s, L s (parameterAxis n) = 0)
    {A : ℝ} (hA : 0 ≤ A) (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    (s₀ : S) (b : S → Fin n → Bool) (p : S → Equiv.Perm S)
    (hp : ∀ s, p s s = s₀)
    (hUg : ∀ s r z, U r (coordinateSign n (b s) z) = U (p s r) z)
    (hLg : ∀ s z, L s (coordinateSign n (b s) z) = L s₀ z) :
    hierarchyJointMoment n m U L 2 / hierarchyJointMoment n m U L 0 -
      (hierarchyJointMoment n m U L 1 / hierarchyJointMoment n m U L 0)^2 ≤ A := by
  let I (a : ℕ) := ∫ z, (L s₀ z)^a * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s₀ z-
    hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) ∂fiberMeasure n 0
  have he (a : ℕ) (s : S) :
      (∫ z, (L s z)^a * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s z-
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) ∂fiberMeasure n 0) = I a := by
    have hh := fixed_spin_gauge_integral n m (fun _ : S => 0) U (b s) (p s)
      (fun _ => rfl) (hUg s) s (fun z => (L s z)^a) (fun z => (L s₀ z)^a)
      (fun z => congrArg (fun x : ℝ => x^a) (hLg s z))
    simpa only [hp] using hh
  have hsum (a : ℕ) : hierarchyJointMoment n m U L a = (Fintype.card S : ℝ)*I a := by
    unfold hierarchyJointMoment
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [hsum,mul_div_mul_left _ _ hc]
  have hBL := hierarchy_fixed_spin_linear_variance n m hm hmu hmono (fun _ : S => 0) U hU₀ s₀
    (L s₀) (hL₀ s₀) hA (hL s₀)
  have hV (z : ParameterSpace n) :
      -((1/2 : ℝ)*coordinateSquare n z-U s₀ z+
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) =
      -(1/2 : ℝ)*coordinateSquare n z+U s₀ z-
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z := by ring
  simpa only [I,pow_zero,one_mul,pow_one,hV] using hBL

theorem coordinateSquare_eq_sum (n : ℕ) (z : ParameterSpace n) :
    coordinateSquare n z = ∑ i, (coordinateProjection n i z)^2 := by
  induction n with
  | zero => simp [coordinateSquare]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [coordinateProjection,Fin.lastCases_last,Fin.lastCases_castSucc,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      coordinateSquare]
    rw [ih z.1]

theorem coordinateProjection_sign (n : ℕ) (b : Fin n → Bool) (i : Fin n) (z : ParameterSpace n) :
    coordinateProjection n i (coordinateSign n b z) = scalarSign (b i) (coordinateProjection n i z) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateProjection,coordinateSign]
    · simpa only [coordinateProjection,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',coordinateSign] using
        ih (fun i => b i.castSucc) j z.1

theorem coordinateLinear_sq_le (n : ℕ) (a : Fin n → ℝ) (z : ParameterSpace n) :
    (coordinateLinear n a z)^2 ≤ (∑ i, (a i)^2)*coordinateSquare n z := by
  rw [coordinateLinear_apply,coordinateSquare_eq_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun i => coordinateProjection n i z)

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyJointLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem gaussian_convex_tilt_integrable (n : ℕ) (G : ParameterSpace n → ℝ)
    (hG : ContDiff ℝ 2 G) (hGc : ConvexOn ℝ univ G)
    (U : ParameterSpace n →L[ℝ] ℝ) :
    let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
    Integrable (fun z => Real.exp (-V z)) (fiberMeasure n 0) ∧
    Integrable (fun z => coordinateSquare n z*Real.exp (-V z)) (fiberMeasure n 0) := by
  let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
  have hq := contDiff_coordinateSquare n
  have hV : ContDiff ℝ 2 V := ((contDiff_const.mul hq).sub U.contDiff).add hG
  apply integrable_stronglyConvex_density n V hV (by norm_num : (0 : ℝ) < 1)
  intro z u
  have he : V = fun z => ((1/2 : ℝ)*coordinateSquare n z + (-1)*U z)+G z := by
    funext z; dsimp only [V]; ring
  rw [he, hessian_add ((contDiff_const.mul hq).add (contDiff_const.mul U.contDiff)) hG,
    hessian_add (contDiff_const.mul hq) (contDiff_const.mul U.contDiff),
    hessian_const_mul hq, hessian_const_mul U.contDiff, hessian_linear,
    hessian_coordinateSquare]
  nlinarith [hessian_nonneg_of_convex G hG hGc z u]

theorem hierarchyLogDensity_continuous {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) :
    Continuous (hierarchyLogDensity n m U s) := by
  have hreg := hierarchyPenalty_regular n m 1 zero_le_one hm hmu hmono
    (affineLogPartition (fun _ => 0) U)
    ⟨affineLogPartition_boundedDerivs _ _,affineLogPartition_convex _ _⟩
  exact (((continuous_coordinateSquare n).const_mul _).add (U s).continuous).sub hreg.1.1.continuous

theorem hierarchyLogDensity_integrable {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) :
    Integrable (fun z => Real.exp (hierarchyLogDensity n m U s z)) (fiberMeasure n 0) ∧
    Integrable (fun z => coordinateSquare n z*Real.exp (hierarchyLogDensity n m U s z))
      (fiberMeasure n 0) := by
  have hreg := hierarchyPenalty_regular n m 1 zero_le_one hm hmu hmono
    (affineLogPartition (fun _ => 0) U)
    ⟨affineLogPartition_boundedDerivs _ _,affineLogPartition_convex _ _⟩
  have he (z : ParameterSpace n) :
      -((1/2 : ℝ)*coordinateSquare n z-U s z+
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) =
        hierarchyLogDensity n m U s z := by unfold hierarchyLogDensity; ring
  simpa only [he] using gaussian_convex_tilt_integrable n _ hreg.1.1 hreg.2 (U s)

theorem hierarchyLogDensity_moment_integrable {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    (s : S) {p : ℕ} (hp : p ≤ 2) :
    Integrable (fun z => (L s z)^p*Real.exp (hierarchyLogDensity n m U s z))
      (fiberMeasure n 0) := by
  obtain ⟨hI₀,hIq⟩ := hierarchyLogDensity_integrable n m hm hmu hmono U s
  have hc := hierarchyLogDensity_continuous n m hm hmu hmono U s
  have hI₂ : Integrable (fun z => (L s z)^2*Real.exp (hierarchyLogDensity n m U s z))
      (fiberMeasure n 0) := by
    apply (hIq.const_mul A).mono' (((L s).continuous.pow 2).mul (Real.continuous_exp.comp hc)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(L s z)^2*Real.exp (hierarchyLogDensity n m U s z)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_right (hL s z) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _)
  interval_cases p
  · simpa only [pow_zero,one_mul] using hI₀
  · simp only [pow_one]
    apply (hI₀.add hI₂).mono' ((L s).continuous.mul (Real.continuous_exp.comp hc)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖L s z*Real.exp (hierarchyLogDensity n m U s z)‖ ≤
      Real.exp (hierarchyLogDensity n m U s z)+(L s z)^2*Real.exp (hierarchyLogDensity n m U s z)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hl : |L s z| ≤ 1+(L s z)^2 := by nlinarith [sq_nonneg (|L s z|-1),sq_abs (L s z)]
    nlinarith [mul_le_mul_of_nonneg_right hl (Real.exp_pos (hierarchyLogDensity n m U s z)).le]
  · exact hI₂

section JointLaw
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyJoint_integrable (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    {p : ℕ} (hp : p ≤ 2) :
    Integrable (fun sz : S × ParameterSpace n =>
      (L sz.1 sz.2)^p*Real.exp (hierarchyLogDensity n m U sz.1 sz.2))
      ((Measure.count : Measure S).prod (fiberMeasure n 0)) := by
  apply (integrable_prod_iff ?_).2
  · exact ⟨Filter.Eventually.of_forall fun s =>
      hierarchyLogDensity_moment_integrable n m hm hmu hmono U L hL s hp,
      Integrable.of_finite⟩
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro s
    exact (((L s).continuous.pow p).mul
      (Real.continuous_exp.comp (hierarchyLogDensity_continuous n m hm hmu hmono U s))).measurable

theorem hierarchyLaw_probability (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    IsProbabilityMeasure (hierarchyLaw n m U) := by
  let : NeZero ((Measure.count : Measure S).prod (fiberMeasure n 0)) := by
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    rw [← univ_prod_univ,Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)
  apply isProbabilityMeasure_tilted
  have hi := hierarchyJoint_integrable n m hm hmu hmono U (fun _ => 0)
    (A := 0) (by intro s z; simp) (p := 0) (by omega)
  simpa only [pow_zero,one_mul] using hi

theorem hierarchyLaw_moment (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    {p : ℕ} (hp : p ≤ 2) :
    (∫ sz, (L sz.1 sz.2)^p ∂hierarchyLaw n m U) =
      hierarchyJointMoment n m U L p / hierarchyJointMoment n m U L 0 := by
  have he (r : ℕ) (hr : r ≤ 2) :
      (∫ sz : S × ParameterSpace n, (L sz.1 sz.2)^r*
        Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
        ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) = hierarchyJointMoment n m U L r := by
    rw [integral_prod _ (hierarchyJoint_integrable n m hm hmu hmono U L hL hr),integral_count]
    rfl
  unfold hierarchyLaw
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have hf : (fun sz : S × ParameterSpace n =>
      Real.exp (hierarchyLogDensity n m U sz.1 sz.2) /
        (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
          ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) * (L sz.1 sz.2)^p) =
      (fun sz => ((L sz.1 sz.2)^p*Real.exp (hierarchyLogDensity n m U sz.1 sz.2)) /
        (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
          ∂(Measure.count : Measure S).prod (fiberMeasure n 0))) := by funext sz; ring
  rw [hf,integral_div,he p hp]
  have he₀ := he 0 (by omega)
  simpa only [pow_zero,one_mul] using congrArg (fun z => hierarchyJointMoment n m U L p / z) he₀

theorem hierarchyLaw_variance (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z) :
    ProbabilityTheory.variance (fun sz => L sz.1 sz.2) (hierarchyLaw n m U) =
      hierarchyJointMoment n m U L 2 / hierarchyJointMoment n m U L 0 -
        (hierarchyJointMoment n m U L 1 / hierarchyJointMoment n m U L 0)^2 := by
  let := hierarchyLaw_probability n m hm hmu hmono U
  have hmeas : Measurable (fun sz : S × ParameterSpace n => L sz.1 sz.2) :=
    measurable_from_prod_countable_right fun s => (L s).continuous.measurable
  have hi₀ := hierarchyJoint_integrable n m hm hmu hmono U L hL (p := 0) (by omega)
  simp only [pow_zero,one_mul] at hi₀
  have hi₂ := hierarchyJoint_integrable n m hm hmu hmono U L hL (p := 2) (by omega)
  have hL₂ : MemLp (fun sz : S × ParameterSpace n => L sz.1 sz.2) 2 (hierarchyLaw n m U) := by
    apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    apply (integrable_tilted_iff hi₀ _).2
    simpa only [smul_eq_mul,mul_comm] using hi₂
  rw [ProbabilityTheory.variance_eq_sub hL₂]
  change (∫ sz, (L sz.1 sz.2)^2 ∂hierarchyLaw n m U) -
    (∫ sz, L sz.1 sz.2 ∂hierarchyLaw n m U)^2 = _
  rw [hierarchyLaw_moment n m hm hmu hmono U L hL (by omega : 2 ≤ 2)]
  have h₁ := hierarchyLaw_moment n m hm hmu hmono U L hL (by omega : 1 ≤ 2)
  simpa only [pow_one] using congrArg (fun v =>
    hierarchyJointMoment n m U L 2/hierarchyJointMoment n m U L 0-v^2) h₁

end JointLaw
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyGaussianLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section LawIdentification
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyTerminalGibbs_sum (n : ℕ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (z : ParameterSpace n) : ∑ s, hierarchyTerminalGibbs n U s z = 1 := by
  have hp : 0 < ∑ s, Real.exp (U s z) :=
    Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [hierarchyTerminalGibbs,Real.exp_sub,affineLogPartition,zero_add,
    Real.exp_log hp,← Finset.sum_div,div_self hp.ne']

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyGaussian_density (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) (z : ParameterSpace n) :
    fiberGaussianDensity n z * (hierarchyPathWeight n m
      (affineLogPartition (fun _ => 0) U) z * hierarchyTerminalGibbs n U s z) =
      (Real.sqrt (2*Real.pi))⁻¹^n * Real.exp (hierarchyLogDensity n m U s z) := by
  rw [hierarchyTerminalGibbs,hierarchy_fixed_spin_density]
  unfold fiberGaussianDensity hierarchyLogDensity
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem hierarchyGaussian_normalizer (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    (Real.sqrt (2*Real.pi))⁻¹^n *
      (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
        ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) = 1 := by
  have hi := hierarchyJoint_integrable n m hm hmu hmono U (fun _ => 0)
    (A := 0) (by intro s z; simp) (p := 0) (by omega)
  simp only [pow_zero,one_mul] at hi
  rw [integral_prod _ hi,integral_count,← integral_finsetSum _
    (fun s _ => (hierarchyLogDensity_integrable n m hm hmu hmono U s).1),← integral_const_mul]
  have he (z : ParameterSpace n) :
      (Real.sqrt (2*Real.pi))⁻¹^n * ∑ s, Real.exp (hierarchyLogDensity n m U s z) =
      fiberGaussianDensity n z * hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z := by
    rw [Finset.mul_sum]
    simp_rw [← hierarchyGaussian_density n m U]
    rw [← Finset.mul_sum,← Finset.mul_sum,hierarchyTerminalGibbs_sum,mul_one]
  simp_rw [he]
  have hn := (hierarchyPathWeight_normalized n m (affineLogPartition (fun _ => 0) U) (affineLogPartition_boundedDerivs (fun _ => 0) U) 0).2
  rw [fiberGaussian_eq_withDensity,integral_withDensity_eq_integral_toReal_smul
    (fiberGaussianDensity_continuous n).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hn
  simpa only [ENNReal.toReal_ofReal (fiberGaussianDensity_pos _ _).le,smul_eq_mul] using hn

theorem hierarchyGaussianLaw_eq (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    hierarchyGaussianLaw n m U = hierarchyLaw n m U := by
  have hn := hierarchyGaussian_normalizer n m hm hmu hmono U
  have hp : 0 < (Real.sqrt (2*Real.pi))⁻¹^n := by positivity
  have hZ : (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
      ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) ≠ 0 := by
    intro h
    rw [h,mul_zero] at hn
    norm_num at hn
  unfold hierarchyGaussianLaw hierarchyLaw Measure.tilted
  rw [fiberGaussian_eq_withDensity,prod_withDensity_right
    (fiberGaussianDensity_continuous n).measurable.ennreal_ofReal]
  rw [← withDensity_mul]
  · apply congrArg (((Measure.count : Measure S).prod (fiberMeasure n 0)).withDensity)
    funext sz
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (fiberGaussianDensity_pos _ _).le,hierarchyGaussian_density]
    congr 1
    apply (eq_div_iff hZ).2
    calc
      _ = ((Real.sqrt (2*Real.pi))⁻¹^n *
          (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
            ∂(Measure.count : Measure S).prod (fiberMeasure n 0))) *
          Real.exp (hierarchyLogDensity n m U sz.1 sz.2) := by ring
      _ = _ := by rw [hn,one_mul]
  · exact ((fiberGaussianDensity_continuous n).measurable.comp measurable_snd).ennreal_ofReal
  · apply Measurable.ennreal_ofReal
    apply measurable_from_prod_countable_right
    intro s
    exact ((hierarchyPathWeight_continuous n m _ (affineLogPartition_boundedDerivs _ _)).mul
      (Real.continuous_exp.comp ((U s).continuous.sub
        (affineLogPartition_boundedDerivs (fun _ => 0) U).1.continuous))).measurable

end LawIdentification
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem massFromAtoms_nonneg (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    0 ≤ massFromAtoms n w i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hw j
  · exact le_rfl

theorem massFromAtoms_le_sum (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    massFromAtoms n w i ≤ ∑ j, w j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact hw j

theorem massFromAtoms_monotone (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Monotone (massFromAtoms n w) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left hj,ite_eq_left (hj.trans hik)]
  · rw [ite_eq_right hj]
    split_ifs
    · exact hw j
    · exact le_rfl
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockAtom_nonneg (D N k : ℕ) (t : Fin (blockDimension D N k+1)) :
    0 ≤ blockAtom D N k t := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity

theorem blockAtom_sum (D N k : ℕ) : ∑ t, blockAtom D N k t = 1 := by
  unfold blockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem blockMass_valid (D N k : ℕ) :
    (∀ i, 0 ≤ blockMass D N k i) ∧ (∀ i, blockMass D N k i ≤ 1) ∧ Monotone (blockMass D N k) := by
  refine ⟨massFromAtoms_nonneg _ _ (blockAtom_nonneg D N k),?_,
    massFromAtoms_monotone _ _ (blockAtom_nonneg D N k)⟩
  intro i
  exact (massFromAtoms_le_sum _ _ (blockAtom_nonneg D N k) i).trans_eq (blockAtom_sum D N k)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinMonomials
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK
open Analytic

theorem spinMonomial_gauge {N : ℕ} (v x : Config N) (I : Finset (Fin N)) :
    spinMonomial (gaugeConfig v x) I = spinMonomial v I*spinMonomial x I := by
  simp only [spinMonomial,gaugeConfig,spin_beq,Finset.prod_mul_distrib]

theorem scalarSign_monomial {N : ℕ} (v : Config N) (I : Finset (Fin N)) (z : ℝ) :
    scalarSign (monomialSign v I) z = spinMonomial v I*z := by
  have hh : spinMonomial v I = 1 ∨ spinMonomial v I = -1 :=
    (sq_eq_one_iff).mp (spinMonomial_sq v I)
  rcases hh with h | h <;> norm_num [monomialSign,h,scalarSign]

theorem spinExponent_axis {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (s : Config N) : spinExponent d a I s (parameterAxis d) = 0 :=
  coordinateLinear_axis _ _

theorem spinExponent_gauge {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (v s : Config N) (z : ParameterSpace d) :
    spinExponent d a I s (coordinateSign d (fun j => monomialSign v (I j)) z) =
      spinExponent d a I (gaugeConfig v s) z := by
  simp only [spinExponent,coordinateLinear_apply,coordinateProjection_sign,scalarSign_monomial,
    spinMonomial_gauge]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spinExponent_sq_le {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (s : Config N) (z : ParameterSpace d) :
    (spinExponent d a I s z)^2 ≤ (∑ j, (a j)^2)*coordinateSquare d z := by
  have h := coordinateLinear_sq_le d (fun j => a j*spinMonomial s (I j)) z
  simpa only [spinExponent,mul_pow,spinMonomial_sq,mul_one] using h

theorem hierarchy_spin_variance {N : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hmu : ∀ j, m j ≤ 1) (hmono : Monotone m)
    (a b : Fin d → ℝ) (I : Fin d → Finset (Fin N)) :
    let U := spinExponent d a I
    let L := spinExponent d b I
    hierarchyJointMoment d m U L 2 / hierarchyJointMoment d m U L 0 -
      (hierarchyJointMoment d m U L 1 / hierarchyJointMoment d m U L 0)^2 ≤ ∑ j, (b j)^2 := by
  apply hierarchy_gauge_linear_variance d m hm hmu hmono
    (spinExponent d a I) (spinExponent d b I) (spinExponent_axis d a I) (spinExponent_axis d b I)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (spinExponent_sq_le d b I)
    (fun _ : Fin N => true) (fun s j => monomialSign s (I j)) gaugeConfigEquiv
  · exact gaugeConfig_self
  · exact spinExponent_gauge d a I
  · intro s z
    simpa only [gaugeConfig_self] using spinExponent_gauge d b I s s z

end SK

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinFieldVariance
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK
open Analytic

theorem hierarchy_spin_variance_probability {N : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hmu : ∀ j, m j ≤ 1) (hmono : Monotone m)
    (a b : Fin d → ℝ) (I : Fin d → Finset (Fin N)) :
    ProbabilityTheory.variance (fun sz => spinExponent d b I sz.1 sz.2)
      (hierarchyLaw d m (spinExponent d a I)) ≤ ∑ j, (b j)^2 := by
  rw [hierarchyLaw_variance d m hm hmu hmono _ _ (spinExponent_sq_le d b I)]
  exact hierarchy_spin_variance d m hm hmu hmono a b I

end SK

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageMeanVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_eq_natAdd (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    fieldIndex D N k b i = Fin.natAdd D (finProdFinEquiv (b,i)) := by
  apply Fin.ext
  change D+b.val*N+i.val = D+(i.val+N*b.val)
  ring

@[simp] theorem blockInteraction_field {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (b : Fin (k+1)) (i : Fin N) : blockInteraction (k := k) I (fieldIndex D N k b i) = {i} := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockInteraction,Fin.addCases_right,Equiv.symm_apply_apply]

@[simp] theorem blockCoefficients_field {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) : blockCoefficients (N := N) a v (fieldIndex D N k b i) = v b := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockCoefficients,Fin.addCases_right,Equiv.symm_apply_apply]

theorem blockCoefficients_squares {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    (∑ t, (blockCoefficients (N := N) a v t)^2) =
      (∑ t, (a t)^2)+(N : ℝ)*∑ b, (v b)^2 := by
  rw [Fin.sum_univ_add]
  simp only [blockCoefficients,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => (v (finProdFinEquiv.symm t).1)^2)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Finset.mul_sum]

theorem blockExponent_expansion {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (s : Config N) (z : ParameterSpace (blockDimension D N k)) :
    blockExponent I a v s z =
      (∑ t : Fin D, a t*spinMonomial s (I t)*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) t) z)+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*spin (s i)*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  unfold blockExponent spinExponent
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*
    spinMonomial s {(finProdFinEquiv.symm t).2}*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,spinMonomial,Finset.prod_singleton,
    fieldIndex_eq_natAdd]

theorem blockFieldEnergy_exponent {D N k : ℕ} (I : Fin D → Finset (Fin N)) (v : Fin (k+1) → ℝ)
    (sz : Config N × ParameterSpace (blockDimension D N k)) :
    blockFieldEnergy v sz = blockExponent I (fun _ => 0) (fun b => v b/(N : ℝ)) sz.1 sz.2 := by
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,blockFieldEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem blockFieldEnergy_variance {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v w : Fin (k+1) → ℝ) :
    ProbabilityTheory.variance (blockFieldEnergy (D := D) (N := N) w)
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) (blockExponent I a v)) ≤
        (∑ b, (w b)^2)/(N : ℝ) := by
  have hm := blockMass_valid D N k
  rw [hierarchyGaussianLaw_eq _ _ hm.1 hm.2.1 hm.2.2]
  have he : blockFieldEnergy (D := D) (N := N) w = fun sz =>
      blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ)) sz.1 sz.2 :=
    funext (blockFieldEnergy_exponent I w)
  rw [he]
  simp only [blockExponent]
  have H := hierarchy_spin_variance_probability (blockDimension D N k) (blockMass D N k)
    hm.1 hm.2.1 hm.2.2 (blockCoefficients a v) (blockCoefficients (fun _ => 0) (fun b => w b/(N : ℝ)))
    (blockInteraction I)
  change _ ≤ _ at H
  rw [blockCoefficients_squares] at H
  simp only [zero_pow (by omega : 2 ≠ 0),Finset.sum_const_zero,zero_add,div_pow,← Finset.sum_div] at H
  by_cases hN : N=0
  · subst N
    simpa only [Nat.cast_zero,mul_zero,zero_mul,div_zero] using H
  · have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    exact H.trans_eq (by field_simp)
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem pairCoefficients_squared_sum (n : ℕ) (p q : Fin n) (hpq : p ≠ q) (a b : ℝ) :
    (∑ t, (pairCoefficients n p q a b t)^2) = a^2+b^2 := by
  have he (t : Fin n) : (pairCoefficients n p q a b t)^2 =
      (if t=p then a^2 else 0)+(if t=q then b^2 else 0) := by
    unfold pairCoefficients
    split_ifs with h₁ h₂ h₂
    · exact (hpq (h₁.symm.trans h₂)).elim
    · ring
    · ring
    · ring
  simp only [he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem sharedFieldEnergy_variance_oai {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b) (j : Fin k) :
    ProbabilityTheory.variance (sharedFieldEnergy D N k Δ j)
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k)
        (blockExponent I a (fun b => Real.sqrt (Δ b)))) ≤
      ((Δ j.castSucc)⁻¹+(Δ j.succ)⁻¹)/(N : ℝ) := by
  have H := blockFieldEnergy_variance I a (fun b => Real.sqrt (Δ b)) (sharedBlockWeights k Δ j)
  have hpq : j.castSucc ≠ j.succ := by
    intro hh
    have h := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at h
    omega
  simp only [sharedBlockWeights,pairCoefficients_squared_sum _ _ _ hpq,neg_sq,inv_pow,
    Real.sq_sqrt (hΔ _).le] at H
  exact H

end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.sharedFieldEnergy_variance_oai := @OAI.SK.Analytic.sharedFieldEnergy_variance_oai
