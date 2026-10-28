-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:39.552412+00:00
-- url     : https://prove2.me/submissions/184c4e5a-3db5-4750-84d4-dff1e42a4e05

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_lt_cap_sat
import Theorems.Thm_OAI_FixedClauseThreshold_subcritical_limit_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.DilutedSpinGlass.rootPathCountable _root_.OAI.DilutedSpinGlass.rootPathSingleton _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A bounded measurable score belongs to every finite Lp space. -/
theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ (fun point => by simpa only [Real.norm_eq_abs] using hB point)

/-- The exact two-independent-copy identity for variance. -/
theorem variance_two_copies {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, ∫ y, (f x-f y)^2 ∂μ ∂μ) = 2 * variance f μ := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs := hf.integrable_sq
  have hin (x : Ω) : (∫ y, (f x-f y)^2 ∂μ) =
      (f x)^2 - 2*f x*(∫ y, f y ∂μ) + ∫ y, (f y)^2 ∂μ := by
    have heq : (fun y => (f x-f y)^2) =
        (fun y => (f x)^2 - 2*f x*f y + (f y)^2) := by
      funext y; ring
    rw [heq]
    have hsub : Integrable (fun y => (f x)^2 - 2*f x*f y) μ :=
      (integrable_const _).sub (hi.const_mul (2*f x))
    rw [integral_add hsub hs,
      integral_sub (integrable_const ((f x)^2)) (hi.const_mul (2*f x)),
      integral_const_mul]
    simp
  simp_rw [hin]
  have hmul : Integrable (fun x => 2*f x*(∫ y, f y ∂μ)) μ :=
    (hi.const_mul 2).mul_const _
  have hsub : Integrable (fun x => (f x)^2 - 2*f x*(∫ y, f y ∂μ)) μ := hs.sub hmul
  rw [integral_add hsub (integrable_const (∫ y, (f y)^2 ∂μ))]
  rw [integral_sub hs hmul, variance_eq_sub hf]
  simp only [Pi.pow_apply]
  rw [show (fun x => 2*f x*(∫ y, f y ∂μ)) =
    (fun x => f x*(2*(∫ y, f y ∂μ))) by funext x; ring]
  rw [integral_mul_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Pairwise oscillation controls root variance without choosing a center. -/
theorem variance_le_oscillation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ} (hf : MemLp f 2 μ)
    (hC : ∀ x y, |f x-f y| ≤ C) : variance f μ ≤ C^2/2 := by
  have hp : ∀ x y, (f x-f y)^2 ≤ C^2 := by
    intro x y
    have h := hC x y
    nlinarith [sq_nonneg (C - |f x-f y|), sq_abs (f x-f y), abs_nonneg (f x-f y)]
  have hb : ∀ x, (∫ y, (f x-f y)^2 ∂μ) ≤ C^2 := by
    intro x
    have hsub : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
    simpa using integral_mono hsub.integrable_sq (integrable_const (C^2)) (hp x)
  have hint : Integrable (fun x => ∫ y, (f x-f y)^2 ∂μ) μ := by
    have hprod : MemLp (fun z : Ω × Ω => f z.1 - f z.2) 2 (μ.prod μ) :=
      (hf.comp_fst μ).sub (hf.comp_snd μ)
    exact hprod.integrable_sq.integral_prod_left
  have h := integral_mono hint (integrable_const (C^2)) hb
  rw [variance_two_copies hf] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

/-- Total variance for a bounded measurable function of two independent root blocks. -/
theorem variance_prod_decomposition {f : Ω × Λ → ℝ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x,y) ∂ν) μ := by
  have hLp := bounded_memLp (μ := μ.prod ν) hf hB 2
  have hLp' (x : Ω) : MemLp (fun y => f (x,y)) 2 ν :=
    bounded_memLp (hf.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y)) 2
  have hm : Measurable (fun x => ∫ y, f (x,y) ∂ν) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmLp : MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ :=
    bounded_memLp hm (fun x => abs_integral_le_bound (fun y => hB (x,y))) 2
  have hint : Integrable f (μ.prod ν) := hLp.integrable (by norm_num)
  rw [variance_eq_sub hLp, variance_eq_sub hmLp]
  simp_rw [variance_eq_sub (hLp' _)]
  simp only [Pi.pow_apply]
  rw [integral_sub hLp.integrable_sq.integral_prod_left hmLp.integrable_sq,
    integral_prod _ hint, integral_prod _ hLp.integrable_sq]
  ring

/-- An independent block average preserves each bounded-difference constant. -/
theorem integral_oscillation {f : Ω × Λ → ℝ} {B C : ℝ}
    (hf : Measurable f) (hB : ∀ z, |f z| ≤ B)
    (hC : ∀ x x' y, |f (x,y)-f (x',y)| ≤ C) :
    ∀ x x', |(∫ y, f (x,y) ∂ν) - (∫ y, f (x',y) ∂ν)| ≤ C := by
  intro x x'
  have hi (z : Ω) : Integrable (fun y => f (z,y)) ν :=
    (bounded_memLp (hf.comp (measurable_const.prodMk measurable_id))
      (fun y => hB (z,y)) 1).integrable le_rfl
  rw [← integral_sub (hi x) (hi x')]
  exact abs_integral_le_bound (hC x x')

end DilutedSpinGlass

namespace DilutedSpinGlass

universe u

/-- Bounded coordinate replacements give a variance bound additive in the
number of independent root coordinates, not quadratic in that number. -/
theorem root_variance_bound {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [hμ : ∀ i, IsProbabilityMeasure (μ i)]
    {F : RootPath Ω n → ℝ} {B : ℝ} (hF : Measurable F) (hB : ∀ x, |F x| ≤ B)
    (C : Fin n → ℝ)
    (hC : ∀ (i : Fin n) x y, |F x-F (replaceRoot n x i y)| ≤ C i) :
    variance F (rootLaw n μ) ≤ ∑ i, (C i)^2/2 := by
  induction n with
  | zero =>
    rw [variance_eq_integral hF.aemeasurable]
    simp [rootLaw]
  | succ n ih =>
    let ν := rootLaw n (fun i => μ i.succ)
    have : ∀ i : Fin n, IsProbabilityMeasure (μ i.succ) := fun i => hμ i.succ
    have ht (x : Ω) : variance (fun y => F (x,y)) ν ≤ ∑ i : Fin n, (C i.succ)^2/2 := by
      apply ih (fun i => μ i.succ)
        (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y))
        (fun i => C i.succ)
      intro i y z
      simpa [replaceRoot, Function.comp_def] using hC i.succ (x,y) z
    have hm : Measurable (fun x => ∫ y, F (x,y) ∂ν) :=
      hF.stronglyMeasurable.integral_prod_right'.measurable
    have hmLp : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 (μ 0) :=
      bounded_memLp hm (fun x => abs_integral_le_bound (fun y => hB (x,y))) 2
    have hosc : ∀ x x', |(∫ y, F (x,y) ∂ν)-(∫ y, F (x',y) ∂ν)| ≤ C 0 := by
      apply integral_oscillation hF hB
      intro x x' y
      simpa [replaceRoot] using hC 0 (x,y) x'
    have hroot := variance_le_oscillation hmLp hosc
    have hLp := bounded_memLp (μ := (μ 0).prod ν) hF hB 2
    have hs (x : Ω) : MemLp (fun y => F (x,y)) 2 ν :=
      bounded_memLp (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y)) 2
    have hint : Integrable (fun x => variance (fun y => F (x,y)) ν) (μ 0) := by
      simp_rw [variance_eq_sub (hs _)]
      exact hLp.integrable_sq.integral_prod_left.sub hmLp.integrable_sq
    have hintBound := integral_mono hint (integrable_const (∑ i : Fin n, (C i.succ)^2/2)) ht
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hintBound
    change variance F ((μ 0).prod ν) ≤ _
    rw [variance_prod_decomposition hF hB, Fin.sum_univ_succ]
    linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.DilutedSpinGlass.rootPathCountable _root_.OAI.DilutedSpinGlass.rootPathSingleton _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

theorem poisson_integrable_linear (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*n) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnext : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have hs := (hasSum_integral_poissonMeasure hnext).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : Summable (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)^2) := by
    simp_rw [pow_two, ← mul_assoc, poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs.summable
  have ht' := Summable.comp_nat_add (f := fun n => poissonWeight r n * (n : ℝ)^2) (k := 1) ht
  simpa only [Real.norm_eq_abs, abs_sq, poissonWeight] using ht'

@[simp] theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  have hi : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have h := poisson_add_one r (fun n => (n : ℝ)) hi
  simp only [← pow_two, Nat.cast_add, Nat.cast_one] at h
  rw [integral_add (poisson_integrable_count r) (integrable_const 1), poisson_mean,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

theorem poisson_variance (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r)^2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ)-r)^2) =
      (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*(n : ℝ) + (r : ℝ)^2) := by
    funext n
    ring
  rw [heq]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*n) (poissonMeasure r) :=
    (poisson_integrable_count_sq r).sub ((poisson_integrable_count r).const_mul (2*(r : ℝ)))
  rw [integral_add hi (integrable_const ((r : ℝ)^2)),
    integral_sub (poisson_integrable_count_sq r) ((poisson_integrable_count r).const_mul (2*r)),
    integral_const_mul, poisson_second_moment, poisson_mean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

/-- Lipschitz sequences have a square-integrable Poisson law. -/
theorem poisson_memLp_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    MemLp f 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
  apply poisson_integrable_quadratic r (A := 2*(f 0)^2) (B := 2*C^2)
  intro n
  have h := hL n 0
  simp only [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  have hh : |f n| ≤ C*(n : ℝ)+|f 0| := by
    calc |f n| = |(f n-f 0)+f 0| := by rw [sub_add_cancel]
         _ ≤ |f n-f 0| + |f 0| := abs_add_le _ _
         _ ≤ C*(n : ℝ)+|f 0| := by linarith
  have hb : 0 ≤ C*(n : ℝ)+|f 0| := by positivity
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f n), sq_abs (f 0),
    sq_nonneg (C*(n : ℝ)-|f 0|), mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hb (abs_nonneg (f n)))]

/-- Poisson random-coordinate count variance: a count-Lipschitz logarithm
has fluctuations of order sqrt(rate), not order rate. -/
theorem poisson_variance_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    variance f (poissonMeasure r) ≤ C^2 * (r : ℝ) := by
  have hf := poisson_memLp_lipschitz r hC hL
  have hn : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) :=
    (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
      (poisson_integrable_count_sq r)
  have hp : ∀ n m : ℕ, (f n-f m)^2 ≤ C^2*((n : ℝ)-(m : ℝ))^2 := by
    intro n m
    have h := hL n m
    have hnon : 0 ≤ C*|(n : ℝ)-(m : ℝ)| := mul_nonneg hC (abs_nonneg _)
    nlinarith [sq_abs (f n-f m), sq_abs ((n : ℝ)-(m : ℝ)),
      mul_nonneg (sub_nonneg.mpr h) (add_nonneg hnon (abs_nonneg (f n-f m)))]
  let μ := poissonMeasure r
  have hint (n : ℕ) := integral_mono
    ((memLp_const (f n)).sub hf).integrable_sq
    (((memLp_const (n : ℝ)).sub hn).integrable_sq.const_mul (C^2)) (hp n)
  have hfprod : MemLp (fun z : ℕ × ℕ => f z.1-f z.2) 2 (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hnprod : MemLp (fun z : ℕ × ℕ => (z.1 : ℝ)-(z.2 : ℝ)) 2 (μ.prod μ) :=
    (hn.comp_fst μ).sub (hn.comp_snd μ)
  have h := integral_mono hfprod.integrable_sq.integral_prod_left
    (hnprod.integrable_sq.const_mul (C^2)).integral_prod_left hint
  simp_rw [integral_const_mul] at h
  rw [variance_two_copies hf, variance_two_copies hn,
    variance_eq_integral (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).aemeasurable, poisson_mean, poisson_variance] at h
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- Adding one root coordinate gives the full Lipschitz bound in the count. -/
theorem nat_lipschitz_of_step {f : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ n, |f (n+1)-f n| ≤ C) : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)| := by
  have hle : ∀ n m, n ≤ m → |f m-f n| ≤ C*((m : ℝ)-(n : ℝ)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have ha : |f (m+1)-f n| ≤ |f (m+1)-f m|+|f m-f n| := by
        calc
          |f (m+1)-f n| = |(f (m+1)-f m)+(f m-f n)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      push_cast
      nlinarith [h m]
  intro n m
  rcases le_total n m with hnm | hmn
  · rw [abs_sub_comm (f n), abs_sub_comm (n : ℝ), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm : (n : ℝ) ≤ m))]
    exact hle n m hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn : (m : ℝ) ≤ n))]
    exact hle m n hmn

/-- Centering at an arbitrary constant separates conditional variance and
squared conditional-mean displacement. -/
theorem integral_sq_sub_center {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    (∫ x, (f x-a)^2 ∂μ) = variance f μ + ((∫ x, f x ∂μ)-a)^2 := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (fun x => (f x-a)^2) = (fun x => f x^2-2*a*f x+a^2) := by funext x; ring
  rw [heq]
  have hs : Integrable (fun x => f x^2-2*a*f x) μ := hf.integrable_sq.sub (hi.const_mul (2*a))
  rw [integral_add hs (integrable_const _), integral_sub hf.integrable_sq (hi.const_mul (2*a)),
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul, variance_eq_sub hf]
  simp only [Pi.pow_apply]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Actual random-count root means inherit the addition/deletion constant. -/
theorem rootAverage_step {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hadd : ∀ n x y, |F (n+1) (x,y) - F n y| ≤ D) (n : ℕ) :
    |rootAverage μ F (n+1)-rootAverage μ F n| ≤ D := by
  let ν := rootLaw n (fun _ : Fin n => μ)
  have hp : Integrable (F (n+1)) (μ.prod ν) :=
    (bounded_memLp (hF (n+1)) (hB (n+1)) 1).integrable le_rfl
  have hi : Integrable (F n) ν := (bounded_memLp (hF n) (hB n) 1).integrable le_rfl
  have hs (x : Ω) : Integrable (fun y => F (n+1) (x,y)) ν :=
    (bounded_memLp ((hF (n+1)).comp (measurable_const.prodMk measurable_id))
      (fun y => hB (n+1) (x,y)) 1).integrable le_rfl
  change |(∫ z, F (n+1) z ∂μ.prod ν) - ∫ y, F n y ∂ν| ≤ D
  rw [integral_prod _ hp]
  have hc : (∫ _ : Ω, (∫ y, F n y ∂ν) ∂μ) = ∫ y, F n y ∂ν := by simp
  rw [← hc, ← integral_sub hp.integral_prod_left (integrable_const _)]
  apply abs_integral_le_bound
  intro x
  rw [← integral_sub (hs x) hi]
  exact abs_integral_le_bound (hadd n x)


end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem rootArray_replace {I : Type*} (n : ℕ) (x : RootPath I n) (j : Fin n) (i : I) :
    rootArray n (replaceRoot n x j i) = Function.update (rootArray n x) j i := by
  classical
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · funext q
      refine Fin.cases ?_ (fun q => ?_) q <;> simp [rootArray, replaceRoot]
    · funext q
      refine Fin.cases ?_ (fun q => ?_) q
      · simp [rootArray, replaceRoot, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      · simp only [rootArray, replaceRoot, Fin.cases_succ, Fin.cons_succ, ih]
        by_cases h : q = j
        · subst q; simp
        · simp [h, show q.succ ≠ j.succ by simpa using h]

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual random-count squared displacement around any center. Both
conditional root fluctuations and random-count fluctuations are retained. -/
theorem poisson_root_second_moment (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hD : 0 ≤ D)
    (hrep : ∀ n (i : Fin n) x y, |F n x-F n (replaceRoot n x i y)| ≤ C)
    (hadd : ∀ n x y, |F (n+1) (x,y)-F n y| ≤ D) (c : ℝ) :
    (∫ n : ℕ, ∫ x, (F n x-c)^2 ∂rootLaw n (fun _ => μ) ∂poissonMeasure r) ≤
      (C^2/2+D^2)*(r : ℝ) + (poissonRootAverage μ r F-c)^2 := by
  have hvar (n : ℕ) : variance (F n) (rootLaw n (fun _ => μ)) ≤ C^2/2*(n : ℝ) := by
    have h := root_variance_bound n (fun _ => μ) (hF n) (hB n) (fun _ => C) (hrep n)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hvint : Integrable (fun n => variance (F n) (rootLaw n (fun _ => μ))) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := C^2/2)
    intro n
    rw [abs_of_nonneg (variance_nonneg _ _), zero_add]
    exact hvar n
  have hmeanLp := poisson_memLp_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  have hcount := poisson_variance_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  simp_rw [integral_sq_sub_center (bounded_memLp (hF _) (hB _) 2)]
  change (∫ n, variance (F n) (rootLaw n (fun _ => μ)) + (rootAverage μ F n-c)^2
    ∂poissonMeasure r) ≤ _
  have hsq : Integrable (fun n => (rootAverage μ F n-c)^2) (poissonMeasure r) :=
    (hmeanLp.sub (memLp_const c)).integrable_sq
  rw [integral_add hvint hsq,
    integral_sq_sub_center hmeanLp c]
  have hi := integral_mono hvint ((poisson_integrable_count r).const_mul (C^2/2)) hvar
  rw [integral_const_mul,poisson_mean] at hi
  change _ ≤ (C^2/2+D^2)*(r : ℝ) + ((∫ n, rootAverage μ F n ∂poissonMeasure r)-c)^2
  nlinarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_GeneralRootArrayLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

variable {X : Type} [MeasurableSpace X]

lemma rootArrayEquiv_apply (n : ℕ) (x : RootPath X n) : rootArrayEquiv (X := X) n x = rootArray n x := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change Fin.insertNth 0 x.1 (rootArrayEquiv (X := X) n x.2) =
      Fin.cons (α := fun _ : Fin (n+1) => X) x.1 (rootArray n x.2)
    rw [Fin.insertNth_zero', ih]


/-- Exact law identification for arbitrary measurable disorder alphabets,
including the continuous physical interaction tables and external fields. -/
theorem measurePreserving_rootArray (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (rootArrayEquiv (X := X) n) (rootLaw n (fun _ => μ))
      (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero =>
    refine ⟨(rootArrayEquiv 0).measurable, ?_⟩
    rw [rootLaw,Measure.map_dirac' (rootArrayEquiv 0).measurable,Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.comp
      ((MeasurePreserving.id μ).prod ih)

theorem integral_rootArray_eq_pi (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) :
    (∫ x, f (rootArray n x) ∂rootLaw n (fun _ => μ)) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  simpa only [rootArrayEquiv_apply] using (measurePreserving_rootArray μ n).integral_comp' f

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePoissonSplit
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Clauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

theorem properSATProbability_nonneg (n k m : ℕ) :
    0 ≤ properSATProbability n k m := by
  unfold properSATProbability
  positivity

theorem forcedVariables_eq_frozen {n : ℕ} {S : Finset (Assignment n)}
    {σ₀ : Assignment n} (hσ₀ : σ₀ ∈ S) :
    forcedVariables S = frozenCoordinates S σ₀ := by
  ext i
  simp only [forcedVariables, frozenCoordinates, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, b, hb⟩ σ hσ
    exact (hb σ hσ).trans (hb σ₀ hσ₀).symm
  · intro h
    exact ⟨⟨σ₀, hσ₀⟩, σ₀ i, h⟩

theorem card_killingClauses {n k : ℕ} (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    Fintype.card {C : ProperClause n k // KillsSolutions S C} =
      (forcedVariables S).card.choose k := by
  obtain ⟨σ₀, hσ₀⟩ := hS
  rw [Fintype.card_congr (killingClauseEquiv S σ₀ hσ₀),
    Fintype.card_coe, Finset.card_powersetCard, forcedVariables_eq_frozen hσ₀]

theorem uniformProbability_le_one {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p ≤ 1 := by
  classical
  unfold uniformProbability
  by_cases h : Fintype.card α = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Fintype.card_subtype_le p

theorem killingProbability_of_nonempty {n k : ℕ} (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    killingProbability k S = ((forcedVariables S).card.choose k : ℝ) /
      ((n.choose k : ℝ) * 2 ^ k) := by
  classical
  unfold killingProbability uniformProbability
  simp only [hS, true_and, card_killingClauses S hS, card_properClause,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Replacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_congr {α : Type*} [Fintype α] {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) : uniformProbability p = uniformProbability q := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquivRight h)]

theorem uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformProbability (fun a => ¬ p a) = 1 - uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le p), sub_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero)]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_FiniteMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem uniformMean_zero {α : Type*} [Fintype α] :
    uniformMean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [uniformMean]

theorem uniformMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) : uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_ClauseProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem restrictSolutions_zero {n k : ℕ} (S : Finset (Assignment n))
    (F : Formula n k 0) : restrictSolutions S F = S := by
  ext σ
  simp only [mem_restrictSolutions, Fin.forall_fin_zero, and_true]

theorem restrictSolutions_cons {n k m : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) :
    restrictSolutions S (Fin.cons C F) = restrictSolutions (addClause S C) F := by
  ext σ
  simp only [mem_restrictSolutions, mem_addClause, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]
  tauto

theorem uniformMean_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun F : Fin m → α =>
      f (Fin.cons a F))) := by
  calc
    _ = uniformMean (fun p : α × (Fin m → α) => f (Fin.cons p.1 p.2)) :=
      (uniformMean_equiv (Fin.consEquiv (fun _ => α)) f).symm
    _ = _ := uniformMean_prod _

theorem alive_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ alive S := by
  unfold alive
  split <;> norm_num

theorem alive_le_one {n : ℕ} (S : Finset (Assignment n)) : alive S ≤ 1 := by
  unfold alive
  split <;> norm_num

theorem alive_mono {n : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T) :
    alive S ≤ alive T := by
  unfold alive
  by_cases hS : S.Nonempty
  · have hT := hS.mono hST
    simp [hS, hT]
  · simp only [ite_eq_right hS]
    split <;> norm_num

theorem survival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k (m + 1) S = uniformMean (fun C : ProperClause n k =>
      survival k m (addClause S C)) := by
  rw [survival, Function.iterate_succ_apply']
  rfl

theorem survival_eq_mean {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformMean (fun F : Formula n k m => alive (restrictSolutions S F)) := by
  induction m generalizing S with
  | zero =>
    simp only [survival_zero, restrictSolutions_zero]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [survival_succ, uniformMean_fin_succ]
    apply uniformMean_congr
    intro C
    rw [ih]
    apply uniformMean_congr
    intro F
    rw [restrictSolutions_cons]

theorem properSATProbability_eq_survival (n k m : ℕ) :
    properSATProbability n k m = survival k m (Finset.univ : Finset (Assignment n)) := by
  rw [survival_eq_mean]
  change uniformProbability (fun F : Formula n k m => Satisfiable F) = _
  rw [uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  simp only [Finset.nonempty_iff_ne_empty]
  apply propext
  rw [← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty, Satisfiable, Satisfies]

theorem survival_mono_solutions {n k m : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T) :
    survival k m S ≤ survival k m T := by
  rw [survival_eq_mean, survival_eq_mean]
  apply uniformMean_mono
  intro F
  apply alive_mono
  intro σ hσ
  rw [mem_restrictSolutions] at hσ ⊢
  exact ⟨hST hσ.1, hσ.2⟩

theorem survival_antitone {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    Antitone (fun m => survival k m S) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  apply antitone_nat_of_succ_le
  intro m
  rw [survival_succ, ← uniformMean_const (α := ProperClause n k) (survival k m S)]
  apply uniformMean_mono
  intro C
  exact survival_mono_solutions (Finset.filter_subset _ _)

theorem properSATProbability_antitone {n k : ℕ} (hkn : k ≤ n) :
    Antitone (properSATProbability n k) := by
  intro i j hij
  rw [properSATProbability_eq_survival, properSATProbability_eq_survival]
  exact survival_antitone hkn _ hij

theorem kills_iff_addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    KillsSolutions S C ↔ ¬ (addClause S C).Nonempty := by
  change (∀ σ ∈ S, ¬ SatisfiesClause σ C) ↔ ¬ ∃ σ, σ ∈ addClause S C
  simp only [mem_addClause, not_exists, not_and]

theorem singleUNSAT_eq {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    uniformProbability (fun C : ProperClause n k => KillsSolutions S C) =
      1 - survival k 1 S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [uniformProbability_eq_mean, survival_succ]
  simp only [survival_zero]
  calc
    _ = uniformMean (fun C : ProperClause n k => 1 - alive (addClause S C)) := by
      apply uniformMean_congr
      intro C
      rw [kills_iff_addClause]
      unfold alive
      by_cases h : (addClause S C).Nonempty <;> simp [h]
    _ = _ := by rw [uniformMean_sub, uniformMean_const]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Forcing
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem deletedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    deletedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      deletedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [deletedMean, h, uniformMean_const]

@[simp] theorem erasedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    erasedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      erasedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [erasedMean, h, uniformMean_const]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Variance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem survival_empty {n k m : ℕ} : survival k m (∅ : Finset (Assignment n)) = 0 := by
  rw [survival_eq_mean]
  have h (F : Formula n k m) : restrictSolutions ∅ F = ∅ := by simp [restrictSolutions]
  simp only [h, alive_empty, uniformMean_zero]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_forall_fintype {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ b, p (f b)) = uniformProbability p ^ Fintype.card β := by
  unfold uniformProbability
  have hc : Fintype.card {f : β → α // ∀ b, p (f b)} =
      Fintype.card (β → {a : α // p a}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ : β => p))
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow, div_pow]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Interpolation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem finiteClauseAverage_mono {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, finiteClauseAverage sat f S ≤ finiteClauseAverage sat g S := by
  intro S
  exact uniformMean_mono (fun c => hfg _)

theorem finiteClauseAverage_const_mul {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    finiteClauseAverage sat (fun S => c * f S) = (fun S => c * finiteClauseAverage sat f S) := by
  funext S
  exact uniformMean_const_mul _ _

theorem finiteClauseAverage_commute {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop) :
    Function.Commute (finiteClauseAverage satC) (finiteClauseAverage satD) := by
  intro f
  funext S
  unfold finiteClauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro d
  apply uniformMean_congr
  intro c
  congr 1
  ext σ
  simp only [Finset.mem_filter]
  tauto

theorem iterate_compare_of_commute {X : Type*}
    (A B : (X → ℝ) → (X → ℝ)) (hA : Monotone A) (hB : Monotone B)
    (hcomm : Function.Commute A B) {f : X → ℝ} (hf : B f ≤ A f) (m : ℕ) :
    B^[m] f ≤ A^[m] f := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      B (B^[m] f) ≤ B (A^[m] f) := hB ih
      _ = A^[m] (B f) := (hcomm.symm.iterate_right m f)
      _ ≤ A^[m] (A f) := hA.iterate m hf
      _ = A (A^[m] f) := (Function.iterate_succ_apply A m f).symm.trans
        (Function.iterate_succ_apply' A m f)

theorem opposing_literal_iff {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n)
    (σ₀ : Assignment n) (hσ₀ : σ₀ ∈ S) (l : Fin v × Bool) :
    (∀ σ ∈ S, σ (e l.1) ≠ l.2) ↔
      l.1 ∈ embeddedForced S e ∧ l.2 = !(σ₀ (e l.1)) := by
  rw [mem_embeddedForced, forcedVariables_eq_frozen hσ₀]
  simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have h0 := h σ₀ hσ₀
    constructor
    · intro σ hσ
      have hs := h σ hσ
      cases h1 : σ (e l.1) <;> cases h2 : σ₀ (e l.1) <;> cases h3 : l.2 <;> simp_all
    · cases h2 : σ₀ (e l.1) <;> cases h3 : l.2 <;> simp_all
  · rintro ⟨h, hb⟩ σ hσ
    rw [h σ hσ, hb]
    cases σ₀ (e l.1) <;> decide

theorem opposing_literal_probability {n v : ℕ} (S : Finset (Assignment n))
    (e : Fin v → Fin n) (hS : S.Nonempty) :
    uniformProbability (fun l : Fin v × Bool => ∀ σ ∈ S, σ (e l.1) ≠ l.2) =
      ((embeddedForced S e).card : ℝ) / (2 * v) := by
  obtain ⟨σ₀, hσ₀⟩ := hS
  let eqv : {l : Fin v × Bool // ∀ σ ∈ S, σ (e l.1) ≠ l.2} ≃ ↥(embeddedForced S e) := {
    toFun := fun l => ⟨l.val.1, ((opposing_literal_iff S e σ₀ hσ₀ l.val).mp l.property).1⟩
    invFun := fun i => ⟨(i.val, !(σ₀ (e i.val))),
      (opposing_literal_iff S e σ₀ hσ₀ _).mpr ⟨i.property, rfl⟩⟩
    left_inv := fun l => by
      apply Subtype.ext
      change (l.val.1, !(σ₀ (e l.val.1))) = l.val
      apply Prod.ext
      · rfl
      · exact ((opposing_literal_iff S e σ₀ hσ₀ l.val).mp l.property).2.symm
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr eqv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (v : ℝ) 2]

theorem embedded_kill_probability {n v k : ℕ} (S : Finset (Assignment n))
    (e : Fin v → Fin n) (hS : S.Nonempty) :
    uniformProbability (fun C : AuxiliaryClause v k =>
      ¬ (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty) =
      (((embeddedForced S e).card : ℝ) / (2 * v))^k := by
  calc
    _ = uniformProbability (fun C : AuxiliaryClause v k =>
        ∀ j, ∀ σ ∈ S, σ (e (C j).1) ≠ (C j).2) := by
      apply uniformProbability_congr
      intro C
      constructor
      · intro h j σ hσ heq
        apply h
        exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, ⟨j, heq⟩⟩⟩
      · intro h ⟨σ, hσ⟩
        obtain ⟨hσ, j, hj⟩ := Finset.mem_filter.mp hσ
        exact h j σ hσ hj
    _ = _ := by
      change (uniformProbability (fun C : Fin k → Fin v × Bool =>
        ∀ j, (fun l : Fin v × Bool => ∀ σ ∈ S, σ (e l.1) ≠ l.2) (C j))) = _
      have hf := uniformProbability_forall_fintype (α := Fin v × Bool) (β := Fin k)
        (fun l => ∀ σ ∈ S, σ (e l.1) ≠ l.2)
      simpa only [Fintype.card_fin, opposing_literal_probability S e hS] using hf

theorem embeddedAverage_alive {n v k : ℕ} (hv : 0 < v) (e : Fin v → Fin n)
    (S : Finset (Assignment n)) :
    embeddedAverage e k alive S = alive S *
      (1 - (((embeddedForced S e).card : ℝ) / (2 * v))^k) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  by_cases hS : S.Nonempty
  · have ha : alive S = 1 := by simp [alive, hS]
    rw [ha, one_mul]
    have h := uniformProbability_not (fun C : AuxiliaryClause v k =>
      (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty)
    rw [embedded_kill_probability S e hS] at h
    have he : embeddedAverage e k alive S = uniformProbability (fun C : AuxiliaryClause v k =>
        (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty) := by
      rw [uniformProbability_eq_mean]
      unfold embeddedAverage finiteClauseAverage
      apply uniformMean_congr
      intro C
      by_cases hC : (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty
      · simp only [alive, ite_eq_left hC]
      · simp only [alive, ite_eq_right hC]
    rw [he]
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [embeddedAverage, finiteClauseAverage, alive_empty, uniformMean_zero]

theorem auxiliaryAverage_alive {n k : ℕ} (hn : 0 < n) (S : Finset (Assignment n)) :
    auxiliaryAverage k alive S = alive S * (1 - (forcedFraction S / 2)^k) := by
  rw [auxiliaryAverage, embeddedAverage_alive hn, embeddedForced_id]
  congr 2
  unfold forcedFraction
  ring

theorem auxiliarySurvival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    auxiliarySurvival k (m + 1) S = uniformMean (fun C : AuxiliaryClause n k =>
      auxiliarySurvival k m (S.filter (fun σ => auxiliarySatisfies σ C))) := by
  unfold auxiliarySurvival
  rw [Function.iterate_succ_apply']
  rfl

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Transfer
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem card_injective_lists (n k : ℕ) :
    Fintype.card {f : Fin k → Fin n // Function.Injective f} = n.descFactorial k := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

theorem properFraction_probability (n k : ℕ) :
    properFraction n k = uniformProbability (fun f : Fin k → Fin n => Function.Injective f) := by
  unfold properFraction uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  simp only [Nat.card_eq_fintype_card, card_injective_lists, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]

theorem properFraction_nonneg (n k : ℕ) : 0 ≤ properFraction n k := by
  unfold properFraction
  positivity

theorem properFraction_le_one (n k : ℕ) : properFraction n k ≤ 1 := by
  rw [properFraction_probability]
  exact uniformProbability_le_one _

theorem repetition_count_mono {b n k : ℕ} (hbn : b ≤ n) :
    (b : ℝ)^k - b.descFactorial k ≤ (n : ℝ)^k - n.descFactorial k := by
  let e : {f : Fin k → Fin b // ¬ Function.Injective f} ↪
      {f : Fin k → Fin n // ¬ Function.Injective f} := {
    toFun := fun f => ⟨fun i => Fin.castLE hbn (f.val i), by
      intro hinj
      apply f.property
      intro i j hij
      apply hinj
      exact congrArg (Fin.castLE hbn) hij⟩
    inj' := by
      intro f g h
      apply Subtype.ext
      funext i
      apply Fin.castLE_injective hbn
      exact congrFun (congrArg Subtype.val h) i }
  have h := Fintype.card_le_of_embedding e
  have hf (v : ℕ) : Fintype.card {f : Fin k → Fin v // ¬ Function.Injective f} =
      v^k - v.descFactorial k := by
    simp only [Fintype.card_subtype_compl, card_injective_lists, Fintype.card_fun, Fintype.card_fin]
  have hd (v : ℕ) : v.descFactorial k ≤ v^k := by
    have h := Fintype.card_subtype_le (fun f : Fin k → Fin v => Function.Injective f)
    simpa only [card_injective_lists, Fintype.card_fun, Fintype.card_fin] using h
  rw [hf, hf] at h
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  simpa only [Nat.cast_sub (hd _), Nat.cast_pow] using h'

theorem properFraction_mul_kill {b n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    properFraction n k * killFraction b n k =
      (b.descFactorial k : ℝ) / ((2 : ℝ)^k * (n : ℝ)^k) := by
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold properFraction killFraction
  rw [Nat.descFactorial_eq_factorial_mul_choose n k, Nat.descFactorial_eq_factorial_mul_choose b k]
  push_cast
  field_simp

theorem auxiliary_kill_le_repetition {b n k : ℕ} (hbn : b ≤ n) (hkn : k ≤ n)
    (hn : 0 < n) :
    ((b : ℝ) / (2 * n))^k ≤ 1 - properFraction n k +
      properFraction n k * killFraction b n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount := repetition_count_mono (k := k) hbn
  have hq := properFraction_le_one n k
  have hden : (0 : ℝ) < (2 : ℝ)^k * (n : ℝ)^k := by positivity
  have hp : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  rw [properFraction_mul_kill hkn hn]
  unfold properFraction at hq ⊢
  rw [div_le_one (by positivity)] at hq
  rw [div_pow, mul_pow]
  have hnonneg : 0 ≤ (n : ℝ)^k - n.descFactorial k := sub_nonneg.mpr hq
  have hm := mul_le_mul_of_nonneg_right hp hnonneg
  have hd : (b : ℝ)^k - b.descFactorial k ≤
      (2 : ℝ)^k * ((n : ℝ)^k - n.descFactorial k) := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hd hden.le
  have he : (2 : ℝ)^k * ((n : ℝ)^k - n.descFactorial k) /
      ((2 : ℝ)^k * (n : ℝ)^k) = 1 - (n.descFactorial k : ℝ) / (n : ℝ)^k := by
    field_simp
  rw [he, sub_div] at hdiv
  linarith

theorem clauseAverage_alive {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    clauseAverage k alive S = alive S * (1 - killFraction (forcedVariables S).card n k) := by
  by_cases hS : S.Nonempty
  · have h := singleUNSAT_eq hkn S
    have he : (uniformProbability (fun C : ProperClause n k => KillsSolutions S C)) =
        killingProbability k S := by
      apply uniformProbability_congr
      exact fun _ => (and_iff_right hS).symm
    rw [he, killingProbability_of_nonempty S hS] at h
    change killFraction _ _ _ = 1 - clauseAverage k alive S at h
    simp only [alive, ite_eq_left hS, one_mul]
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [clauseAverage, addClause, alive_empty, uniformMean_zero]

theorem scaled_proper_le_auxiliaryAverage {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    (fun S => properFraction n k * clauseAverage k alive S) ≤ auxiliaryAverage (n := n) k alive := by
  intro S
  change properFraction n k * clauseAverage k alive S ≤ auxiliaryAverage k alive S
  rw [auxiliaryAverage_alive hn, clauseAverage_alive hkn]
  have hb : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := auxiliary_kill_le_repetition hb hkn hn
  have hh : properFraction n k * (1 - killFraction (forcedVariables S).card n k) ≤
      1 - (forcedFraction S / 2)^k := by
    unfold forcedFraction
    rw [div_div]
    rw [mul_comm (n : ℝ) 2]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hh (alive_nonneg S)
  nlinarith

theorem proper_scaled_le_auxiliaryProbability {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (m : ℕ) :
    (properFraction n k)^m * properSATProbability n k m ≤ auxiliaryProbability n k m := by
  have hstep := scaled_proper_le_auxiliaryAverage hn hkn
  let B : (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
    fun f S => properFraction n k * clauseAverage k f S
  have hB : Monotone B := by
    intro f g h S
    exact mul_le_mul_of_nonneg_left (finiteClauseAverage_mono _ h S) (properFraction_nonneg n k)
  have hcomm : Function.Commute (auxiliaryAverage (n := n) k) B := by
    intro f
    unfold B auxiliaryAverage embeddedAverage
    rw [finiteClauseAverage_const_mul]
    funext S
    congr 1
    exact congrFun (finiteClauseAverage_commute
      (fun C : AuxiliaryClause n k => fun σ => auxiliarySatisfies σ (embedAuxiliaryClause id C))
      (fun C : ProperClause n k => fun σ => SatisfiesClause σ C) f) S
  have hit (j : ℕ) (f : Finset (Assignment n) → ℝ) :
      B^[j] f = (fun S => (properFraction n k)^j * (clauseAverage k)^[j] f S) := by
    induction j with
    | zero => funext S; simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold B clauseAverage
      funext S
      rw [uniformMean_const_mul]
      rw [Function.iterate_succ_apply', pow_succ]
      ring
  have h := iterate_compare_of_commute (auxiliaryAverage k) B
    (fun _ _ h => finiteClauseAverage_mono _ h) hB hcomm hstep m Finset.univ
  rw [hit] at h
  rw [properSATProbability_eq_survival]
  exact h

theorem repeatPairs_succ (k : ℕ) : repeatPairs (k + 1) = repeatPairs k + k := by
  simp only [repeatPairs, Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
  ring

theorem repeatPairs_nonneg (k : ℕ) : 0 ≤ repeatPairs k := Nat.cast_nonneg _

theorem properFraction_succ {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    properFraction n (k + 1) = properFraction n k * (1 - (k : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold properFraction
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, pow_succ]
  field_simp

theorem properFraction_lower {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    1 - repeatPairs k / n ≤ properFraction n k := by
  induction k with
  | zero => simp [properFraction]
  | succ k ih =>
    have hkn' : k ≤ n := by omega
    have hi := ih hkn'
    have hle := properFraction_le_one n k
    have hprod := mul_le_mul_of_nonneg_right hle (show 0 ≤ (k : ℝ) / n by positivity)
    rw [properFraction_succ hn hkn', repeatPairs_succ, add_div]
    nlinarith

theorem auxiliarySurvival_nonneg {n k : ℕ} (m : ℕ) (S : Finset (Assignment n)) :
    0 ≤ auxiliarySurvival k m S := by
  induction m generalizing S with
  | zero => exact alive_nonneg S
  | succ m ih => rw [auxiliarySurvival_succ]; exact uniformMean_nonneg (fun _ => ih _)

theorem auxiliarySurvival_le_one {n k : ℕ} (hn : 0 < n) (m : ℕ) (S : Finset (Assignment n)) :
    auxiliarySurvival k m S ≤ 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  induction m generalizing S with
  | zero => exact alive_le_one S
  | succ m ih =>
    rw [auxiliarySurvival_succ, ← uniformMean_const (α := AuxiliaryClause n k) (1 : ℝ)]
    exact uniformMean_mono (fun _ => ih _)

theorem auxiliaryProbability_nonneg (n k m : ℕ) : 0 ≤ auxiliaryProbability n k m :=
  auxiliarySurvival_nonneg _ _

theorem auxiliaryProbability_le_one {n : ℕ} (hn : 0 < n) (k m : ℕ) :
    auxiliaryProbability n k m ≤ 1 := auxiliarySurvival_le_one hn _ _

theorem exp_neg_two_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ 1 - x by linarith)
  have hh : 1 ≤ Real.exp (2 * x) * (1 - x) := by nlinarith
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (2 * x))).mp
  rw [← Real.exp_add, show 2 * x + -2 * x = 0 by ring, Real.exp_zero]
  simpa only [mul_comm] using hh

theorem transferFactor_pos (k : ℕ) : 0 < transferFactor k := Real.exp_pos _

theorem properFraction_pow_lower {n k m : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (hm : m ≤ mainCap n k) :
    transferFactor k ≤ (properFraction n k)^m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ repeatPairs k / n := div_nonneg (repeatPairs_nonneg k) hn'.le
  have hx : repeatPairs k / n ≤ 1 / 2 := (div_le_iff₀ hn').mpr (by linarith)
  have hbase := (exp_neg_two_le_one_sub hx0 hx).trans (properFraction_lower hn hkn)
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hbase m
  rw [← Real.exp_nat_mul] at hpow
  apply le_trans _ hpow
  apply Real.exp_le_exp.mpr
  have hm' : (m : ℝ) ≤ (capMultiplier k : ℝ) * n := by exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_right hm' hx0
  have he : ((capMultiplier k : ℝ) * n) * (repeatPairs k / n) =
      (capMultiplier k : ℝ) * repeatPairs k := by field_simp
  rw [he] at hh
  nlinarith

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Main
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem floor_density_le_cap {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k) :
    ⌊c * (n : ℝ)⌋₊ ≤ mainCap n k := by
  have h := (Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))).trans
    (mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  exact_mod_cast (show (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ (mainCap n k : ℝ) by
    simpa only [mainCap, Nat.cast_mul] using h)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped BigOperators

theorem relaxedMinimum_attained {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    ∃ s, relaxedViolations s indices signs = relaxedMinimumViolations indices signs := by
  unfold relaxedMinimumViolations
  exact Nat.find_spec (p := fun v => ∃ s, relaxedViolations s indices signs = v) _

theorem relaxedMinimum_le {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) (s : Fin n → Bool) :
    relaxedMinimumViolations indices signs ≤ relaxedViolations s indices signs :=
  Nat.find_min' _ ⟨s, rfl⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RootEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem relaxedViolations_eq_sum {n m : ℕ} (s : Fin n → Bool)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    relaxedViolations s indices signs =
      ∑ j, if relaxedClauseSatisfied s (indices j) (signs j) then 0 else 1 := by
  simp only [relaxedViolations, Finset.card_eq_sum_ones, Finset.sum_filter, ite_not]

theorem clauseMinimum_le_length {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    clauseMinimum cs ≤ m := by
  exact (relaxedMinimum_le _ _ (fun _ => false)).trans
    ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m))

theorem clauseMinimum_le_add_one {n m : ℕ} (cs ds : Fin m → RelaxedClause n)
    (q : Fin m) (h : ∀ j, j ≠ q → cs j = ds j) :
    clauseMinimum cs ≤ clauseMinimum ds + 1 := by
  classical
  obtain ⟨s, hs⟩ := relaxedMinimum_attained (fun j => (ds j).1) (fun j => (ds j).2)
  apply (relaxedMinimum_le _ _ s).trans
  unfold clauseMinimum
  rw [← hs]
  let S := Finset.univ.filter fun j => ¬relaxedClauseSatisfied s (ds j).1 (ds j).2
  have hsub : (Finset.univ.filter fun j =>
      ¬relaxedClauseSatisfied s (cs j).1 (cs j).2) ⊆ insert q S := by
    intro j hj
    by_cases hjq : j = q
    · exact Finset.mem_insert.mpr (Or.inl hjq)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← h j hjq]
      exact (Finset.mem_filter.mp hj).2
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem clauseMinimum_update_bound {n m : ℕ} (cs : Fin m → RelaxedClause n)
    (q : Fin m) (c : RelaxedClause n) :
    |(clauseMinimum cs : ℝ) - clauseMinimum (Function.update cs q c)| ≤ 1 := by
  have h : ∀ j, j ≠ q → cs j = Function.update cs q c j := by
    intro j hj
    exact (Function.update_of_ne hj c cs).symm
  have h₁ := clauseMinimum_le_add_one cs (Function.update cs q c) q h
  have h₂ := clauseMinimum_le_add_one (Function.update cs q c) cs q
    (fun j hj => (h j hj).symm)
  have h₁' : (clauseMinimum cs : ℝ) ≤ clauseMinimum (Function.update cs q c) + 1 := by
    exact_mod_cast h₁
  have h₂' : (clauseMinimum (Function.update cs q c) : ℝ) ≤ clauseMinimum cs + 1 := by
    exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem clauseMinimum_cons_bounds {n m : ℕ} (cs : Fin m → RelaxedClause n)
    (c : RelaxedClause n) :
    clauseMinimum cs ≤ clauseMinimum (Fin.cons c cs) ∧
      clauseMinimum (Fin.cons c cs) ≤ clauseMinimum cs + 1 := by
  have he (s : Fin n → Bool) :
      relaxedViolations s (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).1)
        (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).2) =
        (if relaxedClauseSatisfied s c.1 c.2 then 0 else 1) +
          relaxedViolations s (fun j => (cs j).1) (fun j => (cs j).2) := by
    simp only [relaxedViolations_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  constructor
  · obtain ⟨s, hs⟩ := relaxedMinimum_attained
      (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).1)
      (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).2)
    apply (relaxedMinimum_le _ _ s).trans
    change _ ≤ relaxedMinimumViolations _ _
    rw [← hs, he]
    omega
  · obtain ⟨s, hs⟩ := relaxedMinimum_attained (fun j => (cs j).1) (fun j => (cs j).2)
    apply (relaxedMinimum_le _ _ s).trans
    change _ ≤ relaxedMinimumViolations _ _ + 1
    rw [he, ← hs]
    split <;> omega

theorem rootMinimum_bound (n m : ℕ) (x : RootPath (RelaxedClause n) m) :
    |rootMinimum n m x| ≤ m := by
  rw [rootMinimum, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast clauseMinimum_le_length (rootArray m x)

theorem rootMinimum_replace (n m : ℕ) (q : Fin m)
    (x : RootPath (RelaxedClause n) m) (c : RelaxedClause n) :
    |rootMinimum n m x - rootMinimum n m (replaceRoot m x q c)| ≤ 1 := by
  simp only [rootMinimum, rootArray_replace]
  exact clauseMinimum_update_bound _ _ _

theorem rootMinimum_cons (n m : ℕ) (c : RelaxedClause n)
    (x : RootPath (RelaxedClause n) m) :
    |rootMinimum n (m+1) (c,x) - rootMinimum n m x| ≤ 1 := by
  obtain ⟨hlo,hhi⟩ := clauseMinimum_cons_bounds (rootArray m x) c
  have hlo' : (clauseMinimum (rootArray m x) : ℝ) ≤
      clauseMinimum (Fin.cons c (rootArray m x)) := by exact_mod_cast hlo
  have hhi' : (clauseMinimum (Fin.cons c (rootArray m x)) : ℝ) ≤
      clauseMinimum (rootArray m x) + 1 := by exact_mod_cast hhi
  change |(clauseMinimum (Fin.cons c (rootArray m x)) : ℝ)-clauseMinimum (rootArray m x)| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rootMinimum_variance (n : ℕ) (μ : Measure (RelaxedClause n))
    [IsProbabilityMeasure μ] (r : ℝ≥0) :
    (∫ m : ℕ, ∫ x, (rootMinimum n m x - poissonRootAverage μ r (rootMinimum n))^2
      ∂rootLaw m (fun _ => μ) ∂poissonMeasure r) ≤ 3/2 * (r : ℝ) := by
  have h := poisson_root_second_moment μ r
    (fun m => measurable_of_countable (rootMinimum n m)) (rootMinimum_bound n)
    (show (0 : ℝ) ≤ 1 by norm_num) (rootMinimum_replace n) (rootMinimum_cons n)
    (poissonRootAverage μ r (rootMinimum n))
  norm_num only [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, one_pow] at h
  exact h

theorem rootMinimum_mean_sq (n : ℕ) (μ : Measure (RelaxedClause n))
    [IsProbabilityMeasure μ] (r : ℝ≥0) :
    rootSatisfiableProbability n μ r * (poissonRootAverage μ r (rootMinimum n))^2 ≤
      3/2 * (r : ℝ) := by
  let c := poissonRootAverage μ r (rootMinimum n)
  have hinner (m : ℕ) : Integrable (fun x : RootPath (RelaxedClause n) m =>
      (rootMinimum n m x-c)^2) (rootLaw m (fun _ => μ)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((m+|c|)^2)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := (abs_sub (rootMinimum n m x) c).trans
      (add_le_add (rootMinimum_bound n m x) le_rfl)
    nlinarith [sq_abs (rootMinimum n m x-c), abs_nonneg (rootMinimum n m x-c),
      abs_nonneg c, Nat.cast_nonneg (α := ℝ) m]
  have houter : Integrable (fun m : ℕ => ∫ x, (rootMinimum n m x-c)^2
      ∂rootLaw m (fun _ => μ)) (poissonMeasure r) := by
    apply poisson_integrable_quadratic r (A := 2*c^2) (B := 2)
    intro m
    apply abs_integral_le_bound
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := rootMinimum_bound n m x
    have hsq : (rootMinimum n m x)^2 ≤ (m : ℝ)^2 := by
      nlinarith [sq_abs (rootMinimum n m x), abs_nonneg (rootMinimum n m x),
        Nat.cast_nonneg (α := ℝ) m]
    nlinarith [sq_nonneg (rootMinimum n m x+c)]
  have hpoint (m : ℕ) (x : RootPath (RelaxedClause n) m) :
      (if rootMinimum n m x = 0 then (1 : ℝ) else 0)*c^2 ≤
        (rootMinimum n m x-c)^2 := by
    split_ifs with h
    · rw [h]; ring_nf; exact le_rfl
    · simpa only [zero_mul] using sq_nonneg (rootMinimum n m x-c)
  have hb := integral_mono_of_nonneg (μ := poissonMeasure r)
    (ae_of_all _ (fun m => integral_nonneg (fun x => by positivity))) houter
    (ae_of_all _ (fun m => integral_mono_of_nonneg
      (ae_of_all _ (fun x => by positivity)) (hinner m) (ae_of_all _ (hpoint m))))
  simp only [integral_mul_const] at hb
  exact hb.trans (rootMinimum_variance n μ r)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_AuxiliaryEnergy
attribute [-instance] _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem finiteClauseAverage_iterate {n m : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (S : Finset (Assignment n)) :
    ((finiteClauseAverage sat)^[m] alive) S =
      uniformMean (fun F : Fin m → C => alive (S.filter (fun s => ∀ j, sat (F j) s))) := by
  induction m generalizing S with
  | zero =>
    simp only [Function.iterate_zero_apply, Fin.forall_fin_zero, Finset.filter_true]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', finiteClauseAverage, uniformMean_fin_succ]
    apply uniformMean_congr
    intro c
    rw [ih]
    apply uniformMean_congr
    intro F
    congr 1
    ext s
    simp only [Finset.mem_filter, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    tauto

theorem clauseMinimum_zero_iff {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    clauseMinimum cs = 0 ↔ ∃ s : Assignment n, ∀ j,
      relaxedClauseSatisfied s (cs j).1 (cs j).2 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := relaxedMinimum_attained (fun j => (cs j).1) (fun j => (cs j).2)
    refine ⟨s, ?_⟩
    change relaxedViolations s _ _ = clauseMinimum cs at hs
    rw [h] at hs
    simpa only [relaxedViolations, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_not] using hs
  · rintro ⟨s, hs⟩
    have h := relaxedMinimum_le (fun j => (cs j).1) (fun j => (cs j).2) s
    have hz : relaxedViolations s (fun j => (cs j).1) (fun j => (cs j).2) = 0 := by
      simp only [relaxedViolations, hs, not_true_eq_false, Finset.filter_false,
        Finset.card_empty]
    exact Nat.eq_zero_of_le_zero (hz ▸ h)

theorem auxiliaryProbability_eq_minimum (n m : ℕ) :
    auxiliaryProbability n 3 m =
      uniformMean (fun cs : Fin m → RelaxedClause n =>
        if clauseMinimum cs = 0 then 1 else 0) := by
  unfold auxiliaryProbability auxiliarySurvival auxiliaryAverage embeddedAverage
  rw [finiteClauseAverage_iterate]
  let e := Equiv.piCongrRight (fun _ : Fin m => relaxedClauseEquiv n)
  rw [← uniformMean_equiv e]
  apply uniformMean_congr
  intro cs
  unfold alive
  congr 1
  apply propext
  rw [clauseMinimum_zero_iff]
  simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
  rfl

theorem integral_rootMinimum_zero (n m : ℕ) [NeZero n] :
    (∫ x : RootPath (RelaxedClause n) m,
      (if rootMinimum n m x = 0 then (1 : ℝ) else 0)
      ∂rootLaw m (fun _ => finiteUniform (RelaxedClause n))) = auxiliaryProbability n 3 m := by
  rw [auxiliaryProbability_eq_minimum]
  change (∫ x, (if (clauseMinimum (rootArray m x) : ℝ) = 0 then (1 : ℝ) else 0)
    ∂rootLaw m (fun _ => finiteUniform (RelaxedClause n))) = _
  simp only [Nat.cast_eq_zero]
  rw [integral_rootArray_eq_pi (finiteUniform (RelaxedClause n)) m
    (fun cs => if clauseMinimum cs = 0 then (1 : ℝ) else 0),
    finiteUniform_pi, integral_finiteUniform]
  simp only [uniformMean, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem rootSatisfiableProbability_eq_auxiliary (n : ℕ) [NeZero n] (r : ℝ≥0) :
    rootSatisfiableProbability n (finiteUniform (RelaxedClause n)) r =
      ∫ m : ℕ, auxiliaryProbability n 3 m ∂poissonMeasure r := by
  unfold rootSatisfiableProbability poissonRootAverage rootAverage
  simp only [integral_rootMinimum_zero]

theorem relaxedFixedMinimum_nonneg (n m : ℕ) : 0 ≤ relaxedFixedMinimum n m :=
  uniformMean_nonneg (fun _ => Nat.cast_nonneg _)

theorem relaxedPoissonMinimum_nonneg (n : ℕ) (a : ℝ≥0) :
    0 ≤ relaxedPoissonMinimum n a := integral_nonneg (fun _ => relaxedFixedMinimum_nonneg _ _)

theorem integral_rootMinimum_eq (n m : ℕ) [NeZero n] :
    (∫ x : RootPath (RelaxedClause n) m, rootMinimum n m x
      ∂rootLaw m (fun _ => finiteUniform (RelaxedClause n))) = relaxedFixedMinimum n m := by
  simp only [rootMinimum]
  rw [integral_rootArray_eq_pi (finiteUniform (RelaxedClause n)) m
    (fun cs => (clauseMinimum cs : ℝ)), finiteUniform_pi, integral_finiteUniform]
  simp only [relaxedFixedMinimum, uniformMean, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem poissonRootAverage_minimum_eq (n : ℕ) [NeZero n] (a : ℝ≥0) :
    poissonRootAverage (finiteUniform (RelaxedClause n)) (a*n) (rootMinimum n) =
      relaxedPoissonMinimum n a := by
  unfold poissonRootAverage rootAverage relaxedPoissonMinimum
  simp only [integral_rootMinimum_eq]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonCountBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem poisson_upper_deviation (r : ℝ≥0) {d : ℝ} (hd : 0 < d) :
    (∫ m : ℕ, (if (r : ℝ) + d < m then (1 : ℝ) else 0) ∂poissonMeasure r) ≤
      (r : ℝ) / d^2 := by
  have hi : Integrable (fun m : ℕ => if (r : ℝ)+d < m then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => by split <;> norm_num)
  have hs : Integrable (fun m : ℕ => ((m : ℝ)-(r : ℝ))^2) (poissonMeasure r) :=
    ((memLp_two_iff_integrable_sq (measurable_of_countable
      (fun m : ℕ => (m : ℝ))).aestronglyMeasurable).mpr
      (poisson_integrable_count_sq r) |>.sub (memLp_const (r : ℝ))).integrable_sq
  have h := integral_mono hi (hs.div_const (d^2)) (fun m => show
      (if (r : ℝ)+d < m then (1 : ℝ) else 0) ≤ ((m : ℝ)-(r : ℝ))^2 / d^2 from by
    split_ifs with hm
    · apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
      nlinarith
    · exact div_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [integral_div, poisson_variance] at h
  exact h

theorem poisson_density_upper_tail {a : ℝ≥0} {b : ℝ} (hab : (a : ℝ) < b)
    {n : ℕ} (hn : 0 < n) :
    (∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) ≤
      (a : ℝ) / ((b-a)^2*n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (b-a)*(n : ℝ) := mul_pos (sub_pos.mpr hab) hn'
  have h := poisson_upper_deviation (a*n) hd
  have he : (a*n : ℝ≥0) + (b-(a : ℝ))*(n : ℝ) = b*n := by
    push_cast
    ring
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  field_simp

theorem poisson_density_upper_tail_tendsto {a : ℝ≥0} {b : ℝ} (hab : (a : ℝ) < b) :
    Tendsto (fun n : ℕ => ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0)
      ∂poissonMeasure (a*n)) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => (a : ℝ) / ((b-a)^2*n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
        ((a : ℝ)/(b-a)^2)).congr
        (fun n => by simp only [Function.comp_apply, div_eq_mul_inv, mul_inv]; ring)
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun m => by positivity)))
    _ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact poisson_density_upper_tail hab hn

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonSATProbability
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology Classical

theorem auxiliaryPoissonProbability_lower {n : ℕ} (hn : 6 ≤ n) (a : ℝ≥0)
    {b : ℝ} (hb0 : 0 ≤ b) (hbcap : b ≤ capMultiplier 3) :
    transferFactor 3 * properSATProbability n 3 ⌊b*n⌋₊ *
      (1 - ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) ≤
      auxiliaryPoissonProbability n a := by
  have hn0 : 0 < n := by omega
  have h3 : 3 ≤ n := by omega
  have hcap := floor_density_le_cap (n := n) hb0 hbcap
  let c := transferFactor 3 * properSATProbability n 3 ⌊b*n⌋₊
  have hp : ∀ m : ℕ, c * (1 - if b*n < m then (1 : ℝ) else 0) ≤ auxiliaryProbability n 3 m := by
    intro m
    by_cases hm : b*n < m
    · simpa only [ite_eq_left hm, sub_self, mul_zero] using auxiliaryProbability_nonneg n 3 m
    · have hmc : m ≤ ⌊b*n⌋₊ := Nat.le_floor (le_of_not_gt hm)
      have hfac := properFraction_pow_lower hn0 h3
        (by norm_num [repeatPairs]; omega : 2 * repeatPairs 3 ≤ n) (hmc.trans hcap)
      have hsat := properSATProbability_antitone h3 hmc
      have hprod := mul_le_mul hfac hsat (properSATProbability_nonneg n 3 _)
        (pow_nonneg (properFraction_nonneg n 3) m)
      simpa only [ite_eq_right hm, sub_zero, mul_one, c] using
        hprod.trans (proper_scaled_le_auxiliaryProbability hn0 h3 m)
  have hi : Integrable (fun m : ℕ => if b*n < m then (1 : ℝ) else 0)
      (poissonMeasure (a*n)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => by split <;> norm_num)
  have ha : Integrable (fun m => auxiliaryProbability n 3 m) (poissonMeasure (a*n)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun m => abs_le.mpr ⟨by linarith [auxiliaryProbability_nonneg n 3 m],
      auxiliaryProbability_le_one hn0 3 m⟩)
  have h := integral_mono ((integrable_const 1).sub hi |>.const_mul c) ha hp
  rw [integral_const_mul] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, c,
    auxiliaryPoissonProbability] using h

theorem auxiliaryPoissonProbability_subcritical {a : ℝ≥0}
    (ha : (a : ℝ) < limitingCenter 3) :
    ∀ᶠ n : ℕ in atTop, transferFactor 3 / 4 ≤ auxiliaryPoissonProbability n a := by
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have hb0 : 0 ≤ b := (show (0 : ℝ) ≤ a from a.property).trans hab.le
  have hbcap : b ≤ capMultiplier 3 := (hb.trans (limitingCenter_lt_cap_sat 3 (by decide))).le
  have hs := (subcritical_limit_sat 3 (by decide) b hb0 hb).eventually
    (Ioi_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  have ht := (poisson_density_upper_tail_tendsto hab).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs, ht, eventually_ge_atTop 6] with n hn ht hn6
  have h := auxiliaryPoissonProbability_lower hn6 a hb0 hbcap
  have hc := transferFactor_pos 3
  have hx : (1/4 : ℝ) ≤ properSATProbability n 3 ⌊b*n⌋₊ *
      (1 - ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n)) := by
    have hmul := mul_le_mul hn.le (show (1/2 : ℝ) ≤ 1 -
      ∫ m : ℕ, (if b*n < m then (1 : ℝ) else 0) ∂poissonMeasure (a*n) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1/2) (properSATProbability_nonneg n 3 ⌊b*n⌋₊)
    norm_num at hmul
    exact hmul
  have hprod := mul_le_mul_of_nonneg_left hx hc.le
  nlinarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SubcriticalEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem relaxedPoissonMinimum_mean_sq (n : ℕ) [NeZero n] (a : ℝ≥0) :
    auxiliaryPoissonProbability n a * (relaxedPoissonMinimum n a)^2 ≤
      3/2 * (a : ℝ)*n := by
  have h := rootMinimum_mean_sq n (finiteUniform (RelaxedClause n)) (a*n)
  rw [rootSatisfiableProbability_eq_auxiliary, poissonRootAverage_minimum_eq] at h
  simpa only [auxiliaryPoissonProbability, NNReal.coe_mul, NNReal.coe_natCast, mul_assoc] using h

theorem relaxedPoissonMinimum_subcritical_sat_oai {a : ℝ≥0}
    (ha : (a : ℝ) < limitingCenter 3) :
    Tendsto (fun n : ℕ => relaxedPoissonMinimum n a / n) atTop (nhds 0) := by
  let c := transferFactor 3 / 4
  have hc : 0 < c := div_pos (transferFactor_pos 3) (by norm_num)
  let K := (3/2 : ℝ) * a / c
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (K/n)) atTop (nhds 0) := by
    have ht := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul K
    simpa only [Function.comp_apply, ← div_eq_mul_inv, mul_zero, Real.sqrt_zero] using ht.sqrt
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    div_nonneg (relaxedPoissonMinimum_nonneg n a) (Nat.cast_nonneg n))) _ hlim
  filter_upwards [auxiliaryPoissonProbability_subcritical ha, eventually_gt_atTop 0] with n hp hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hv := relaxedPoissonMinimum_mean_sq n a
  have hsq : (relaxedPoissonMinimum n a)^2 ≤ K*n := by
    dsimp only [K]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm _ c]
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans hv
  have hd := div_le_div_of_nonneg_right hsq (sq_nonneg (n : ℝ))
  have he : (relaxedPoissonMinimum n a/n)^2 ≤ K/n := by
    rw [div_pow]
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have hnon := div_nonneg (relaxedPoissonMinimum_nonneg n a) hn'.le
  simpa only [Real.sqrt_sq hnon] using Real.sqrt_le_sqrt he

end FixedClauseThreshold.Computability

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat_oai := @OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat_oai
