-- Prove2me | solution 1 for OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:44.671644+00:00
-- url     : https://prove2.me/submissions/8a42219e-e3da-4cf8-99fd-550a549bee7f

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

variable {n : ℕ}

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

end KernelTower
end DilutedSpinGlass

end

end OAI
end

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProductTowers
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Conditional power means commute with literal relabeling of every hidden
mark variable. This is needed for the physical Palm exchangeability. -/
theorem backwardLog_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n (transport e n T) m f =
      backwardLog n T m (f ∘ pathEquiv e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, transport]
    have he : (fun a : Λ => backwardLog n (transport e n (T.2 (e.symm a)))
        (fun j => m j.succ) (fun y => f (a,y))) =
      (fun a : Λ => backwardLog n (T.2 (e.symm a))
        (fun j => m j.succ) ((fun y => f (a,y)) ∘ pathEquiv e n)) :=
      funext (fun a => ih (T.2 (e.symm a)) (fun j => m j.succ) (fun y => f (a,y)))
    rw [he, FiniteLaw.logMean_transport]
    congr 1
    funext a
    simp only [Function.comp_def, Equiv.symm_apply_apply, pathEquiv_cons]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

theorem eq_of_weights {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

end DilutedSpinGlass.KernelTower

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

/-- A parameter in a Poisson root average stays measurable, despite the
count-dependent dimension of the actual root state. -/
theorem measurable_poissonRootAverage (r : ℝ≥0)
    {F : X → (n : ℕ) → RootPath Ω n → ℝ}
    (hF : ∀ n, Measurable (fun z : X × RootPath Ω n => F z.1 n z.2)) :
    Measurable (fun x => poissonRootAverage μ r (F x)) := by
  have hm : Measurable (fun z : X × ℕ => rootAverage μ (F z.1) z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun x => ∫ y, F x n y ∂rootLaw n (fun _ => μ))
    exact (hF n).stronglyMeasurable.integral_prod_right'.measurable
  change Measurable (fun x => ∫ n, rootAverage μ (F x) n ∂poissonMeasure r)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

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

/-- A linear root bound is sufficient for all count averages in the physical
model; no bounded support for the Poisson count is introduced. -/
theorem poissonRootAverage_bound (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {A D : ℝ}
    (hB : ∀ n x, |F n x| ≤ A+D*n) :
    |poissonRootAverage μ r F| ≤ A+D*(r : ℝ) := by
  have hm (n : ℕ) : |rootAverage μ F n| ≤ A+D*n := abs_integral_le_bound (hB n)
  have hi : Integrable (rootAverage μ F) (poissonMeasure r) :=
    poisson_integrable_linear r hm
  have h := integral_mono (hi.norm) ((integrable_const A).add ((poisson_integrable_count r).const_mul D)) hm
  simp only [Real.norm_eq_abs,Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((poisson_integrable_count r).const_mul D),
    integral_const_mul,poisson_mean] at h
  have hnorm := norm_integral_le_integral_norm (μ := poissonMeasure r) (f := rootAverage μ F)
  simpa only [poissonRootAverage,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using
    hnorm.trans h

/-- Uniform stability passes through the entire marked-Poisson root law. -/
theorem poissonRootAverage_stability (r : ℝ≥0)
    {F G : (n : ℕ) → RootPath Ω n → ℝ} {A B D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hBF : ∀ n x, |F n x| ≤ A+B*n) (hBG : ∀ n x, |G n x| ≤ A+B*n)
    (hdiff : ∀ n x, |F n x-G n x| ≤ D) :
    |poissonRootAverage μ r F-poissonRootAverage μ r G| ≤ D := by
  have hiF : Integrable (rootAverage μ F) (poissonMeasure r) :=
    poisson_integrable_linear r (fun n => abs_integral_le_bound (hBF n))
  have hiG : Integrable (rootAverage μ G) (poissonMeasure r) :=
    poisson_integrable_linear r (fun n => abs_integral_le_bound (hBG n))
  unfold poissonRootAverage
  rw [← integral_sub hiF hiG]
  apply abs_integral_le_bound
  intro n
  unfold rootAverage
  rw [← integral_sub ((bounded_memLp (hF n) (hBF n) 1).integrable le_rfl)
    ((bounded_memLp (hG n) (hBG n) 1).integrable le_rfl)]
  exact abs_integral_le_bound (hdiff n)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaUncurry {Y : Type*} [MeasurableSpace Y] {f : (i : I) → X i → Y}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x : Sigma X => f x.1 x.2) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro i
  rw [← MeasurableSpace.comap_le_iff_le_map]
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {I : Type*} {X : I → Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [∀ i, MeasurableSpace (X i)]
    (μ : Measure I) (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Sufficient integrability on the genuine disjoint-union root law. -/
theorem familyLaw_integrable_bound (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) {B : I → ℝ} (hB : Integrable B μ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) := by
  let F : Sigma X → ℝ := fun z => f z.1 z.2
  have hm : Measurable F := measurable_sigmaUncurry hf
  have hi (i : I) : Integrable (f i) (ν i) :=
    Integrable.of_bound (hf i).aestronglyMeasurable (B i) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb i x))
  have hi' (i : I) : Integrable F (familyKernel ν i) := by
    change Integrable F ((ν i).map (Sigma.mk i))
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr (hi i)
  apply (Measure.integrable_comp_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi', ?_⟩
  apply hB.mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ z, ‖F z‖ ∂(ν i).map (Sigma.mk i)) ≤ B i
  rw [integral_map (measurable_sigmaMk i).aemeasurable hm.norm.aestronglyMeasurable]
  have hh := integral_mono (hi i).norm (integrable_const (B i))
    (fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

omit [∀ i, IsProbabilityMeasure (ν i)] in
 
theorem integral_familyLaw (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν)) :
    (∫ z : Sigma X, f z.1 z.2 ∂familyLaw μ ν) = ∫ i, ∫ x, f i x ∂ν i ∂μ := by
  unfold familyLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ i, ∫ z : Sigma X, f z.1 z.2 ∂(ν i).map (Sigma.mk i) ∂μ) = _
  apply integral_congr_ae
  apply ae_of_all
  intro i
  exact integral_map (measurable_sigmaMk i).aemeasurable
    (measurable_sigmaUncurry hf).aestronglyMeasurable

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_memLp_linear {f : (n : ℕ) → X n → ℝ}
    (hf : ∀ n, Measurable (f n)) {A B : ℝ} (hb : ∀ n x, |f n x| ≤ A+B*n) :
    MemLp (fun z : Sigma X => f z.1 z.2) 2 (familyLaw (poissonMeasure r) ν) := by
  apply (memLp_two_iff_integrable_sq (measurable_sigmaUncurry hf).aestronglyMeasurable).mpr
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n x => (f n x)^2) (fun n => (hf n).pow_const 2)
    (B := fun n => 2*A^2+2*B^2*(n : ℝ)^2)
  · apply poisson_integrable_quadratic r (A := 2*A^2) (B := 2*B^2)
    intro n
    rw [abs_of_nonneg (by positivity)]
  · intro n x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : (f n x)^2 ≤ (A+B*n)^2 := by
      exact sq_le_sq' (abs_le.mp (hb n x)).1 (abs_le.mp (hb n x)).2
    nlinarith [sq_nonneg (A-B*n)]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_memLp :
    MemLp (fun z : Sigma X => (z.1 : ℝ)) 2 (familyLaw (poissonMeasure r) ν) := by
  apply familyPoisson_memLp_linear ν r (fun _ => measurable_const) (A := 0) (B := 1)
  intro n x
  simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeterogeneousMarks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- Adding a type uses its own prior, independently of all old marks. -/
theorem tower_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (split roots i) L (tower (Fin.cons i roots) L T Q) =
      KernelTower.prod L (tower roots L T Q) (markPrior L (Q i)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro z
      change T.1.weight z.1.1 *
          (∏ j : Fin (k+1), (Q ((Fin.cons i roots : Fin (k+1) → I) j) 0).weight
            ((Fin.cons z.2 z.1.2 : Row (A := A) (Fin.cons i roots)) j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      rw [Fin.prod_univ_succ]
      change T.1.weight z.1.1 *
        ((Q i 0).weight z.2 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      ring
    · funext z
      exact ih (T.2 z.1.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    physical roots L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      physical (Fin.cons i roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) =
      (y.1.1, physical (Fin.cons i roots) L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_succ {k : ℕ} (roots : Fin k → I) (i : I) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    mark q L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      mark q.succ L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 q.succ, mark q L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) = (y.1.2 q.succ, mark q.succ L y.2)
    rw [ih]
    rfl

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_zero {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y) = mark 0 L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 0, KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y.2)) =
      (y.1.2 0, mark 0 L y.2)
    rw [ih]
    rfl

variable {k L : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem insertedLog_split (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    insertedLog base roots factor i (KernelTower.pathEquiv (split roots i) L y) =
      logWeight base (Fin.cons i roots) factor y := by
  simp only [insertedLog, logWeight, physical_split, mark_split_succ,
    mark_split_zero, Fin.sum_univ_succ]
  change base (physical (Fin.cons i roots) L y) +
      (∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y))) +
      Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) =
    base (physical (Fin.cons i roots) L y) +
      (Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) +
      ∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y)))
  ring

/-- Uniform add/delete control does not depend on the mark dimension or type. -/
theorem root_cons_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hfactor : ∀ x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Fin.cons i roots) factor - root T Q m base roots factor| ≤ C := by
  have h := KernelTower.backwardLog_transport (split roots i) L
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
  have heq : insertedLog base roots factor i ∘ KernelTower.pathEquiv (split roots i) L =
      logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  unfold root
  rw [← h, ← KernelTower.backwardLog_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
    (logWeight base roots factor)]
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [insertedLog, add_sub_cancel_left] using hfactor
    (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)

/-- Typewise log-factor errors sum on the actual root list. -/
theorem root_factor_stability (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y) - Real.log (factor' i x y)| ≤ C i) :
    |root T Q m base roots factor - root T Q m base roots factor'| ≤ ∑ q, C (roots q) := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [logWeight, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q _ => hC _ _ _))

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
variable {k L : ℕ}

/-- The complete independent row can be integrated as a single finite mark.
Its dimension depends on the realized labels, never on a deterministic cutoff. -/
theorem tower_eq_prod (roots : Fin k → I) (L : ℕ) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower roots L T Q = KernelTower.prod L T
      (markPrior L (fun d => FiniteLaw.pi (fun j => Q (roots j) d))) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_eq_fst (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L y = KernelTower.pathFst L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L y.2) = (y.1.1, KernelTower.pathFst L y.2)
    rw [ih]

/-- All unused finite priors integrate out, exactly, even if their dimension
varies over the full countable type list. -/
theorem root_one (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I) :
    root T Q m base roots (fun _ _ _ => 1) = KernelTower.backwardLog L T m base := by
  unfold root
  have heq : logWeight (A := A) base roots (fun _ _ _ => 1) =
      base ∘ KernelTower.pathFst L := by
    funext y
    simp only [logWeight, Real.log_one, Finset.sum_const_zero, add_zero,
      physical_eq_fst, Function.comp_apply]
  rw [heq, tower_eq_prod]
  exact KernelTower.backwardLog_prod_fst L T _ m base

/-- The pathwise perturbation cost is additive over all realized labels. -/
theorem root_base_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C i) :
    |root T Q m base roots factor - KernelTower.backwardLog L T m base| ≤
      ∑ q, C (roots q) := by
  rw [← root_one T Q m base roots]
  exact root_factor_stability T Q m hm base roots factor (fun _ _ _ => 1) C
    (fun i x y => by simpa only [Real.log_one, sub_zero] using hC i x y)

/-- No lower bound on a type's intensity occurs in this global domination. -/
theorem abs_root_le (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ |KernelTower.backwardLog L T m base| + C*k := by
  have h := root_base_bound T Q m hm base roots factor (fun _ => C) hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have ht := abs_add_le (root T Q m base roots factor - KernelTower.backwardLog L T m base)
    (KernelTower.backwardLog L T m base)
  rw [sub_add_cancel] at ht
  linarith

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

theorem tower_transport {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (rowPerm roots σ) L (tower roots L T Q) =
      tower (roots ∘ σ) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro x
      change T.1.weight x.1 * (∏ q, (Q (roots q) 0).weight
          (Equiv.piCongrLeft (fun q => A (roots q)) σ x.2 q)) =
        T.1.weight x.1 * ∏ q, (Q (roots (σ q)) 0).weight (x.2 q)
      congr 1
      symm
      exact Fintype.prod_equiv σ _ _ (fun q => by rw [Equiv.piCongrLeft_apply_apply])
    · funext x
      exact ih (T.2 x.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      physical roots L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.1, physical roots L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) (q : Fin k) :
    mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y) = mark (σ q) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 (σ q), mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.2 (σ q), mark (σ q) L y.2)
    rw [ih]

variable {k L : ℕ}
omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem logWeight_rowPerm (roots : Fin k → I) (σ : Equiv.Perm (Fin k))
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    logWeight base (roots ∘ σ) factor (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      logWeight base roots factor y := by
  simp only [logWeight, physical_rowPerm, mark_rowPerm, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem root_perm (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (σ : Equiv.Perm (Fin k)) :
    root T Q m base (roots ∘ σ) factor = root T Q m base roots factor := by
  have h := KernelTower.backwardLog_transport (rowPerm roots σ) L (tower roots L T Q) m
    (logWeight base (roots ∘ σ) factor)
  have heq : logWeight base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm roots σ) L =
      logWeight base roots factor := funext (fun y => logWeight_rowPerm roots σ base factor y)
  simpa only [tower_transport, heq, root] using h

end DilutedSpinGlass.HeterogeneousMarks

 

namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L : ℕ}

/-- Replacement may change the complete mark alphabet and prior of that term;
it is proved by two independent insertions, not by identifying the alphabets. -/
theorem root_update_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I) (q : Fin k) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Function.update roots q i) factor - root T Q m base roots factor| ≤ 2*C := by
  classical
  cases k with
  | zero => exact Fin.elim0 q
  | succ k =>
    let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 q
    let row := roots ∘ σ
    let tail := Fin.tail row
    have hrows : Function.update roots q i ∘ σ = Fin.cons i tail := by
      funext j
      refine Fin.cases ?_ (fun t => ?_) j
      · simp [σ]
      · have hneq : σ t.succ ≠ q := by
          have h0 : σ 0 = q := Equiv.swap_apply_left _ _
          rw [← h0]
          exact fun h => Fin.succ_ne_zero t (σ.injective h)
        simp only [Function.comp_apply, Function.update_of_ne hneq, Fin.cons_succ]
        rfl
    have hold : roots ∘ σ = Fin.cons (roots q) tail := by
      have hzero : row 0 = roots q := by simp [row, σ]
      rw [← hzero]
      exact (Fin.cons_self_tail row).symm
    rw [← root_perm T Q m base (Function.update roots q i) factor σ,
      ← root_perm T Q m base roots factor σ, hrows, hold]
    have hnew := root_cons_bound T Q m hm base tail i factor (hf i)
    have hold' := root_cons_bound T Q m hm base tail (roots q) factor (hf (roots q))
    calc
      _ ≤ |root T Q m base (Fin.cons i tail) factor - root T Q m base tail factor| +
          |root T Q m base tail factor - root T Q m base (Fin.cons (roots q) tail) factor| :=
        abs_sub_le _ _ _
      _ ≤ C+C := by rw [abs_sub_comm (root T Q m base tail factor)]; exact add_le_add hnew hold'
      _ = 2*C := by ring

/-- Physical disorder changes only the base energy, even with all countably
many type laws available to the finite realized auxiliary row. -/
theorem root_base_stability (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base base' : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hb : ∀ x, |base x-base' x| ≤ C) :
    |root T Q m base roots factor-root T Q m base' roots factor| ≤ C := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [logWeight, add_sub_add_right_eq_sub] using hb (physical roots L y)

end DilutedSpinGlass.HeterogeneousMarks



end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniformIndexCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω I X : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace X] {L : ℕ}

theorem root_uniform_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j) (base : FinitePath Ω L → ℝ)
    {n : ℕ} (roots : Fin n → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {B C : ℝ}
    (hb : ∀ y, |base y| ≤ B) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ B+C*n := by
  have hh := KernelTower.backwardLog_stability L T m hm
    (f := base) (g := fun _ => 0) (by simpa only [sub_zero] using hb)
  rw [KernelTower.backwardLog_const L T m (fun j => ne_of_gt (hm j)) 0, sub_zero] at hh
  exact (abs_root_le T Q m hm base roots factor hf).trans (add_le_add hh le_rfl)

theorem measurable_root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (factor : X → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (hf : ∀ i y z, Measurable (fun x => factor x i y z)) :
    Measurable (fun x => root T Q m (base x) roots (factor x)) := by
  apply KernelTower.measurable_backwardLog
  intro y
  exact (hb _).add (Finset.measurable_sum _ (fun j _ => (hf _ _ _).log))

theorem measurable_root_base [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (n : ℕ) :
    Measurable (fun z : X × RootPath I n => root T Q m (base z.1) (rootArray n z.2) factor) := by
  apply measurable_from_prod_countable_left
  intro roots
  exact measurable_root T Q m base (rootArray n roots) (fun _ => factor) hb
    (fun _ _ _ => measurable_const)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeterogeneousTwoPoisson
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
open scoped NNReal ENNReal

variable {I J : Type*} [MeasurableSpace I] [MeasurableSpace J]
    (μ : Measure I) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]

/-- Quadratic integrability for a genuine random-dimensional root block. -/
theorem poisson_integrable_root_squared (r : ℝ≥0)
    {F : (n : ℕ) → RootPath I n → ℝ} {A D : ℝ}
    (hF : ∀ n x, |F n x| ≤ A+D*n) (c : ℝ) :
    Integrable (fun n : ℕ => ∫ x, (F n x-c)^2 ∂rootLaw n (fun _ => μ)) (poissonMeasure r) := by
  apply poisson_integrable_quadratic r (A := 2*(|A|+|c|)^2) (B := 2*D^2)
  intro n
  apply abs_integral_le_bound
  intro x
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : |F n x-c| ≤ |A|+|c|+|D| * n := by
    calc
      _ ≤ |F n x|+|c| := abs_sub _ _
      _ ≤ (A+D*n)+|c| := add_le_add (hF n x) le_rfl
      _ ≤ |A|+|c|+|D| * n := by
        have ha := le_abs_self A
        have hd := mul_le_mul_of_nonneg_right (le_abs_self D) hn
        linarith
  rw [abs_of_nonneg (sq_nonneg _)]
  have hs : (F n x-c)^2 ≤ (|A|+|c|+|D| * n)^2 := by
    nlinarith [sq_abs (F n x-c),abs_nonneg (F n x-c)]
  have hscaled_sq : (|D| * (n : ℝ))^2 = D^2 * (n : ℝ)^2 := by
    rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg ((|A|+|c|)-|D| * n)]

/-- Two independent Poisson families, without converting both counts into
one process or conditioning away either of the count fluctuations. -/
theorem two_poisson_roots_second_moment (r s : ℝ≥0)
    {F : (k : ℕ) → RootPath I k → (n : ℕ) → RootPath J n → ℝ}
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ k n, Measurable (fun z : RootPath I k × RootPath J n => F k z.1 n z.2))
    (hB : ∀ k x n y, |F k x n y| ≤ B+C*k+D*n)
    (hrep1 : ∀ k (i : Fin k) x z n y, |F k x n y-F k (replaceRoot k x i z) n y| ≤ 2*C)
    (hadd1 : ∀ k z x n y, |F (k+1) (z,x) n y-F k x n y| ≤ C)
    (hrep2 : ∀ k x n (i : Fin n) y z, |F k x n y-F k x n (replaceRoot n y i z)| ≤ 2*D)
    (hadd2 : ∀ k x n z y, |F k x (n+1) (z,y)-F k x n y| ≤ D) (c : ℝ) :
    (∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ) ∂poissonMeasure r) ≤
      3*C^2*(r : ℝ)+3*D^2*(s : ℝ)+
      (poissonRootAverage μ r (fun k x => poissonRootAverage ν s (F k x))-c)^2 := by
  let G (k : ℕ) (x : RootPath I k) := poissonRootAverage ν s (F k x)
  have hFm (k : ℕ) (x : RootPath I k) (n : ℕ) : Measurable (F k x n) :=
    (hF k n).comp (measurable_const.prodMk measurable_id)
  have hGm (k : ℕ) : Measurable (G k) := measurable_poissonRootAverage ν s (hF k)
  have hGB (k : ℕ) (x : RootPath I k) : |G k x| ≤ B+C*k+D*(s : ℝ) :=
    poissonRootAverage_bound ν s (hB k x)
  have hGr (k : ℕ) (i : Fin k) (x : RootPath I k) (z : I) :
      |G k x-G k (replaceRoot k x i z)| ≤ 2*C :=
    poissonRootAverage_stability ν s (hFm k x) (hFm k (replaceRoot k x i z))
      (hB k x) (hB k (replaceRoot k x i z)) (hrep1 k i x z)
  have hGa (k : ℕ) (z : I) (x : RootPath I k) : |G (k+1) (z,x)-G k x| ≤ C := by
    apply poissonRootAverage_stability ν s (A := B+C*(k+1)) (B := D)
      (hFm (k+1) (z,x)) (hFm k x)
    · simpa using hB (k+1) (z,x)
    · intro n y
      have h := hB k x n y
      have hk : (k : ℝ) ≤ k+1 := le_add_of_nonneg_right zero_le_one
      nlinarith
    · exact hadd1 k z x
  have houter := poisson_root_second_moment μ r hGm hGB hC hGr hGa c
  have hins (k : ℕ) (x : RootPath I k) :=
    poisson_root_second_moment ν s (hFm k x) (hB k x) hD (hrep2 k x) (hadd2 k x) c
  have hsqi (k : ℕ) : Integrable (fun x => (G k x-c)^2) (rootLaw k (fun _ => μ)) :=
    ((bounded_memLp (hGm k) (hGB k) 2).sub (memLp_const c)).integrable_sq
  have hstep (k : ℕ) :
      (∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2 ∂rootLaw n (fun _ => ν)
        ∂poissonMeasure s ∂rootLaw k (fun _ => μ)) ≤
      ((2*D)^2/2+D^2)*(s : ℝ) + ∫ x, (G k x-c)^2 ∂rootLaw k (fun _ => μ) := by
    have h := integral_mono_of_nonneg (μ := rootLaw k (fun _ => μ))
      (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))))
      ((integrable_const (((2*D)^2/2+D^2)*(s : ℝ))).add (hsqi k)) (ae_of_all _ (hins k))
    simp only [Pi.add_apply] at h
    rwa [integral_add (integrable_const _) (hsqi k), integral_const,
      probReal_univ,smul_eq_mul,one_mul] at h
  have hsqint := poisson_integrable_root_squared μ r (A := B+D*(s : ℝ)) (D := C)
    (fun k x => by convert hGB k x using 1; ring) c
  have hnonneg (k : ℕ) : 0 ≤ (∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
  have h := integral_mono_of_nonneg (μ := poissonMeasure r)
    (ae_of_all _ hnonneg)
    ((integrable_const (((2*D)^2/2+D^2)*(s : ℝ))).add hsqint) (ae_of_all _ hstep)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hsqint,integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  dsimp only [G] at houter
  nlinarith

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeterogeneousFullVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- Both random counts and all physical fields contribute to this bound.
The heterogeneous auxiliary priors remain inside the finite power means. -/
theorem full_root_variance
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    let F := fun h k (x : RootPath X k) n (y : RootPath I n) =>
      root T Q m (base h k x) (rootArray n y) factor+c*n
    let G := fun h => poissonRootAverage μ r (fun k x => poissonRootAverage ν s (F h k x))
    (∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, (F h k x n y-(∫ z, G z ∂rootLaw M ξ))^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
        ∂poissonMeasure r ∂rootLaw M ξ) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  dsimp only
  let F := fun h k (x : RootPath X k) n (y : RootPath I n) =>
    root T Q m (base h k x) (rootArray n y) factor+c*n
  let H := fun h k x => poissonRootAverage ν s (F h k x)
  let G := fun h => poissonRootAverage μ r (H h)
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      F z.1.1 k z.1.2 n z.2) :=
    (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (hbmeas k) factor n).add measurable_const
  have hFh (h : RootPath Y M) (k n : ℕ) :
      Measurable (fun z : RootPath X k × RootPath I n => F h k z.1 n z.2) :=
    (hF k n).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hFm (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) :
      Measurable (F h k x n) := (hFh h k n).comp (measurable_const.prodMk measurable_id)
  have hB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |F h k x n y| ≤ B+C*k+(D+|c|)*n := by
    have hh := root_uniform_bound T Q m hm (base h k x) (rootArray n y) factor (hb h k x) hf
    calc
      _ ≤ |root T Q m (base h k x) (rootArray n y) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*k+D*n+|c| *n := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
        exact add_le_add hh le_rfl
      _ = _ := by ring
  have hH (k : ℕ) : Measurable (fun z : RootPath Y M × RootPath X k => H z.1 k z.2) :=
    measurable_poissonRootAverage ν s (hF k)
  have hG : Measurable G := measurable_poissonRootAverage μ r hH
  have hHB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) :
      |H h k x| ≤ B+C*k+(D+|c|)*(s:ℝ) := poissonRootAverage_bound ν s (hB h k x)
  have hGB (h : RootPath Y M) : |G h| ≤ (B+(D+|c|)*(s:ℝ))+C*r := by
    apply poissonRootAverage_bound μ r
    intro k x
    convert hHB h k x using 1 <;> first | rfl | ring
  have hHE (j : Fin M) (h : RootPath Y M) (z : Y) (k : ℕ) (x : RootPath X k) :
      |H h k x-H (replaceRoot M h j z) k x| ≤ E j := by
    apply poissonRootAverage_stability ν s (hFm h k x) (hFm (replaceRoot M h j z) k x)
      (hB h k x) (hB (replaceRoot M h j z) k x)
    intro n y
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hfield j h z k x)
  have hGE (j : Fin M) (h : RootPath Y M) (z : Y) : |G h-G (replaceRoot M h j z)| ≤ E j := by
    apply poissonRootAverage_stability μ r (A := B+(D+|c|)*(s:ℝ)) (B := C)
      (fun k => (hH k).comp (measurable_const.prodMk measurable_id))
      (fun k => (hH k).comp (measurable_const.prodMk measurable_id))
    · intro k x; simpa only [add_right_comm, Function.comp_apply, id_eq] using hHB h k x
    · intro k x; simpa only [add_right_comm, Function.comp_apply, id_eq] using hHB (replaceRoot M h j z) k x
    · exact hHE j h z
  have hv := root_variance_bound M ξ hG hGB E hGE
  have hrep1 (h : RootPath Y M) (k : ℕ) (j : Fin k) (x : RootPath X k) (z : X)
      (n : ℕ) (y : RootPath I n) :
      |F h k x n y-F h k (replaceRoot k x j z) n y| ≤ 2*C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hrep h k j x z)
  have hadd1 (h : RootPath Y M) (k : ℕ) (z : X) (x : RootPath X k)
      (n : ℕ) (y : RootPath I n) : |F h (k+1) (z,x) n y-F h k x n y| ≤ C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hadd h k z x)
  have hrep2 (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ)
      (j : Fin n) (y : RootPath I n) (z : I) :
      |F h k x n y-F h k x n (replaceRoot n y j z)| ≤ 2*(D+|c|) := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub,rootArray_replace,abs_sub_comm]
    exact (root_update_bound T Q m hm _ _ j z factor hf).trans (by linarith [abs_nonneg c])
  have hadd2 (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ)
      (z : I) (y : RootPath I n) : |F h k x (n+1) (z,y)-F h k x n y| ≤ D+|c| := by
    change |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor+c*(n+1:ℕ)-
      (root T Q m (base h k x) (rootArray n y) factor+c*n)| ≤ _
    rw [Nat.cast_add,Nat.cast_one]
    calc
      _ = |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor-
        root T Q m (base h k x) (rootArray n y) factor+c| := by congr 1; ring
      _ ≤ |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor-
        root T Q m (base h k x) (rootArray n y) factor|+|c| := abs_add_le _ _
      _ ≤ D+|c| := add_le_add (root_cons_bound T Q m hm _ _ z factor (hf z)) le_rfl
  have hstep (h : RootPath Y M) := two_poisson_roots_second_moment μ ν r s hC
    (add_nonneg hD (abs_nonneg c)) (hFh h) (hB h) (hrep1 h) (hadd1 h) (hrep2 h) (hadd2 h)
    (∫ z, G z ∂rootLaw M ξ)
  have hi : Integrable (fun h => (G h-∫ z, G z ∂rootLaw M ξ)^2) (rootLaw M ξ) :=
    ((bounded_memLp hG hGB 2).sub (memLp_const (∫ z, G z ∂rootLaw M ξ))).integrable_sq
  have hnn (h : RootPath Y M) : 0 ≤ (∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y,
      (F h k x n y-∫ z, G z ∂rootLaw M ξ)^2 ∂rootLaw n (fun _ => ν)
      ∂poissonMeasure s ∂rootLaw k (fun _ => μ) ∂poissonMeasure r) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ =>
      integral_nonneg (fun _ => sq_nonneg _))))
  have hh := integral_mono_of_nonneg (μ := rootLaw M ξ) (ae_of_all _ hnn)
    ((integrable_const (3*C^2*(r:ℝ)+3*(D+|c|)^2*(s:ℝ))).add hi) (ae_of_all _ hstep)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hi,integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have heq : (∫ h, (G h-∫ z, G z ∂rootLaw M ξ)^2 ∂rootLaw M ξ) =
      variance G (rootLaw M ξ) := (variance_eq_integral hG.aemeasurable).symm
  change _ ≤ _
  exact hh.trans (add_le_add le_rfl (heq.le.trans hv))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

/-- Quadratic envelopes allow both the pressure and its square to be passed
through the two independent compound laws, without any count cut-off. -/
theorem fullRoot_integrable_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (packRoot F) (fullRootLaw ξ μ ν r s) := by
  have hk := (((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := (((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : Integrable (fun z : FullRootState Y X I M => B+C*(z.2.1.1:ℝ)^2+D*(z.2.2.1:ℝ)^2)
      (fullRootLaw ξ μ ν r s) := (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))


theorem twoCompound_integrable_quadratic
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2))
    {B C D : ℝ} (hb : ∀ k x n y, |F k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2)
      ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)
  have he : Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      B+C*(z.1.1:ℝ)^2+D*(z.2.1:ℝ)^2) ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) :=
    (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' hF.aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using hb z.1.1 z.1.2 z.2.1 z.2.2))

/-- Exact Fubini identity for the full root law, with all count-dependent
root spaces and all physical fields retained. -/
theorem integral_fullRootLaw_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, F h k x n y
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hm := measurable_packRoot hF
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hF hb)]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  have hhm : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) := hm.comp (measurable_const.prodMk measurable_id)
  have hhi := twoCompound_integrable_quadratic μ ν r s hhm (hb h)
  change (∫ z, F h z.1.1 z.1.2 z.2.1 z.2.2 ∂(compoundRootLaw μ r).prod (compoundRootLaw ν s)) = _
  rw [integral_prod _ hhi]
  have hg (k : ℕ) : Measurable (fun x : RootPath X k =>
      ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s) := by
    have hh : Measurable (fun z : RootPath X k × Sigma (RootPath I) => F h k z.1 z.2.1 z.2.2) :=
      hhm.comp (((measurable_sigmaMk k).comp measurable_fst).prodMk measurable_snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  change (∫ z : Sigma (RootPath X), ∫ w : Sigma (RootPath I),
    F h z.1 z.2 w.1 w.2 ∂compoundRootLaw ν s
      ∂familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))) = _
  rw [integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k x => ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s)
      hg hhi.integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hfm (n : ℕ) : Measurable (F h k x n) :=
    (hF k n).comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  exact integral_familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
    (F h k x) hfm
    (familyLaw_integrable_bound (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
      (F h k x) hfm
      ((integrable_const (B+C*(k:ℝ)^2)).add ((poisson_integrable_count_sq s).const_mul D))
      (hb h k x))

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

open Filter Set
open scoped Topology BigOperators

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularDepth
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_variance_eq
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*k+D*n) :
    variance (packRoot F) (fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y,
        (F h k x n y-(∫ h', ∫ k' : ℕ, ∫ x', ∫ n' : ℕ, ∫ y', F h' k' x' n' y'
          ∂rootLaw n' (fun _ => ν) ∂poissonMeasure s ∂rootLaw k' (fun _ => μ)
            ∂poissonMeasure r ∂rootLaw M ξ))^2
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hk (k : ℕ) : C*k ≤ C+C*(k:ℝ)^2 := by
    have h : (k:ℝ) ≤ 1+(k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-(1:ℝ)/2)]
    nlinarith [mul_le_mul_of_nonneg_left h hC]
  have hn (n : ℕ) : D*n ≤ D+D*(n:ℝ)^2 := by
    have h : (n:ℝ) ≤ 1+(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-(1:ℝ)/2)]
    nlinarith [mul_le_mul_of_nonneg_left h hD]
  have hbq h k x n y : |F h k x n y| ≤ (B+C+D)+C*(k:ℝ)^2+D*(n:ℝ)^2 := by
    linarith [hb h k x n y,hk k,hn n]
  have he := integral_fullRootLaw_quadratic ξ μ ν r s hF hbq
  let center := ∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s
  have hsq h k x n y : |(F h k x n y-center)^2| ≤
      3*(|B|+|center|)^2+3*C^2*(k:ℝ)^2+3*D^2*(n:ℝ)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hbd : |F h k x n y-center| ≤ (|B|+|center|)+C*k+D*n := by
      have hh := abs_sub (F h k x n y) center
      linarith [hb h k x n y,le_abs_self B]
    have ha := abs_nonneg (F h k x n y-center)
    have hh : (F h k x n y-center)^2 ≤ ((|B|+|center|)+C*k+D*n)^2 := by
      nlinarith [sq_abs (F h k x n y-center)]
    nlinarith [sq_nonneg ((|B|+|center|)-C*k),sq_nonneg ((|B|+|center|)-D*n),
      sq_nonneg (C*k-D*n)]
  rw [variance_eq_integral (measurable_packRoot hF).aemeasurable]
  change (∫ z, packRoot (fun h k x n y => (F h k x n y-center)^2) z ∂fullRootLaw ξ μ ν r s) = _
  rw [integral_fullRootLaw_quadratic ξ μ ν r s
    (fun k n => ((hF k n).sub measurable_const).pow_const 2) hsq]
  dsimp only [center]
  rw [he]

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualRootVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The concentration estimate under one genuine product probability measure,
with independent physical fields and both Poisson reservoirs. -/
theorem variance_actual_root_sat_oai
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    variance (packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y) factor+c*n))
      (fullRootLaw ξ μ ν r s) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      root T Q m (base z.1.1 k z.1.2) (rootArray n z.2) factor+c*n) :=
    (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (hbmeas k) factor n).add measurable_const
  have hB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |root T Q m (base h k x) (rootArray n y) factor+c*n| ≤ B+C*k+(D+|c|)*n := by
    have hh := root_uniform_bound T Q m hm (base h k x) (rootArray n y) factor (hb h k x) hf
    calc
      _ ≤ |root T Q m (base h k x) (rootArray n y) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*k+D*n+|c| *n := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
        exact add_le_add hh le_rfl
      _ = _ := by ring
  rw [fullRoot_variance_eq ξ μ ν r s hF hC (add_nonneg hD (abs_nonneg c)) hB]
  exact full_root_variance μ ν ξ r s T Q m hm base hbmeas factor hC hD hb hf hrep hadd E hfield c

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root_sat_oai := @OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root_sat_oai
