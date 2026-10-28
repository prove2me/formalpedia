-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:14.508104+00:00
-- url     : https://prove2.me/submissions/72c7bdf8-575e-48ad-9b9b-5ce1d62d4a35

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_averagedEnergyRoot_old_new_compare_sat

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

/-- Exact insertion identity for a single finite backward step. -/
theorem logMean_insertion {m : ℝ} (f a : Ω → ℝ) :
    P.logMean m (fun x => f x + a x) - P.logMean m f =
      (P.tilt m f).logMean m a := by
  have hmom : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  rw [logMean, logMean, logMean, hmom,
    Real.log_div (ne_of_gt (P.expMoment_pos _ _)) (ne_of_gt (P.expMoment_pos _ _)),
    sub_div]

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


theorem insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    backwardLog n T m (fun x => f x + a x) - backwardLog n T m f =
      backwardLog n (tilt n T m f) m a := by
  induction n with
  | zero => simp only [backwardLog]; ring
  | succ n ih =>
    let F := fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y))
    let A := fun x => backwardLog n
      (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
      (fun j => m j.succ) (fun y => a (x,y))
    have hc : (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y) + a (x,y))) = (fun x => F x + A x) := by
      funext x
      have hi := ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ - F x = A x at hi
      linarith
    change T.1.logMean (m 0) _ - T.1.logMean (m 0) F =
      (T.1.tilt (m 0) F).logMean (m 0) A
    rw [hc]
    exact T.1.logMean_insertion F A



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

/-- Pointwise bounds survive every backward step, uniformly in depth. -/
theorem backwardLog_bound (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f : FinitePath Ω n → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) : |backwardLog n T m f| ≤ c := by
  have h := backwardLog_stability n T m hm (g := fun _ => 0)
    (fun x => by simpa only [sub_zero] using hf x)
  rwa [backwardLog_const n T m (fun i => ne_of_gt (hm i)), sub_zero] at h

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonMoments
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

/-- A bounded measurable score belongs to every finite Lp space. -/
theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ (fun point => by simpa only [Real.norm_eq_abs] using hB point)

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
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

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

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

theorem familyPoisson_count_integrable :
    Integrable (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) := by
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (poisson_integrable_count r)
  intro n _
  simp

theorem familyPoisson_count_mean :
    (∫ z : Sigma X, (z.1 : ℝ) ∂familyLaw (poissonMeasure r) ν) = (r : ℝ) := by
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (familyPoisson_count_integrable ν r)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_mean]

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

variable {k L : ℕ}

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
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L : ℕ}

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFunDual_iid_sum (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (L : StrongDual ℝ E) :
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L =
      charFunDual μ L ^ n := by
  rw [charFunDual_apply,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [map_sum,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun x : E => Complex.exp ((L x : ℂ)*Complex.I))]
  simp only [charFunDual_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma charFunDual_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ E) :
    charFunDual (compoundPoisson r μ) L = Complex.exp ((r:ℂ)*(charFunDual μ L-1)) := by
  have hi : Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) (compoundPoisson r μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂compoundPoisson r μ) = _
  rw [compoundPoisson,integral_sum_measure hi]
  have hw (n : ℕ) : 0 ≤ Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial := by positivity
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (hw _)]
  change (∑' n : ℕ, (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L) = _
  simp_rw [charFunDual_iid_sum,Complex.real_smul]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFunDual μ L)).mul_left
    (Complex.exp (-(r:ℂ)))
  have he : (fun n : ℕ => ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial:ℝ):ℂ)*charFunDual μ L^n) =
      (fun n : ℕ => Complex.exp (-(r:ℂ))*(((r:ℂ)*charFunDual μ L)^n/n.factorial)) := by
    funext n
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
      Complex.ofReal_exp,Complex.ofReal_neg,mul_pow]
    ring
  rw [he,hh.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  congr 1
  ring
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

theorem extractionProbe_pos (j : ℕ) : 0 < extractionProbe j := by
  unfold extractionProbe
  positivity

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundSuperposition
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Set

lemma extractionProbe_le_quarter (j : ℕ) : extractionProbe j ≤ 1/4 := by
  unfold extractionProbe
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

lemma extractionProbe_abs_le_quarter (j : ℕ) : |extractionProbe j| ≤ 1/4 := by
  rw [abs_of_pos (extractionProbe_pos j)]
  exact extractionProbe_le_quarter j

lemma probeLow_pos (j : ℕ) : 0 < probeLow j := pow_pos (extractionProbe_pos j) _
lemma probeLow_lt_high (j : ℕ) : probeLow j < probeHigh j := by
  have := probeLow_pos j
  unfold probeHigh
  linarith
lemma probeHigh_lt_quarter (j : ℕ) : probeHigh j < 1/4 := by
  have hp : probeLow j ≤ (1/4:ℝ)^4 := by
    apply (pow_le_pow_left₀ (extractionProbe_pos j).le (extractionProbe_le_quarter j) (j+4)).trans
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold probeHigh
  nlinarith

lemma probe_interval_quarter (j : ℕ) :
    Icc (probeLow j) (probeHigh j) ⊆ Icc (-(1:ℝ)/4) (1/4) := by
  intro u hu
  have := probeLow_pos j
  have := probeHigh_lt_quarter j
  exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

end DilutedSpinGlass
end

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma charFunDual_nnreal_smul (r : ℝ≥0) (μ : Measure E) (L : StrongDual ℝ E) :
    charFunDual ((r:ℝ≥0∞) • μ) L = (r:ℂ)*charFunDual μ L := by
  simp only [charFunDual_apply,integral_smul_measure,ENNReal.coe_toReal,Complex.real_smul]

omit [SecondCountableTopology E] in
lemma charFunDual_add_measure (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L : StrongDual ℝ E) : charFunDual (μ+ν) L = charFunDual μ L+charFunDual ν L := by
  have h (ξ : Measure E) [IsFiniteMeasure ξ] :
      Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) ξ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  exact integral_add_measure (h μ) (h ν)

/-- Superposition of marked Poisson sums follows solely from equality of
 the finite intensity measures. No independence of coordinates of a mark is needed. -/
lemma compoundPoisson_superposition [CompleteSpace E] (s t : ℝ≥0)
    (μ ν τ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (h : ((s+t:ℝ≥0):ℝ≥0∞) • μ = (s:ℝ≥0∞) • ν+(t:ℝ≥0∞) • τ) :
    compoundPoisson (s+t) μ = compoundPoisson s ν ∗ compoundPoisson t τ := by
  apply Measure.ext_of_charFunDual
  funext L
  let : IsFiniteMeasure ((s:ℝ≥0∞) • ν) := inferInstanceAs (IsFiniteMeasure (s • ν))
  let : IsFiniteMeasure ((t:ℝ≥0∞) • τ) := inferInstanceAs (IsFiniteMeasure (t • τ))
  have hh := congrArg (fun ξ : Measure E => charFunDual ξ L) h
  simp only [charFunDual_add_measure,charFunDual_nnreal_smul] at hh
  rw [charFunDual_conv,charFunDual_compoundPoisson,charFunDual_compoundPoisson,
    charFunDual_compoundPoisson,← Complex.exp_add]
  congr 1
  push_cast at hh ⊢
  linear_combination hh

lemma compoundPoisson_add [CompleteSpace E] (s t : ℝ≥0)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    compoundPoisson (s+t) μ = compoundPoisson s μ ∗ compoundPoisson t μ := by
  apply compoundPoisson_superposition
  simp only [ENNReal.coe_add,add_smul]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

end FiniteLaw

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniformIndexCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

theorem abs_spin (s : Spin) : |spin s| = 1 := by
  cases s <;> norm_num [spin]

end DilutedSpinGlass.PhysicalRoot
end

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

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma clipReal_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipReal C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clipSample_bound {p : ℕ} {C : ℝ} (hC : 0 ≤ C) (z : InteractionSample p) (σ) :
    |(clipSample C z).1 σ| ≤ C := clipReal_bound hC _

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set


lemma boundParameter_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

lemma abs_log_affine_le {d e t u : ℝ} (hD : |d| ≤ 1) (hE : |e| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) : |Real.log (1+t*d+u*e)| ≤ 1 := by
  have htd : |t*d| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg t,abs_nonneg d]
  have hue : |u*e| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg u,abs_nonneg e]
  have hlo : 1/2 ≤ 1+t*d+u*e := by linarith [(abs_le.mp htd).1,(abs_le.mp hue).1]
  have hhi : 1+t*d+u*e ≤ 3/2 := by linarith [(abs_le.mp htd).2,(abs_le.mp hue).2]
  have hpos : 0 < 1+t*d+u*e := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hinv : (1+t*d+u*e)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    linarith
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [∀ q, Fintype (A q)] in
lemma spinFactor_log_bound
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (u : K×ℕ → ℝ) (i : K×ℕ) (σ : Spin) (y : FinitePath (A i.1) (L+1)) :
    |Real.log (spinFactor D E u i σ y)| ≤ 1 := by
  apply abs_log_affine_le (hD _ _ _) (hE _ _ _) (extractionProbe_abs_le_quarter _)
  have hu := probe_interval_quarter i.2 (boundParameter_mem (probeLow_lt_high i.2).le (u i))
  exact abs_le.mpr ⟨by linarith [hu.1],hu.2⟩

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniversalDictionary
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators


lemma table_bound {L r : ℕ} (g : Table L r) (y : Fin L → Fin r → Bool) :
    |(g.1 y : ℝ)| ≤ 1 := by exact_mod_cast g.2 y
lemma direction_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |direction q σ y| ≤ 1 := by
  rw [direction,abs_mul]
  have hs : |spin σ| = 1 := by cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _
lemma anchor_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |anchor q σ y| ≤ 1 := by
  rw [anchor,abs_mul]
  have hs : |(if q.2.2.2 then spin σ else 1 : ℝ)| = 1 := by
    split <;> cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullCubeConditionalContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma gridExponents_lower (L : ℕ) (j : Fin (L+1)) :
    ((L+1:ℕ):ℝ)⁻¹ ≤ gridExponents L j := by
  change _ ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.le_add_left 1 j.val)

lemma gridExponents_last (L : ℕ) : gridExponents L (Fin.last L) = 1 := by
  simp only [gridExponents,Fin.val_last]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos L)))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRegularSelection
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance fullRegularSelectionDecidableEq_r3f9cfc_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixedPatterns
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    Measurable (rootInsertion T Q m base old V a F) := by
  apply measurable_from_prod_countable_left
  intro v
  apply measurable_packRoot_into (F := fun h k x n y =>
    backwardLog (L+1) (tilt (L+1) (tower (rootArray n y) (L+1) T Q) m
      (logWeight (base h k x) (rootArray n y) old)) m
      (fun w => F (fun i => V (physical (rootArray n y) (L+1) w) (v i))))
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  simp_rw [← insertion]
  apply Measurable.sub
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact ((hb k _).add measurable_const).add measurable_const
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact (hb k _).add measurable_const

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SameInsertionAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (z : FullRootState Y X I M) :
    |sameInsertionAverage T Q m base old V a F z|≤C := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact backwardLog_bound (L+1) _ m hm (fun y => hF _)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalInsertionComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators Topology
variable {p : ℕ}

lemma reservoirInsertion_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |reservoirInsertion M C H N L u a F|≤D := by
  apply abs_integral_le_bound
  intro z
  exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F hF z


end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionStability
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

lemma map_familyLaw_sum {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MeasurableSpace Y] (μ : Measure I) (ν : ∀ i, Measure (X i))
    (f : (i : I) → X i → Y) (hf : ∀ i, Measurable (f i)) :
    Measure.map (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) =
      Measure.sum (fun i => μ {i} • Measure.map (f i) (ν i)) := by
  rw [familyLaw,Measure.comp_eq_sum_of_countable]
  rw [Measure.map_sum (measurable_sigmaUncurry hf).aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul]
  change μ {i} • Measure.map (fun z : Sigma X => f z.1 z.2)
    (Measure.map (Sigma.mk i) (ν i)) = _
  rw [Measure.map_map (measurable_sigmaUncurry hf) (measurable_sigmaMk i)]
  rfl

variable {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma map_iid_energy (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (n : ℕ) :
    Measure.map (fun x : RootPath X n => ∑ i, V (rootArray n x i)) (rootLaw n (fun _ => μ)) =
      Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => Measure.map V μ)) := by
  have hp := (measurePreserving_rootArray μ n).map_eq
  rw [← Measure.pi_map_pi (fun _ : Fin n => hV.aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← hp,Measure.map_map (by fun_prop) (rootArrayEquiv n).measurable]
  congr 1
  funext x
  simp only [Function.comp_apply,rootArrayEquiv_apply]

omit [NormedSpace ℝ E] in
/-- The physical recursive Poisson container has exactly the compound-sum
energy law, including its independent random count. -/
lemma map_compoundRoot_energy (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) :
    Measure.map (fun z : Sigma (RootPath X) => ∑ i, V (rootArray z.1 z.2 i)) (compoundRootLaw μ r) =
      compoundPoisson r (Measure.map V μ) := by
  rw [compoundRootLaw,map_familyLaw_sum _ _ (fun n x => ∑ i,V (rootArray n x i)) (fun n => by
    simpa only [rootArrayEquiv_apply] using
      (show Measurable (fun x : RootPath X n => ∑ i,V (rootArrayEquiv (X := X) n x i)) by fun_prop))]
  simp only [poissonMeasure_singleton,map_iid_energy μ V hV,compoundPoisson]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundMoment
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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma iid_energy_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (n : ℕ) :
    Integrable id (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) := by
  rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  change Integrable (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))
  exact integrable_finsetSum _ (fun i _ => integrable_eval (μ := fun _ : Fin n => μ) (i := i) hi)

omit [NormedSpace ℝ E] in
lemma iid_energy_norm_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (n : ℕ) :
    (∫ x, ‖x‖ ∂Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) ≤
      n*(∫ x, ‖x‖ ∂μ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫ x : Fin n → E, ∑ i, ‖x i‖ ∂Measure.pi (fun _ : Fin n => μ) :=
      integral_mono (integrable_finsetSum _ (fun i _ => integrable_eval hi)).norm
        (integrable_finsetSum _ (fun i _ => integrable_comp_eval hi.norm))
        (fun x => norm_sum_le _ _)
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => integrable_comp_eval hi.norm)]
      have he (i : Fin n) : (∫ x : Fin n → E, ‖x i‖ ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x,‖x‖ ∂μ :=
        integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) (by fun_prop)
      simp only [he,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [NormedSpace ℝ E] in
lemma compoundPoisson_integrable_id (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) : Integrable id (compoundPoisson r μ) := by
  unfold compoundPoisson
  apply integrable_sum_measure
  · intro n
    exact (iid_energy_integrable μ hi n).smul_measure ENNReal.ofReal_ne_top
  · have hs := ((hasSum_integral_poissonMeasure (poisson_integrable_count r)).mul_right
      (∫ x, ‖x‖ ∂μ)).summable
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) _ hs
    intro n
    rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
    change (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*_ ≤
      ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*(n:ℝ))*(∫ x,‖x‖ ∂μ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (iid_energy_norm_le μ hi n) (by positivity)

omit [NormedSpace ℝ E] in
lemma compoundPoisson_norm_le (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) :
    (∫ x, ‖x‖ ∂compoundPoisson r μ) ≤ r*(∫ x, ‖x‖ ∂μ) := by
  have hc : Integrable (fun x : E => ‖x‖) (compoundPoisson r μ) :=
    (compoundPoisson_integrable_id r μ hi).norm
  rw [compoundPoisson,integral_sum_measure hc]
  have hs := (hasSum_integral_poissonMeasure (poisson_integrable_count r)).mul_right (∫ x,‖x‖ ∂μ)
  rw [poisson_mean] at hs
  rw [← hs.tsum_eq]
  apply Summable.tsum_le_tsum
  · intro n
    rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
    change (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*_ ≤
      ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*(n:ℝ))*(∫ x,‖x‖ ∂μ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (iid_energy_norm_le μ hi n) (by positivity)
  · exact (hasSum_integral_measure hc).summable
  · exact hs.summable

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundCoupling
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [NormedSpace ℝ E] [SecondCountableTopology E] in
lemma integrable_lipschitz_of_id (μ : Measure E) [IsFiniteMeasure μ]
    (hi : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) : Integrable f μ := by
  apply ((hi.norm.const_mul (C:ℝ)).add (integrable_const |f 0|)).mono' hf.continuous.measurable.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hh := hf.norm_sub_le x 0
  simp only [Real.norm_eq_abs,sub_zero] at hh
  calc
    |f x| = |(f x-f 0)+f 0| := by rw [sub_add_cancel]
    _ ≤ |f x-f 0|+|f 0| := abs_add_le _ _
    _ ≤ (C:ℝ)*‖x‖+|f 0| := by linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_id_conv (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) : Integrable id (μ∗ν) := by
  rw [Measure.conv,integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma lipschitz_conv_add_bound (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    |(∫ x, f x ∂(μ∗ν))-(∫ x, f x ∂μ)| ≤ C*(∫ y,‖y‖ ∂ν) := by
  have hfi := integrable_lipschitz_of_id μ hμ hf
  have hfc := integrable_lipschitz_of_id (μ∗ν) (integrable_id_conv μ ν hμ hν) hf
  have hfp : Integrable (fun z : E×E => f (z.1+z.2)) (μ.prod ν) := by
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable (by fun_prop)).mp hfc
  rw [integral_conv hfc,← integral_sub hfp.integral_prod_left hfi]
  calc
    _ ≤ ∫ x, |(∫ y, f (x+y) ∂ν)-f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, (C:ℝ)*(∫ y,‖y‖ ∂ν) ∂μ := by
      apply integral_mono (hfp.integral_prod_left.sub hfi).abs (integrable_const _)
      intro x
      have hx : Integrable (fun y => f (x+y)) ν := by
        apply integrable_lipschitz_of_id ν hν
        simpa only [mul_one,Function.comp_def] using hf.comp (isometry_add_left x).lipschitz
      change |(∫ y, f (x+y) ∂ν)-f x|≤_
      have hc : (∫ _y : E, f x ∂ν)=f x := by simp
      rw [← hc,← integral_sub hx (integrable_const _)]
      calc
        _ ≤ ∫ y, |f (x+y)-f x| ∂ν := abs_integral_le_integral_abs
        _ ≤ ∫ y, (C:ℝ)*‖y‖ ∂ν := by
          apply integral_mono (hx.sub (integrable_const _)).abs (hν.norm.const_mul _)
          intro y
          simpa only [add_sub_cancel_left,Real.norm_eq_abs,Pi.sub_apply,id_eq] using hf.norm_sub_le (x+y) x
        _ = _ := integral_const_mul _ _
    _ = _ := by simp

lemma compoundPoisson_rate_add_bound (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson (r+s) μ)-(∫ x, f x ∂compoundPoisson r μ)| ≤
      C*s*(∫ y,‖y‖ ∂μ) := by
  rw [compoundPoisson_add]
  exact (lipschitz_conv_add_bound _ _ (compoundPoisson_integrable_id r μ hμ)
    (compoundPoisson_integrable_id s μ hμ) hf).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (compoundPoisson_norm_le s μ hμ) C.coe_nonneg)

lemma compoundPoisson_rate_bound (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r μ)-(∫ x, f x ∂compoundPoisson s μ)| ≤
      C*|(r:ℝ)-s| *(∫ y,‖y‖ ∂μ) := by
  rcases le_total s r with h|h
  · have hh := compoundPoisson_rate_add_bound s (r-s) μ hμ hf
    rw [add_tsub_cancel_of_le h,NNReal.coe_sub h] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
    exact hh
  · have hh := compoundPoisson_rate_add_bound r (s-r) μ hμ hf
    rw [add_tsub_cancel_of_le h,NNReal.coe_sub h] at hh
    rw [abs_sub_comm (∫ x, f x ∂compoundPoisson r μ),abs_sub_comm (r:ℝ),
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
    exact hh

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal ENNReal BigOperators
variable {Ω I S : Type} [Fintype Ω] [Fintype S]
    {A : I → Type} [∀ i,Fintype (A i)] {L k : ℕ}

lemma root_energy_insertion (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base F : FinitePath Ω L → ℝ)
    (roots : Fin k → I) (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    root T Q m (base+F) roots factor-root T Q m base roots factor =
      backwardLog L (tilt L (tower roots L T Q) m (logWeight base roots factor)) m
        (fun y => F (physical roots L y)) := by
  unfold root
  rw [← insertion]
  congr 2
  funext y
  simp only [logWeight,Pi.add_apply]
  ring

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RandomInsertion
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] {M : ℕ}

lemma integral_fullRootLaw_reordered
    (ξ : Fin M → Measure Y) [∀ i,IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n a,|F h k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h,∫ a : Sigma (RootPath I),∫ x : Sigma (RootPath X),F h x.1 x.2 a.1 a.2
        ∂compoundRootLaw μ r ∂compoundRootLaw ν s ∂rootLaw M ξ := by
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hf hb)]
  apply integral_congr_ae
  filter_upwards [] with h
  have hmf : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) :=
    (measurable_packRoot hf).comp (measurable_const.prodMk measurable_id)
  exact integral_prod_symm _ (twoCompound_integrable_quadratic μ ν r s hmf (hb h))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundPhysicalMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma energyRoot_lipschitz (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) :
    LipschitzWith 1 (energyRoot Q m field factor h a) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply root_base_stability _ Q m hm
  intro y
  simp only [add_sub_add_right_eq_sub]
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (terminalState L y)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkSiteCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ}

lemma measurable_indexedPotential (theta : X → InteractionSample p)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (indexedPotential (N := N) theta) := by
  apply Measurable.of_eval
  intro σ
  apply measurable_from_prod_countable_left
  intro j
  simpa only [indexedPotential] using hθ (fun q => σ (j q))

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountBridgeTools
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]
lemma integral_expect (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ i,Integrable (fun x => f x i) μ) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) := by
  unfold expect
  rw [integral_finsetSum _ (fun i _ => (hf i).const_mul _)]
  simp only [integral_const_mul]
lemma integral_expect_bounded (P : FiniteLaw Ω) (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Ω → ℝ) (hf : ∀ i,Measurable (fun x => f x i)) {B : ℝ}
    (hb : ∀ x i,|f x i|≤B) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) :=
  integral_expect P μ f (fun i => Integrable.of_bound (hf i).aestronglyMeasurable B
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x i)))
end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityInsertionAlgebra
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
open _root_.MeasureTheory

lemma cavitySiteEnergy_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (s : Fin k × Fin (p-1) → Spin) :
    |cavitySiteEnergy θ h s| ≤ |h|+∑ j,‖(θ j).1‖ := by
  change |Real.log ((∑ ε : Spin, Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2)| ≤ _
  have hh (ε : Spin) : |h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)| ≤ |h|+∑ j,‖(θ j).1‖ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul,abs_spin,mul_one]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ j).1 (appendSpin (fun l => s (j,l)) ε)))
  -- This is the logarithm of the uniform two-spin exponential moment.
  have hb := (FiniteLaw.uniform : FiniteLaw Spin).logMean_stability (show (0:ℝ)<1 by norm_num)
    (g := fun _ => 0) (fun ε => by simpa only [sub_zero] using hh ε)
  simp only [FiniteLaw.logMean_const _ (one_ne_zero), sub_zero] at hb
  simpa only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
    FiniteLaw.uniform,Fintype.card_bool,← Finset.mul_sum,inv_mul_eq_div,Nat.cast_ofNat,← Finset.sum_div] using hb

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PerturbedEnergyMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ} [NeZero N]

lemma integrable_indexedPotential
    (μ : Measure X) [IsProbabilityMeasure μ] (theta : X → InteractionSample p)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ))
    {C : ℝ} (hC : 0≤C) (hθ : ∀ x σ,|(theta x).1 σ|≤C) :
    Integrable id (Measure.map (indexedPotential (N := N) theta) (μ.prod (finiteUniform (Fin p → Fin N)))) := by
  apply (integrable_map_measure measurable_id.aestronglyMeasurable (measurable_indexedPotential theta hθm).aemeasurable).mpr
  apply (integrable_const C).mono' (measurable_indexedPotential theta hθm).aestronglyMeasurable
  exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs, indexedPotential, id_eq] using hθ z.1 (fun l => σ (z.2 l))))

end DilutedSpinGlass.SizeCoupling

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AveragedEnergyRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped BigOperators Topology

namespace UniversalDictionary
open ConcreteReservoir

lemma reservoirInsertionOn_bound {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ)
    {D : ℝ} (hF : ∀ s,|F s|≤D) : |reservoirInsertionOn M C H N L u F|≤D :=
  reservoirInsertion_bound M C H N L u (Fintype.card ι) _ (fun _ => hF _)

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace Y] [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma energyRoot_bound (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E : (Fin N → Spin) → ℝ) :
    |energyRoot Q m field factor h a E|≤‖E‖+H*N+D*a.1 := by
  apply root_uniform_bound _ Q m hm _ _ factor _ hf
  intro y
  apply (abs_add_le _ _).trans
  apply add_le_add
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i : Fin N,H := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul,abs_spin,mul_one]; exact hh _)
      _ = H*N := by simp [mul_comm]

lemma measurable_energyRoot (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (field : Y → ℝ) (hh : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ) :
    Measurable (fun z : ((RootPath Y N) × ((Fin N → Spin) → ℝ)) × Sigma (RootPath I) =>
      energyRoot Q m field factor z.1.1 z.2 z.1.2) := by
  apply measurable_prodSigma (f := fun (z : (RootPath Y N) × ((Fin N → Spin) → ℝ)) n a => energyRoot Q m field factor z.1 ⟨n,a⟩ z.2)
  intro k
  apply measurable_from_prod_countable_left
  intro a
  apply measurable_root _ Q m _ (rootArray k a) (fun _ => factor) _ (fun _ _ _ => measurable_const)
  intro y
  exact ((measurable_pi_apply _).comp measurable_snd).add
    (Finset.measurable_sum _ (fun i _ => (hh.comp ((measurable_rootArray N i).comp measurable_fst)).mul_const _))

omit [MeasurableSpace Y] in
lemma integrable_energyRoot_marks (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (E : (Fin N → Spin) → ℝ) :
    Integrable (fun a => energyRoot Q m field factor h a E) (compoundRootLaw ν s) := by
  have hc : Integrable (fun a : Sigma (RootPath I) => (a.1:ℝ)) (compoundRootLaw ν s) :=
    familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s
  have hmeas : Measurable (fun a : Sigma (RootPath I) => energyRoot Q m field factor h a E) :=
    measurable_sigmaUncurry (f := fun n a => energyRoot Q m field factor h ⟨n,a⟩ E) (fun n => measurable_of_countable _)
  apply ((integrable_const (‖E‖+H*N)).add (hc.const_mul D)).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs,Pi.add_apply] using energyRoot_bound Q m hm field factor hh hf h a E)

omit [MeasurableSpace Y] in
lemma energyRoot_marks_bound (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (E : (Fin N → Spin) → ℝ) :
    |∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s|≤‖E‖+H*N+D*s := by
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E).abs
    ((integrable_const (‖E‖+H*N)).add ((familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s).const_mul D))
    (fun a => energyRoot_bound Q m hm field factor hh hf h a E)).trans_eq
  simp only [Pi.add_apply]
  change (∫ a : Sigma (RootPath I), (‖E‖+H*N)+D*a.1 ∂familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))) = _
  rw [integral_add (integrable_const _) ((familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s).const_mul D),
    integral_const_mul,familyPoisson_count_mean]
  simp

lemma averagedEnergyRoot_lipschitz (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    LipschitzWith 1 (averagedEnergyRoot ξ ν s Q m field factor) := by
  have hmi E : Measurable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) := by
    exact ((measurable_energyRoot Q m field hhm factor).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hi E : Integrable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) (rootLaw N (fun _ => ξ)) :=
    bounded_memLp (hmi E) (fun h => energyRoot_marks_bound ν s Q m hm field factor hh hf h E) 1 |>.integrable le_rfl
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,averagedEnergyRoot]
  rw [← integral_sub (hi E) (hi F)]
  apply abs_integral_le_bound
  intro h
  rw [← integral_sub (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E)
    (integrable_energyRoot_marks ν s Q m hm field factor hh hf h F)]
  apply abs_integral_le_bound
  intro a
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    (energyRoot_lipschitz Q m hm field factor h a).dist_le_mul E F

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalInsertionIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory KernelTower PhysicalRoot ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i,Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootInsertion_eq_difference (T : KernelTower Ω (L+1))
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin) (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) (i : Fin a → Site N) :
    rootInsertion T Q m base old V a F (z,i) =
      root T Q m (fun y => base z.1 z.2.1.1 z.2.1.2 y+F (fun j => V y (i j)))
        (rootArray z.2.2.1 z.2.2.2) old -
      root T Q m (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old := by
  exact (root_energy_insertion T Q m (base z.1 z.2.1.1 z.2.1.2)
    (fun y => F (fun j => V y (i j))) _ old).symm

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionPoissonAlgebra
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

lemma poisson_average_bound (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : |∫ k,f k ∂poissonMeasure ρ|≤B+D*ρ := by
  have hg : Integrable (fun k : ℕ => B+D*k) (poissonMeasure ρ) :=
    (integrable_const _).add ((poisson_integrable_count ρ).const_mul D)
  have hh := norm_integral_le_of_norm_le (f := f) hg (ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs] using h k))
  simpa only [Real.norm_eq_abs,integral_add (integrable_const _) ((poisson_integrable_count ρ).const_mul D),
    integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,poisson_mean] using hh

lemma poisson_average_integrable (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : Integrable f (poissonMeasure ρ) := by
  apply ((integrable_const B).add ((poisson_integrable_count ρ).const_mul D)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_apply] using h k)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AveragedRootBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma averagedEnergyRoot_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    |averagedEnergyRoot ξ ν s Q m field factor E|≤‖E‖+H*N+D*s := by
  have := rootLawProbability N (fun _ => ξ)
  exact abs_integral_le_bound (fun h => energyRoot_marks_bound ν s Q m hm field factor hh hf h E)

lemma cavitySiteEnergy_norm_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (j : Fin k×Fin (p-1) → Fin N) (E : (Fin N → Spin) → ℝ)
    {C H : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hθ : ∀ a,‖(θ a).1‖≤C) (hh : |h|≤H) :
    ‖(fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a)))‖≤‖E‖+H+C*k := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro σ
  rw [Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ ‖E‖+(|h|+∑ a,‖(θ a).1‖) := add_le_add (norm_le_pi_norm E σ) (cavitySiteEnergy_bound θ h _)
    _ ≤ ‖E‖+(H+∑ _a : Fin k,C) := add_le_add_right (add_le_add hh (Finset.sum_le_sum (fun a _ => hθ a))) _
    _ = _ := by simp [mul_comm,add_assoc]

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavitySeparable
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N k p : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_cavityArrayEnergy (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (E : (Fin N → Spin) → ℝ) (j : Fin k → Fin (p-1) → Fin N) :
    Measurable (cavityArrayEnergy theta field E j) := by
  apply Measurable.of_eval
  intro σ
  unfold cavityArrayEnergy cavitySiteEnergy
  apply measurable_const.add
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro ε _
  apply Measurable.exp
  apply ((hh.comp measurable_snd).mul_const _).add
  exact Finset.measurable_sum _ (fun a _ => (hθ _).comp ((measurable_pi_apply a).comp measurable_fst))

omit [MeasurableSpace X] in
lemma cavityArrayValue_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    {H C B : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hθ : ∀ x,‖(theta x).1‖ ≤ C) (hh : ∀ y,|field y| ≤ H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : ∀ v,|F v| ≤ ‖v‖+B)
    (E : (Fin N → Spin) → ℝ) (z : Fin k → X) :
    |cavityArrayValue ξ theta field F E z| ≤ ‖E‖+H+C*k+B := by
  apply FiniteLaw.abs_expect_le
  intro j
  apply abs_integral_le_bound
  intro h
  apply (hF _).trans
  apply add_le_add _ le_rfl
  exact PhysicalRoot.cavitySiteEnergy_norm_bound (fun a => theta (z a)) (field h)
    (fun a => j a.1 a.2) E hH hC (fun _ => hθ _) (hh h)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundSample
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]

lemma measurable_compound_sample (V : X → E) (hV : Measurable V) :
    Measurable (fun z : Sigma (RootPath X) => ∑ i,V (rootArray z.1 z.2 i)) := by
  apply measurable_sigmaUncurry (f := fun n z => ∑ i,V (rootArray n z i))
  intro n
  apply Finset.measurable_sum
  intro i _
  exact hV.comp (measurable_rootArray n i)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_EnergyInsertionMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma integrable_energyRoot_field_mean (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    Integrable (fun h => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s)
      (rootLaw N (fun _ => ξ)) := by
  have hmi : Measurable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) := by
    exact ((measurable_energyRoot Q m field hfield factor).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  exact Integrable.of_bound hmi.aestronglyMeasurable (‖E‖+H*N+D*s)
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using energyRoot_marks_bound ν s Q m hm field factor hh hf h E))

lemma averagedEnergyRoot_increment (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E J : (Fin N → Spin) → ℝ) :
    averagedEnergyRoot ξ ν s Q m field factor (E+J)-averagedEnergyRoot ξ ν s Q m field factor E=
      ∫ h,∫ a,energyRoot Q m field factor h a (E+J)-energyRoot Q m field factor h a E
        ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
  unfold averagedEnergyRoot
  rw [← integral_sub (integrable_energyRoot_field_mean ξ ν s Q m hm field hfield factor hh hf (E+J))
    (integrable_energyRoot_field_mean ξ ν s Q m hm field hfield factor hh hf E)]
  apply integral_congr_ae
  filter_upwards [] with h
  exact (integral_sub (integrable_energyRoot_marks ν s Q m hm field factor hh hf h (E+J))
    (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E)).symm

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma energyRoot_increment_bound
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E J : (Fin N → Spin) → ℝ) :
    |energyRoot Q m field factor h a (E+J)-energyRoot Q m field factor h a E|≤‖J‖ := by
  simpa only [dist_eq_norm,Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul] using
    (energyRoot_lipschitz Q m hm field factor h a).dist_le_mul (E+J) E

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_OneNewLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_newPotential (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (newPotential (N := N) theta) := by
  apply measurable_from_prod_countable_left
  intro i
  exact Measurable.of_eval (fun σ => by
    change Measurable (fun c => (theta c).1 (appendSpin (fun b => σ (i b).succ) (σ 0)))
    exact hθ _)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRootIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma measurable_reorder_increment {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Add γ] [MeasurableAdd₂ γ]
    (F : (α × γ) × β → ℝ) (hF : Measurable F) (J : γ) :
    Measurable (fun z : (α × β) × γ => F ((z.1.1,z.2+J),z.1.2)-F ((z.1.1,z.2),z.1.2)) := by
  exact (hF.comp ((measurable_fst.fst.prodMk (measurable_snd.add_const J)).prodMk measurable_fst.snd)).sub
    (hF.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))

lemma measurable_energyRoot_increment
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (J : (Fin N → Spin) → ℝ) :
    Measurable (fun z : (RootPath Y N × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
      energyRoot Q m field factor z.1.1 z.1.2 (z.2+J)-energyRoot Q m field factor z.1.1 z.1.2 z.2) :=
  measurable_reorder_increment
    (fun z : (RootPath Y N × ((Fin N → Spin) → ℝ)) × Sigma (RootPath I) =>
      energyRoot Q m field factor z.1.1 z.2 z.1.2)
    (measurable_energyRoot Q m field hfield factor) J

lemma fullRoot_energy_increment
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (J : (Fin N → Spin) → ℝ) :
    (∫ z : FullRootState Y X I N,
      energyRoot Q m field factor z.1 z.2.2 ((∑ i,V (rootArray z.2.1.1 z.2.1.2 i))+J)-
        energyRoot Q m field factor z.1 z.2.2 (∑ i,V (rootArray z.2.1.1 z.2.1.2 i))
       ∂fullRootLaw (fun _ => ξ) μ ν r s) =
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor (E+J)-
        averagedEnergyRoot ξ ν s Q m field factor E ∂compoundPoisson r (Measure.map V μ) := by
  let κ := compoundPoisson r (Measure.map V μ)
  let : IsProbabilityMeasure (Measure.map V μ) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let G := fun z : (RootPath Y N × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
    energyRoot Q m field factor z.1.1 z.1.2 (z.2+J)-energyRoot Q m field factor z.1.1 z.1.2 z.2
  have hmG : Measurable G := measurable_energyRoot_increment Q m field hfield factor J
  have hbG (z) : |G z|≤‖J‖ := energyRoot_increment_bound Q m hm field factor z.1.1 z.1.2 z.2 J
  have hiG : Integrable G (((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s)).prod κ) :=
    Integrable.of_bound hmG.aestronglyMeasurable _ (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbG z))
  let F := fun (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) =>
    G ((h,⟨n,a⟩),∑ i,V (rootArray k x i))
  have hFm k n : Measurable (fun z : (RootPath Y N × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2) := by
    apply hmG.comp
    apply Measurable.prodMk
    · exact measurable_fst.fst.prodMk ((measurable_sigmaMk (i := n)).comp measurable_snd)
    · exact Finset.measurable_sum _ (fun i _ => hV.comp ((measurable_rootArray k i).comp measurable_fst.snd))
  have he : (∫ z,packRoot F z ∂fullRootLaw (fun _ => ξ) μ ν r s)=
      ∫ h,∫ a,∫ E,G ((h,a),E) ∂κ ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
    rw [integral_fullRootLaw_reordered (fun _ => ξ) μ ν r s hFm
      (B := ‖J‖) (C := 0) (D := 0) (fun h k x n a => by simpa only [zero_mul,add_zero] using hbG ((h,⟨n,a⟩),∑ i,V (rootArray k x i)))]
    apply integral_congr_ae
    filter_upwards [] with h
    apply integral_congr_ae
    filter_upwards [] with a
    dsimp only [F,κ]
    rw [← map_compoundRoot_energy μ V hV r]
    have hma : Measurable (fun E : (Fin N → Spin) → ℝ => G ((h,a),E)) :=
      hmG.comp (measurable_const.prodMk measurable_id)
    rw [integral_map (measurable_compound_sample V hV).aemeasurable hma.aestronglyMeasurable]
  change (∫ z,packRoot F z ∂fullRootLaw (fun _ => ξ) μ ν r s)=_
  rw [he,← integral_prod _ hiG.integral_prod_left,integral_integral_swap hiG]
  apply integral_congr_ae
  filter_upwards [hiG.prod_left_ae] with E hE
  rw [integral_prod _ hE,← averagedEnergyRoot_increment ξ ν s Q m hm field hfield factor hh hf E J]

end DilutedSpinGlass.PhysicalRoot

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {N p k : ℕ} [NeZero N]

lemma measurable_cavityArrayValue_joint (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) :
    Measurable (fun z : ((Fin N → Spin) → ℝ)×(Fin k → X) =>
      cavityArrayValue ξ theta field F z.1 z.2) := by
  apply FiniteLaw.measurable_expect
  intro j
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun z : (((Fin N → Spin) → ℝ)×(Fin k → X))×Y =>
    F (cavityArrayEnergy theta field z.1.1 j (z.1.2,z.2)))
  apply Measurable.stronglyMeasurable
  apply hF.measurable.comp
  apply Measurable.of_eval
  intro σ
  change Measurable (fun z : (((Fin N → Spin) → ℝ)×(Fin k → X))×Y =>
    z.1.1 σ+cavitySiteEnergy (fun a => theta (z.1.2 a)) (field z.2) (fun a => σ (j a.1 a.2)))
  apply ((measurable_pi_apply σ).comp (measurable_fst.comp measurable_fst)).add
  unfold cavitySiteEnergy
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro ε _
  apply Measurable.exp
  apply ((hh.comp measurable_snd).mul_const _).add
  exact Finset.measurable_sum _ (fun a _ => (hθ _).comp
    ((measurable_pi_apply a).comp (measurable_snd.comp measurable_fst)))

lemma measurable_cavityPoissonValue (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (r : ℝ≥0) :
    Measurable (cavityPoissonValue μ ξ theta field F r) := by
  unfold cavityPoissonValue
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun z : ((Fin N → Spin) → ℝ)×ℕ =>
    ∫ x : Fin z.2 → X,cavityArrayValue ξ theta field F z.1 x ∂Measure.pi (fun _ : Fin z.2 => μ))
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_left
  intro k
  exact (measurable_cavityArrayValue_joint (k := k) ξ theta field hθ hh hF).stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : Fin k => μ)) |>.measurable

lemma cavityPoissonValue_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    {H C B : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : ∀ E,|F E|≤‖E‖+B)
    (r : ℝ≥0) (E : (Fin N → Spin) → ℝ) :
    |cavityPoissonValue μ ξ theta field F r E|≤‖E‖+H+C*r+B := by
  have hb (k : ℕ) : |∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ)|≤‖E‖+H+C*k+B :=
    abs_integral_le_bound (fun z => cavityArrayValue_bound ξ theta field hH hC hθ hh hF E z)
  have h := poisson_average_bound r (fun k : ℕ => ∫ z : Fin k → X,
    cavityArrayValue ξ theta field F E z ∂Measure.pi (fun _ : Fin k => μ))
    (B := ‖E‖+H+B) (D := C) (fun k => (hb k).trans_eq (by ring))
  exact h.trans_eq (by ring)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalCavityPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p : ℕ} [NeZero N]

lemma integrable_cavityPoissonValue
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (θ : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (θ x).1 σ)) (hhm : Measurable field)
    {C H B : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ x,‖(θ x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (hFb : ∀ E,|F E|≤‖E‖+B)
    (r : ℝ≥0) : Integrable (cavityPoissonValue μ ξ θ field F r) ρ := by
  have hb E : |cavityPoissonValue μ ξ θ field F r E|≤‖E‖+(H+C*r+B) := by
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ θ field hH hC hθ hh hFb r E
  exact (hρ.norm.add (integrable_const (H+C*r+B))).mono'
    (measurable_cavityPoissonValue μ ξ θ field hθm hhm hF r).aestronglyMeasurable
    (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hb E))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalInsertionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower ConcreteReservoir
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I] in
lemma rootInsertion_energyRoot
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) (z : FullRootState Y X I N) (i : Fin a → Site N) :
    rootInsertion (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
      (fun h k x y => energy V field h k x (terminalState L y)) factor
      (fun y s => readSpin (terminalState L y) s) a F (z,i) =
    energyRoot Q m field factor z.1 z.2.2
      ((∑ j,V (rootArray z.2.1.1 z.2.1.2 j))+(fun σ => F (fun j => readSpin σ (i j))))-
      energyRoot Q m field factor z.1 z.2.2 (∑ j,V (rootArray z.2.1.1 z.2.1.2 j)) := by
  rw [rootInsertion_eq_difference]
  unfold energyRoot
  apply congrArg₂ (fun x y : ℝ => x-y)
  · congr 1
    funext y
    simp only [energy,Pi.add_apply,Finset.sum_apply]
    ring
  · simp only [energy,Finset.sum_apply]

lemma fullRoot_sameInsertion_energy
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    (∫ z : FullRootState Y X I N,
      sameInsertionAverage (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
        (fun h k x y => energy V field h k x (terminalState L y)) factor
        (fun y i => readSpin (terminalState L y) i) a F z
      ∂fullRootLaw (fun _ => ξ) μ ν r s) =
    (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor (E+(fun σ => F (fun j => readSpin σ (i j))))-
        averagedEnergyRoot ξ ν s Q m field factor E
        ∂compoundPoisson r (Measure.map V μ)) := by
  unfold sameInsertionAverage
  rw [FiniteLaw.integral_expect_bounded (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)) (fullRootLaw (fun _ => ξ) μ ν r s) (B := ‖F‖)]
  · apply FiniteLaw.expect_congr
    intro i
    simp only [rootInsertion_energyRoot]
    exact fullRoot_energy_increment ξ μ ν r s V hV Q m hm field hfield factor hh hf _
  · intro i
    exact (measurable_rootInsertion _ Q m _ factor _
      (fun k _ => measurable_energy V field (fun σ => (measurable_pi_apply σ).comp hV) hfield k _) a F).comp
        (measurable_id.prodMk measurable_const)
  · intro z i
    exact backwardLog_bound (L+1) _ m hm (fun _ => norm_le_pi_norm F _)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirInsertionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p : ℕ}

lemma reservoirInsertion_energy (M : Model p) (C H : ℝ) (hH : 0≤H) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) {D : ℝ}
    (hf : ∀ i y a,|Real.log (dictionaryFactor (observableAt direction N) (observableAt anchor N) u i y a)|≤D)
    (b : ℕ) (F : (Fin b → Spin) → ℝ) :
    reservoirInsertion M C H N L u b F=
      (FiniteLaw.uniform : FiniteLaw (Fin b → Site N)).expect (fun i =>
        ∫ E,averagedEnergyRoot M.field.toMeasure (markLaw (weights L) N) (scoreRate N)
            (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (clipReal H)
            (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
            (E+(fun σ => F (fun j => readSpin σ (i j))))-
          averagedEnergyRoot M.field.toMeasure (markLaw (weights L) N) (scoreRate N)
            (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (clipReal H)
            (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) E
          ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
            (Measure.map (boundedPotential C) (bondLaw M N))) := by
  unfold reservoirInsertion reservoirLaw physicalBase physicalSpin
  exact fullRoot_sameInsertion_energy M.field.toMeasure (bondLaw M N) (markLaw (weights L) N)
    (reservoirRate M.alpha (p-1) N) (scoreRate N) (boundedPotential C)
    (Measurable.of_eval (measurable_boundedPotential C)) _ (gridExponents L)
    (gridExponents_pos L) (clipReal H) (measurable_clipReal H) _
    (fun y => clipReal_bound hH y) hf b F

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirSiteTransport
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirInsertion_energy_positive (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (b : ℕ) (F : (Fin b → Spin) → ℝ) :
    reservoirInsertion M C H N L u b F=
      (FiniteLaw.uniform : FiniteLaw (Fin b → Fin N)).expect (fun i =>
        ∫ E,averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
            (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
            (locatedFactor (spinFactor direction anchor u))
            (E+(fun σ => F (fun j => σ (i j))))-
          averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
            (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
            (locatedFactor (spinFactor direction anchor u)) E
          ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
            (Measure.map (fun z : InteractionSample p × (Fin p → Fin N) =>
              fun σ => clipReal C (z.1.1 (fun j => σ (z.2 j))))
              (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))) := by
  have he := reservoirInsertion_energy M C H hH N L u (D := 1)
    (fun i y a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a) b F
  rw [he]
  change variableSiteInsertion (N := N) M C H u b F (max N 1)=_
  have hmax : max N 1=N := max_eq_left (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  simp only [hmax]
  unfold variableSiteInsertion
  simp only [Fin.is_lt,↓reduceDIte,Fin.eta]
  rfl

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirInsertionOnEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirInsertionOn_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ) :
    reservoirInsertionOn M C H N L u F=
      (FiniteLaw.uniform : FiniteLaw (ι → Fin N)).expect (fun i =>
        ∫ E,reservoirEnergyRoot M H N L u (E+(fun σ => F (fun j => σ (i j))))-
          reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N) := by
  unfold reservoirInsertionOn
  rw [reservoirInsertion_energy_positive M C H hH]
  let e : (Fin (Fintype.card ι) → Fin N) ≃ (ι → Fin N) :=
    Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl (Fin N))
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityAllocatedMean
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertion_integrable (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) (v : E) :
    Integrable (fun E => F (E+v)-F E) ρ := by
  apply Integrable.of_bound (hF.continuous.comp (continuous_id.add continuous_const) |>.sub hF.continuous).aestronglyMeasurable ‖v‖
  exact ae_of_all _ (fun E => by simpa using hF.norm_sub_le (E+v) E)

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertionFunctional_lipschitz (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (energyInsertionFunctional ρ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,energyInsertionFunctional]
  rw [← integral_sub (energyInsertion_integrable ρ hF v) (energyInsertion_integrable ρ hF w)]
  apply abs_integral_le_bound
  intro E
  simpa only [sub_sub_sub_cancel_right,add_sub_add_left_eq_sub,NNReal.coe_one,one_mul,
    Real.norm_eq_abs] using hF.norm_sub_le (E+v) (E+w)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertionFunctional_bound (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) (v : E) :
    |energyInsertionFunctional ρ F v|≤‖v‖ := by
  apply abs_integral_le_bound
  intro E
  simpa only [add_sub_cancel_left,NNReal.coe_one,one_mul,Real.norm_eq_abs] using hF.norm_sub_le (E+v) E

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityInsertionFunctional
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p k : ℕ} [NeZero N]

omit [MeasurableSpace X] in
lemma cavityArray_insertionFunctional (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hhm : Measurable field) {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hh : ∀ y,|field y|≤H)
    (z : Fin k → X) (hz : ∀ a,‖(theta (z a)).1‖≤C) :
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect (fun j =>
      ∫ y,energyInsertionFunctional ρ F
        (fun σ => cavitySiteEnergy (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))) ∂ξ)=
      ∫ E,cavityArrayValue ξ theta field F E z-F E ∂ρ := by
  let V := fun (j : Fin k → Fin (p-1) → Fin N) (y : Y) (σ : Fin N → Spin) =>
    cavitySiteEnergy (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))
  have hVm j : Measurable (V j) := by
    apply Measurable.of_eval
    intro σ
    change Measurable (fun y => cavitySiteEnergy (fun a => theta (z a)) (field y)
      (fun a => σ (j a.1 a.2)))
    unfold cavitySiteEnergy
    apply Measurable.log
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro ε _
    apply Measurable.exp
    exact (hhm.mul_const _).add measurable_const
  have hVb j y : ‖V j y‖≤H+C*k := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro σ
    have hb := cavitySiteEnergy_bound (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))
    have hs : (∑ a : Fin k,‖(theta (z a)).1‖)≤C*k := by
      simpa [mul_comm] using Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin k))) => hz a)
    simpa only [Real.norm_eq_abs] using hb.trans (add_le_add (hh y) hs)
  have hi j : Integrable (fun w : Y×((Fin N → Spin) → ℝ) => F (w.2+V j w.1)-F w.2) (ξ.prod ρ) := by
    apply Integrable.of_bound ((hF.continuous.measurable.comp (measurable_snd.add ((hVm j).comp measurable_fst))).sub
      (hF.continuous.measurable.comp measurable_snd)).aestronglyMeasurable (H+C*k)
    exact ae_of_all _ (fun w => by
      simpa only [Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul,Pi.sub_apply,Pi.add_apply,Function.comp_apply] using
        (hF.norm_sub_le (w.2+V j w.1) w.2).trans (by simpa using hVb j w.1))
  have hj j : (∫ y,energyInsertionFunctional ρ F (V j y) ∂ξ)=
      ∫ E,∫ y,F (E+V j y)-F E ∂ξ ∂ρ := integral_integral_swap (hi j)
  have hsub E j : (∫ y,F (E+V j y)-F E ∂ξ)=(∫ y,F (E+V j y) ∂ξ)-F E := by
    have he : Integrable (fun y => F (E+V j y)-F E) ξ := by
      apply Integrable.of_bound ((hF.continuous.measurable.comp (measurable_const.add (hVm j))).sub measurable_const).aestronglyMeasurable (H+C*k)
      exact ae_of_all _ (fun y => by simpa using (hF.norm_sub_le (E+V j y) E).trans (by simpa using hVb j y))
    have he' : Integrable (fun y => F (E+V j y)) ξ := by
      exact (he.add (integrable_const (F E))).congr (ae_of_all _ (fun y => by simp))
    rw [integral_sub he' (integrable_const _)]; simp
  change (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect
    (fun j => ∫ y,energyInsertionFunctional ρ F (V j y) ∂ξ)=_
  simp_rw [hj]
  rw [← FiniteLaw.integral_expect _ ρ _ (fun j => (hi j).integral_prod_right)]
  apply integral_congr_ae
  filter_upwards [] with E
  simp only [hsub,FiniteLaw.expect_sub,FiniteLaw.expect_const,cavityArrayValue]
  rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundRateAverage
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [CompleteSpace V]

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma integral_add_lipschitz [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {F : E → ℝ} (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (fun x => ∫ y,F (x+y) ∂μ) := by
  have hi x : Integrable (fun y => F (x+y)) μ :=
    integrable_lipschitz_of_id μ hμ (by simpa only [mul_one, Function.comp_def] using hF.comp (isometry_add_left x).lipschitz)
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  rw [← integral_sub (hi x) (hi z)]
  apply abs_integral_le_bound
  intro y
  simpa only [Real.norm_eq_abs,add_sub_add_right_eq_sub,NNReal.coe_one,one_mul] using hF.norm_sub_le (x+y) (z+y)

omit [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V] in
lemma integrated_compound_rate_bound [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (ρ : Measure V) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    {e : V → E} (he : LipschitzWith 1 e) {F : E → ℝ} (hF : LipschitzWith 1 F)
    (r s : ℝ≥0) :
    |(∫ x,∫ y,F (e x+y) ∂compoundPoisson r μ ∂ρ)-
      (∫ x,∫ y,F (e x+y) ∂compoundPoisson s μ ∂ρ)|≤
        |(r:ℝ)-s| * (∫ y,‖y‖ ∂μ) := by
  have hl t : LipschitzWith 1 (fun x => ∫ y,F (e x+y) ∂compoundPoisson t μ) := by
    simpa only [one_mul,Function.comp_def] using
      (integral_add_lipschitz (compoundPoisson t μ) (compoundPoisson_integrable_id t μ hμ) hF).comp he
  rw [← integral_sub (integrable_lipschitz_of_id ρ hρ (hl r)) (integrable_lipschitz_of_id ρ hρ (hl s))]
  apply abs_integral_le_bound
  intro x
  have hx : LipschitzWith 1 (fun y => F (e x+y)) := by
    simpa only [mul_one, Function.comp_def] using hF.comp (isometry_add_left (e x)).lipschitz
  simpa only [NNReal.coe_one,one_mul] using compoundPoisson_rate_bound r s μ hμ hx

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalCavityRate
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p k : ℕ} [NeZero N]

omit [MeasurableSpace X] in
lemma cavityArrayValue_shift [MeasurableSpace X] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hh : ∀ y,|field y|≤H)
    (z : Fin k → X) (hz : ∀ a,‖(theta (z a)).1‖≤C) (E : (Fin N → Spin) → ℝ) :
    cavityArrayValue ξ theta field (fun v => F (E+v)-F E) 0 z=
      cavityArrayValue ξ theta field F E z-F E := by
  have h := cavityArray_insertionFunctional (Measure.dirac E) ξ theta field hhm hF hH hC hh z hz
  have he v : energyInsertionFunctional (Measure.dirac E) F v=F (E+v)-F E := by
    unfold energyInsertionFunctional
    rw [integral_dirac]
  simp only [integral_dirac,he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold cavityArrayValue cavityArrayEnergy
  congr 1
  ext j
  congr 1
  ext y
  congr 2
  ext σ
  simp

lemma cavityArrayValue_gap_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (hh : ∀ y,|field y|≤H) (z : Fin k → X) (E : (Fin N → Spin) → ℝ) :
    |cavityArrayValue ξ theta field F E z-F E|≤H+C*k := by
  rw [← cavityArrayValue_shift ξ theta field hhm hF hH hC hh z (fun a => hθ _) E]
  have hb : ∀ v,|F (E+v)-F E|≤‖v‖+0 := fun v => by
    simpa using hF.norm_sub_le (E+v) E
  simpa using cavityArrayValue_bound ξ theta field hH hC hθ hh hb 0 z

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

omit [NeZero N] in
lemma liftOldEnergy_lipschitz [NeZero N] : LipschitzWith 1 (liftOldEnergy (N := N)) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro σ
  exact norm_le_pi_norm (E-F) (fun i => σ i.succ)

lemma averagedEnergyRoot_cavity_rate_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r t s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) t E ∂ρ)|≤
      C*|(r:ℝ)-t|+4*D*s/(N+1) := by
  let G := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
  let μn := Measure.map (newPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin q → Fin N)))
  have hnM := measurable_newPotential (N := N) theta hθm
  have : IsProbabilityMeasure μn := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hnb (z : X×(Fin q → Fin N)) : ‖newPotential theta z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1))
  have hin : Integrable id μn := by
    apply (integrable_map_measure aestronglyMeasurable_id hnM.aemeasurable).mpr
    exact Integrable.of_bound hnM.aestronglyMeasurable C (ae_of_all _ hnb)
  have hni : (∫ v,‖v‖ ∂μn)≤C := by
    rw [show (∫ v,‖v‖ ∂μn)=∫ z,‖newPotential theta z‖ ∂(μ.prod (finiteUniform (Fin q → Fin N))) from
      integral_map hnM.aemeasurable continuous_norm.aestronglyMeasurable]
    exact (le_abs_self _).trans (abs_integral_le_bound (fun z => by simpa only [abs_of_nonneg (norm_nonneg _)] using hnb z))
  have hGl : LipschitzWith 1 G := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    _ m hm field hhm (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)
  have hrate := (integrated_compound_rate_bound μn hin ρ hρ liftOldEnergy_lipschitz hGl r t).trans
    (mul_le_mul_of_nonneg_left hni (abs_nonneg ((r:ℝ)-t)))
  have hr := averagedEnergyRoot_old_new_compare_sat μ ξ ν ρ hρ r s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  have ht := averagedEnergyRoot_old_new_compare_sat μ ξ ν ρ hρ t s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  dsimp only [G,μn] at hrate
  have h1 := abs_sub_le (∫ E,cavityPoissonValue μ ξ theta field
    (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r μn ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson t μn ∂ρ)
  have h2 := abs_sub_le (∫ E,cavityPoissonValue μ ξ theta field
    (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson t μn ∂ρ)
    (∫ E,cavityPoissonValue μ ξ theta field
      (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) t E ∂ρ)
  dsimp only [G,μn] at h1 h2
  rw [abs_sub_comm] at hr
  exact (h2.trans (add_le_add (h1.trans (add_le_add hr hrate)) ht)).trans_eq (by ring)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityGapFubini
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p : ℕ} [NeZero N]

lemma cavityPoisson_gap_fubini
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (hh : ∀ y,|field y|≤H) (r : ℝ≥0) :
    (∫ k,∫ z : Fin k → X,∫ E,cavityArrayValue ξ theta field F E z-F E ∂ρ
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)=
      ∫ E,cavityPoissonValue μ ξ theta field F r E-F E ∂ρ := by
  let g := fun (k : ℕ) (E : (Fin N → Spin) → ℝ) (z : Fin k → X) =>
    cavityArrayValue ξ theta field F E z-F E
  have hgm k : Measurable (fun w : ((Fin N → Spin) → ℝ)×(Fin k → X) => g k w.1 w.2) :=
    (measurable_cavityArrayValue_joint ξ theta field hθm hhm hF.continuous).sub
      (hF.continuous.measurable.comp measurable_fst)
  have hgb k E z : |g k E z|≤H+C*k :=
    cavityArrayValue_gap_bound ξ theta field hhm hF hH hC hθ hh z E
  have hgi k : Integrable (fun w : ((Fin N → Spin) → ℝ)×(Fin k → X) => g k w.1 w.2)
      (ρ.prod (Measure.pi (fun _ : Fin k => μ))) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable (H+C*k)
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hgb k w.1 w.2))
  have hs k : (∫ z : Fin k → X,∫ E,g k E z ∂ρ ∂Measure.pi (fun _ : Fin k => μ))=
      ∫ E,∫ z : Fin k → X,g k E z ∂Measure.pi (fun _ : Fin k => μ) ∂ρ :=
    (integral_integral_swap (hgi k)).symm
  let f := fun (k : ℕ) (E : (Fin N → Spin) → ℝ) =>
    ∫ z : Fin k → X,g k E z ∂Measure.pi (fun _ : Fin k => μ)
  have hfm : Measurable (fun w : ((Fin N → Spin) → ℝ)×ℕ => f w.2 w.1) := by
    apply measurable_from_prod_countable_left
    intro k
    exact (hgm k).stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : Fin k => μ)) |>.measurable
  have hfb k E : |f k E|≤H+C*k := abs_integral_le_bound (fun z => hgb k E z)
  have hfi : Integrable (fun w : ((Fin N → Spin) → ℝ)×ℕ => f w.2 w.1)
      (ρ.prod (poissonMeasure r)) := by
    apply (((integrable_const H).add ((poisson_integrable_count r).const_mul C)).comp_snd ρ).mono'
      hfm.aestronglyMeasurable
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply] using hfb w.2 w.1)
  change (∫ k,∫ z : Fin k → X,∫ E,g k E z ∂ρ ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)=_
  simp_rw [hs]
  rw [show (∫ k,∫ E,f k E ∂ρ ∂poissonMeasure r)=∫ E,∫ k,f k E ∂poissonMeasure r ∂ρ from
    (integral_integral_swap hfi).symm]
  apply integral_congr_ae
  filter_upwards [] with E
  have hge k : Integrable (g k E) (Measure.pi (fun _ : Fin k => μ)) :=
    Integrable.of_bound (((hgm k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (H+C*k) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hgb k E z))
  have ha k : Integrable (cavityArrayValue ξ theta field F E : (Fin k → X) → ℝ)
      (Measure.pi (fun _ : Fin k => μ)) := by
    exact ((hge k).add (integrable_const (F E))).congr (ae_of_all _ (fun z => by simp [g]))
  have he k : f k E=(∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ))-F E := by
    dsimp only [f,g]
    rw [integral_sub (ha k) (integrable_const _)]; simp
  have hfie : Integrable (fun k => f k E) (poissonMeasure r) := poisson_average_integrable r _ (fun k => hfb k E)
  have hca : Integrable (fun k => ∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ)) (poissonMeasure r) := by
    exact (hfie.add (integrable_const (F E))).congr (ae_of_all _ (fun k => by simp [he k]))
  simp_rw [he]
  rw [integral_sub hca (integrable_const _)]; simp [cavityPoissonValue]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirEnergyBounds
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirEnergyRoot_lipschitz (M : Model p) {H : ℝ} (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) : LipschitzWith 1 (reservoirEnergyRoot M H N L u) :=
  averagedEnergyRoot_lipschitz M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
    _ (gridExponents L) (gridExponents_pos L) (clipReal H) (measurable_clipReal H)
    (locatedFactor (spinFactor direction anchor u)) (fun y => clipReal_bound hH y)
    (fun i _ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a)

lemma reservoirEnergyLaw_eq (M : Model p) (C : ℝ) :
    reservoirEnergyLaw M C N=compoundPoisson (reservoirRate M.alpha (p-1) N)
      (Measure.map (indexedPotential (N := N) (clipSample C))
        (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) := rfl

instance reservoirEnergyLaw_probability (M : Model p) (C : ℝ) :
    IsProbabilityMeasure (reservoirEnergyLaw M C N) := by
  rw [reservoirEnergyLaw_eq]
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) (clipSample C))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma reservoirEnergyLaw_integrable (M : Model p) {C : ℝ} (hC : 0≤C) :
    Integrable id (reservoirEnergyLaw M C N) := by
  rw [reservoirEnergyLaw_eq]
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) (clipSample C))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply compoundPoisson_integrable_id
  exact integrable_indexedPotential M.disorder.toMeasure (clipSample C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)) hC
    (fun _ _ => clipReal_bound hC _)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirBondEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L k : ℕ} [NeZero N]

lemma reservoirInsertionOn_site_energy (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) (h : ℝ) :
    reservoirInsertionOn M C H N L u (cavitySiteEnergy θ h)=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect (fun j =>
        energyInsertionFunctional (reservoirEnergyLaw M C N) (reservoirEnergyRoot M H N L u)
          (fun σ => cavitySiteEnergy θ h (fun a => σ (j a.1 a.2)))) := by
  rw [reservoirInsertionOn_energy M C H hH]
  let e := Equiv.curry (Fin k) (Fin (p-1)) (Fin N)
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma integral_reservoirInsertionOn_site (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) (hθ : ∀ a,‖(θ a).1‖≤C) :
    (∫ y,reservoirInsertionOn M C H N L u (cavitySiteEnergy θ (clipReal H y)) ∂M.field.toMeasure)=
      ∫ E,cavityArrayValue M.field.toMeasure id (clipReal H) (reservoirEnergyRoot M H N L u) E θ-
        reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N := by
  let F := reservoirEnergyRoot M H N L u
  let ρ := reservoirEnergyLaw M C N
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  simp_rw [reservoirInsertionOn_site_energy M C H hH]
  rw [FiniteLaw.integral_expect]
  · exact cavityArray_insertionFunctional ρ M.field.toMeasure id (clipReal H) (measurable_clipReal H)
      hF hH hC (fun y => clipReal_bound hH y) θ hθ
  · intro j
    apply Integrable.of_bound
      ((energyInsertionFunctional_lipschitz ρ hF).continuous.measurable.comp ?_).aestronglyMeasurable (H+C*k)
    · exact ae_of_all _ (fun y => by
        rw [Real.norm_eq_abs]
        apply (energyInsertionFunctional_bound ρ hF _).trans
        have hb := cavitySiteEnergy_norm_bound θ (clipReal H y) (fun a => j a.1 a.2) 0 hH hC hθ (clipReal_bound hH y)
        simpa only [Pi.zero_apply,zero_add,norm_zero] using hb)
    · apply Measurable.of_eval
      intro σ
      change Measurable (fun y => cavitySiteEnergy θ (clipReal H y) (fun a => σ (j a.1 a.2)))
      unfold cavitySiteEnergy
      apply Measurable.log
      apply Measurable.div_const
      apply Finset.measurable_sum
      intro ε _
      apply Measurable.exp
      exact ((measurable_clipReal H).mul_const _).add measurable_const

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirSitePoisson
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma insertionPoisson_site_energy (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) :
    insertionPoisson M C H N L u
      (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
      (fun _ z => cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2)) r=
      ∫ E,cavityPoissonValue M.disorder.toMeasure M.field.toMeasure (clipSample C) (clipReal H)
        (reservoirEnergyRoot M H N L u) r E-reservoirEnergyRoot M H N L u E
        ∂reservoirEnergyLaw M C N := by
  have hclip (z : InteractionSample p) : ‖(clipSample C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs,clipSample] using clipReal_bound hC (z.1 σ))
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  have ha (k : ℕ) :
      (∫ z : (Fin k → InteractionSample p)×ℝ,
        reservoirInsertionOn M C H N L u (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))
        ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)=
      ∫ θ : Fin k → InteractionSample p,∫ E,
        cavityArrayValue M.field.toMeasure (clipSample C) (clipReal H) (reservoirEnergyRoot M H N L u) E θ-
          reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
    have hm : Measurable (fun z : (Fin k → InteractionSample p)×ℝ =>
        reservoirInsertionOn M C H N L u (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))) := by
      simp_rw [reservoirInsertionOn_site_energy M C H hH]
      apply FiniteLaw.measurable_expect
      intro j
      apply (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF).continuous.measurable.comp
      convert measurable_cavityArrayEnergy (N := N) (p := p) (k := k) (clipSample C) (clipReal H)
          (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
          (measurable_clipReal H) (0 : (Fin N → Spin) → ℝ) j using 1
      all_goals try with_reducible_and_instances rfl
      ext z σ
      simp [cavityArrayEnergy]
    have hb (z : (Fin k → InteractionSample p)×ℝ) : |reservoirInsertionOn M C H N L u
        (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))|≤H+C*k := by
      apply reservoirInsertionOn_bound
      intro σ
      apply (cavitySiteEnergy_bound _ _ σ).trans
      have hs : (∑ j : Fin k,‖(clipSample C (z.1 j)).1‖)≤C*k := by
        simpa [mul_comm] using Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hclip (z.1 j))
      exact add_le_add (clipReal_bound hH _) hs
    rw [integral_prod _ (Integrable.of_bound hm.aestronglyMeasurable (H+C*k)
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z)))]
    apply integral_congr_ae
    filter_upwards [] with θ
    exact integral_reservoirInsertionOn_site M hC hH u (fun j => clipSample C (θ j)) (fun _ => hclip _)
  unfold insertionPoisson
  simp_rw [ha]
  exact cavityPoisson_gap_fubini M.disorder.toMeasure M.field.toMeasure (reservoirEnergyLaw M C N)
    (clipSample C) (clipReal H)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
    (measurable_clipReal H) hF hH hC hclip (fun y => clipReal_bound hH y) r

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ClippedProxyRate
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {N L q : ℕ} [NeZero N]

lemma clippedSiteInsertion_rate_bound_sat_oai (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
    |clippedSiteInsertion M C H N L u r-clippedSiteInsertion M C H N L u t|≤
      C*|(r:ℝ)-t|+4*(scoreRate N:ℝ)/(N+1) := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  have hθ z : ‖(clipSample (p := q+1) C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs] using clipSample_bound hC z σ)
  have hρ := reservoirEnergyLaw_integrable (N := N) M hC
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  have hFi := integrable_lipschitz_of_id (reservoirEnergyLaw M C N) hρ hF
  have hFb (E : (Fin N → Spin) → ℝ) : |reservoirEnergyRoot M H N L u E|≤‖E‖+(H*N+1*scoreRate N) := by
    simpa only [reservoirEnergyRoot,add_assoc] using averagedEnergyRoot_bound M.field.toMeasure
      ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
      (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (gridExponents_pos L)
      (clipReal H) (locatedFactor (spinFactor direction anchor u)) (fun y => clipReal_bound hH y)
      (fun i y a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a) E
  have hCi a := integrable_cavityPoissonValue M.disorder.toMeasure M.field.toMeasure
    (reservoirEnergyLaw M C N) hρ (clipSample C) (clipReal H) hθm (measurable_clipReal H)
    hC hH hθ (fun y => clipReal_bound hH y) hF.continuous hFb a
  have hh := averagedEnergyRoot_cavity_rate_bound M.disorder.toMeasure M.field.toMeasure (weights L)
    (reservoirEnergyLaw M C N) hρ r t (scoreRate N) (clipSample C) (clipReal H) hθm (measurable_clipReal H)
    (fun i : Spec L×ℕ => prior i.1) (gridExponents L) (gridExponents_pos L) (gridExponents_last L)
    (spinFactor direction anchor u) hH hC hθ (fun y => clipReal_bound hH y)
    (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)
  unfold clippedSiteInsertion
  rw [insertionPoisson_site_energy M hC hH,insertionPoisson_site_energy M hC hH,
    integral_sub (hCi r) hFi,integral_sub (hCi t) hFi,sub_sub_sub_cancel_right]
  simpa only [mul_one,reservoirEnergyRoot] using hh

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat_oai := @OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat_oai
