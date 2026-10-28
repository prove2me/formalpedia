-- Prove2me | solution 1 for OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:38:21.893343+00:00
-- url     : https://prove2.me/submissions/cf60df1e-bd6f-4d08-b3f6-c9a32744be61

import Mathlib
import Definitions.Def_DilutedSpin
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma sum_cavityGood {q N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : (Fin (q+1) → Fin (N+1)) → A) :
    (∑ x : {x // @CavityGood q N x},f x.val) =
      (∑ x : Fin (q+1) → Fin N,f (fun i => (x i).succ))+
      ∑ j : Fin (q+1), ∑ x : Fin q → Fin N,f (j.insertNth 0 (fun i => (x i).succ)) := by
  classical
  rw [← Equiv.sum_comp (cavityGoodEquiv q N)]
  simp [cavityGoodEquiv,Equiv.ofBijective,cavityIndexMap,Fintype.sum_prod_type]

open Classical in
lemma sum_cavityKeep {q N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : (Fin (q+1) → Fin (N+1)) → A) :
    (∑ x,if CavityGood x then f x else 0) =
      (∑ x : Fin (q+1) → Fin N,f (fun i => (x i).succ))+
      ∑ z : Fin (q+1) × (Fin q → Fin N),f (z.1.insertNth 0 (fun i => (z.2 i).succ)) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := CavityGood) _ (by simp)]
  rw [sum_cavityGood,Fintype.sum_prod_type]

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
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma expect_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (f : Ω → Λ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end DilutedSpinGlass.FiniteLaw
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_SizeSpinRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I J : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

lemma tower_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower (A := fun j => A (f j)) roots L T (fun j => Q (f j)) =
      tower (f ∘ roots) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma physical_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (L : ℕ)
    (y : FinitePath (Ω × Row (A := fun j => A (f j)) roots) L) :
    physical roots L y = physical (f ∘ roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.1,z)) (ih y.2)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma mark_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := fun j => A (f j)) roots) L) :
    mark (A := fun j => A (f j)) q L y = mark (A := A) (roots := f ∘ roots) q L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.2 q,z)) (ih y.2)

/-- Mere relabeling preserves every realized heterogeneous prior and factor.
This is used to identify per-occurrence and dictionary-label presentations. -/
theorem root_pullback (f : J → I) {k L : ℕ} (roots : Fin k → J)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    root T (fun j => Q (f j)) m base roots (fun j => factor (f j)) =
      root T Q m base (f ∘ roots) factor := by
  unfold root
  rw [tower_pullback]
  congr 1
  funext y
  simp only [logWeight,physical_pullback,mark_pullback,Function.comp_apply]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSpinMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {Z : Type} [MeasurableSpace Z]

lemma finite_logWeight_bound {N p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin)
    {C H : ℝ} (hθ : ∀ j x, |(theta j).1 x| ≤ C) (hh : ∀ i, |h i| ≤ H) :
    |logWeight theta h indices σ| ≤ H*N+C*k := by
  have hs (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]
  unfold logWeight
  apply (abs_add_le _ _).trans
  have h1 := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hθ j (fun q => σ (indices j q))))
  have h2 : |∑ i, h i*spin (σ i)| ≤ ∑ _i : Fin N, H :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simpa only [abs_mul,hs,mul_one] using hh i))
  simpa [mul_comm,add_comm] using add_le_add h1 h2

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

lemma abs_integral_le_const (μ : Measure Z) [IsProbabilityMeasure μ] {f : Z → ℝ} {B : ℝ}
    (h : ∀ z, |f z| ≤ B) : |∫ z, f z ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (ae_of_all μ (fun z => by simpa only [Real.norm_eq_abs] using h z)))

end DilutedSpinGlass.SizeCoupling
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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_bound (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C H : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h k x σ| ≤ H*N+C*k := by
  apply (abs_add_le _ _).trans
  have hx := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hV (rootArray k x j) σ))
  have hy : |∑ i, field (rootArray N h i)*spin (σ i)| ≤ H*N := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin N, H := Finset.sum_le_sum (fun i _ => by
        simpa only [abs_mul,abs_spin,mul_one] using hh (rootArray N h i))
      _ = H*N := by simp [mul_comm]
  have hx' : |∑ j, V (rootArray k x j) σ| ≤ C*k := by simpa [mul_comm] using hx
  linarith

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

end

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

lemma compoundPoisson_map_linear [CompleteSpace F] (r : ℝ≥0) (μ : Measure E)
    [IsProbabilityMeasure μ] (A : E →L[ℝ] F) :
    Measure.map A (compoundPoisson r μ) = compoundPoisson r (Measure.map A μ) := by
  let : IsProbabilityMeasure (Measure.map A μ) :=
    (Measure.isProbabilityMeasure_map_iff A.measurable.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map,charFunDual_compoundPoisson,charFunDual_compoundPoisson,charFunDual_map]

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

lemma integral_norm_sub_compound [CompleteSpace E] (r : ℝ≥0) (μ : Measure (E×E))
    [IsProbabilityMeasure μ] (hi : Integrable id μ) :
    (∫ z, ‖z.1-z.2‖ ∂compoundPoisson r μ) ≤ r*(∫ z,‖z.1-z.2‖ ∂μ) := by
  let A := ContinuousLinearMap.fst ℝ E E-ContinuousLinearMap.snd ℝ E E
  have hm : Measure.map A (compoundPoisson r μ) = compoundPoisson r (Measure.map A μ) :=
    compoundPoisson_map_linear r μ A
  let : IsProbabilityMeasure (Measure.map A μ) :=
    (Measure.isProbabilityMeasure_map_iff A.measurable.aemeasurable).mpr inferInstance
  have hai : Integrable id (Measure.map A μ) :=
    (integrable_map_measure aestronglyMeasurable_id A.measurable.aemeasurable).mpr (A.integrable_comp hi)
  have hb := compoundPoisson_norm_le r (Measure.map A μ) hai
  rw [← hm,integral_map A.measurable.aemeasurable (by fun_prop),
    integral_map A.measurable.aemeasurable (by fun_prop)] at hb
  exact hb

/-- A first-moment transport bound for the physical marked Poisson process.
It also justifies deletion of all repeated-new-site bonds at their actual cost. -/
lemma compoundPoisson_lipschitz_coupling [CompleteSpace E] (r : ℝ≥0) (μ : Measure (E×E))
    [IsProbabilityMeasure μ] (hi : Integrable id μ) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r (Measure.map Prod.fst μ))-
      (∫ x, f x ∂compoundPoisson r (Measure.map Prod.snd μ))| ≤
      C*r*(∫ z,‖z.1-z.2‖ ∂μ) := by
  let A := ContinuousLinearMap.fst ℝ E E
  let B := ContinuousLinearMap.snd ℝ E E
  have hmA := compoundPoisson_map_linear r μ A
  have hmB := compoundPoisson_map_linear r μ B
  have hc := compoundPoisson_integrable_id r μ hi
  have hia : Integrable (fun z : E×E => f z.1) (compoundPoisson r μ) := by
    have hp : Integrable id (Measure.map A (compoundPoisson r μ)) :=
      (integrable_map_measure aestronglyMeasurable_id A.measurable.aemeasurable).mpr (A.integrable_comp hc)
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable A.measurable.aemeasurable).mp
      (integrable_lipschitz_of_id _ hp hf)
  have hib : Integrable (fun z : E×E => f z.2) (compoundPoisson r μ) := by
    have hp : Integrable id (Measure.map B (compoundPoisson r μ)) :=
      (integrable_map_measure aestronglyMeasurable_id B.measurable.aemeasurable).mpr (B.integrable_comp hc)
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable B.measurable.aemeasurable).mp
      (integrable_lipschitz_of_id _ hp hf)
  change |(∫ x, f x ∂compoundPoisson r (Measure.map A μ))-
    (∫ x, f x ∂compoundPoisson r (Measure.map B μ))| ≤ _
  rw [← hmA,← hmB,integral_map A.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable,
    integral_map B.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable]
  change |(∫ z : E×E, f z.1 ∂compoundPoisson r μ)-(∫ z, f z.2 ∂compoundPoisson r μ)|≤_
  rw [← integral_sub hia hib]
  calc
    _ ≤ ∫ z, |f z.1-f z.2| ∂compoundPoisson r μ := abs_integral_le_integral_abs
    _ ≤ ∫ z : E×E, (C:ℝ)*‖z.1-z.2‖ ∂compoundPoisson r μ := by
      apply integral_mono (hia.sub hib).abs
        (((A-B).integrable_comp hc).norm.const_mul (C:ℝ))
      intro z
      exact hf.norm_sub_le z.1 z.2
    _ = (C:ℝ)*(∫ z,‖z.1-z.2‖ ∂compoundPoisson r μ) := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (integral_norm_sub_compound r μ hi) C.coe_nonneg

end DilutedSpinGlass

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

lemma count_linear_le_quadratic {B C D : ℝ} (hC : 0≤C) (hD : 0≤D) (k n : ℕ) :
    B+C*k+D*n ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2 := by
  have hk : (k:ℝ)≤k^2 := by exact_mod_cast Nat.le_self_pow (by omega : 2≠0) k
  have hn : (n:ℝ)≤n^2 := by exact_mod_cast Nat.le_self_pow (by omega : 2≠0) n
  nlinarith

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

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma measurable_rootSample_fixed
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : Measurable V) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (k n : ℕ) (a : RootPath I n) :
    Measurable (fun z : RootPath Y N × RootPath X k =>
      rootSample V field Q m factor z.1 k z.2 n a) := by
  let b := fun z : RootPath Y N × RootPath X k =>
    fun y : FinitePath (Fin N → Spin) (L+1) => energy V field z.1 k z.2 (terminalState L y)
  have hb : ∀ y,Measurable (fun z => b z y) := fun y =>
    measurable_energy V field (fun σ => (measurable_pi_apply σ).comp hV) hh k _
  exact measurable_root (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m b
    (rootArray n a) (fun _ => factor) hb (fun _ _ _ => measurable_const)

lemma measurable_rootSample
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : Measurable V) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (k n : ℕ) :
    Measurable (fun z : (RootPath Y N × RootPath X k) × RootPath I n =>
      rootSample V field Q m factor z.1.1 k z.1.2 n z.2) := by
  apply measurable_from_prod_countable_left
  intro a
  exact measurable_rootSample_fixed V field hV hh Q m factor k n a

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] [Countable I]
  [MeasurableSingletonClass I] in
lemma rootSample_bound (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hVb : ∀ x σ,|V x σ|≤C) (hhb : ∀ y,|field y|≤H)
    (hfb : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) :
    |rootSample V field Q m factor h k x n a|≤H*N+C*k+D*n := by
  exact root_uniform_bound _ Q m hm _ _ factor
    (fun y => energy_bound V field hVb hhb h k x _) hfb

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma integral_compound_energyRoot (μ : Measure X) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) :
    (∫ z : Sigma (RootPath X),rootSample V field Q m factor h z.1 z.2 a.1 a.2 ∂compoundRootLaw μ r)=
      ∫ E,energyRoot Q m field factor h a E ∂compoundPoisson r (Measure.map V μ) := by
  have he : Measurable (fun z : Sigma (RootPath X) => ∑ i,V (rootArray z.1 z.2 i)) := by
    apply measurable_sigmaUncurry (f := fun n (x : RootPath X n) => ∑ i,V (rootArray n x i))
    intro k
    simpa only [rootArrayEquiv_apply] using
      (show Measurable (fun x : RootPath X k => ∑ i,V (rootArrayEquiv (X := X) k x i)) by fun_prop)
  rw [← map_compoundRoot_energy μ V hV r,
    integral_map he.aemeasurable (energyRoot_lipschitz Q m hm field factor h a).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [rootSample,energyRoot,energy,Finset.sum_apply]

lemma fullRoot_energy_integral
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : Measurable V) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hVb : ∀ x σ,|V x σ|≤C) (hhb : ∀ y,|field y|≤H)
    (hfb : ∀ i y a,|Real.log (factor i y a)|≤D) :
    (∫ z,packRoot (rootSample V field Q m factor) z ∂fullRootLaw (fun _ => ξ) μ ν r s) =
      ∫ h,∫ a,∫ E,energyRoot Q m field factor h a E
        ∂compoundPoisson r (Measure.map V μ) ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
  rw [integral_fullRootLaw_reordered (fun _ => ξ) μ ν r s
    (measurable_rootSample V field hV hh Q m factor)
    (fun h k x n a => (rootSample_bound V field Q m hm factor hVb hhb hfb h k x n a).trans
      (count_linear_le_quadratic hC hD k n))]
  apply integral_congr_ae
  filter_upwards [] with h
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_compound_energyRoot μ r V field hV Q m hm factor h a

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperMoments
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Superposition with null marks permitted: equality of the centered mark
 characteristic exponents is enough, without equality of the raw intensities. -/
lemma compoundPoisson_superposition_centered (r s t : ℝ≥0)
    (μ ν τ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (h : ∀ L : StrongDual ℝ E, (r:ℂ)*(charFunDual μ L-1) =
      (s:ℂ)*(charFunDual ν L-1)+(t:ℂ)*(charFunDual τ L-1)) :
    compoundPoisson r μ = compoundPoisson s ν ∗ compoundPoisson t τ := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_conv,charFunDual_compoundPoisson,charFunDual_compoundPoisson,
    charFunDual_compoundPoisson,← Complex.exp_add,h]

omit [CompleteSpace E] in
lemma charFunDual_centered_map {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (V : X → E) (hV : Measurable V) (L : StrongDual ℝ E) :
    charFunDual (Measure.map V μ) L-1 = ∫ x, Complex.exp ((L (V x):ℂ)*Complex.I)-1 ∂μ := by
  have hi : Integrable (fun x => Complex.exp ((L (V x):ℂ)*Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,
    charFunDual_apply,integral_map hV.aemeasurable (by fun_prop)]

end DilutedSpinGlass

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

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompleteSpace E] in
lemma centeredExp_integrable (V : X → E) (hV : Measurable V) (L : StrongDual ℝ E) :
    Integrable (fun x => Complex.exp ((L (V x):ℂ)*Complex.I)-1) μ := by
  have hi : Integrable (fun x => Complex.exp ((L (V x):ℂ)*Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  exact hi.sub (integrable_const _)

omit [CompleteSpace E] in
lemma centered_finite_mark {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (V : X×A → E) (hV : Measurable V) (L : StrongDual ℝ E) :
    charFunDual (Measure.map V (μ.prod (finiteUniform A))) L-1 =
      (Fintype.card A:ℂ)⁻¹ * ∑ a, ∫ x, Complex.exp ((L (V (x,a)):ℂ)*Complex.I)-1 ∂μ := by
  rw [charFunDual_centered_map _ V hV,integral_prod_symm _ (centeredExp_integrable _ V hV L),
    integral_finiteUniform]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]

/-- Exact splitting of a finite marked process, allowing marks outside two
 disjoint families to be replaced by zero. The rates retain their exact finite-size values. -/
lemma finite_poisson_split {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (eA : A → C) (eB : B → C) (good : C → Prop) [DecidablePred good]
    (hs : ∀ f : C → ℂ, (∑ c,if good c then f c else 0) = (∑ a,f (eA a))+(∑ b,f (eB b)))
    (V : X×C → E) (hV : Measurable V) (r : ℝ≥0) :
    compoundPoisson r (Measure.map (fun z : X×C => if good z.2 then V z else 0)
      (μ.prod (finiteUniform C))) =
      compoundPoisson (r*(Fintype.card A)/(Fintype.card C))
        (Measure.map (fun z : X×A => V (z.1,eA z.2)) (μ.prod (finiteUniform A))) ∗
      compoundPoisson (r*(Fintype.card B)/(Fintype.card C))
        (Measure.map (fun z : X×B => V (z.1,eB z.2)) (μ.prod (finiteUniform B))) := by
  have hm0 : Measurable (fun z : X×C => if good z.2 then V z else 0) :=
    hV.ite (((Set.to_countable {c | good c}).measurableSet).preimage measurable_snd) measurable_const
  have hmA : Measurable (fun z : X×A => V (z.1,eA z.2)) :=
    hV.comp (measurable_fst.prodMk ((measurable_of_countable eA).comp measurable_snd))
  have hmB : Measurable (fun z : X×B => V (z.1,eB z.2)) :=
    hV.comp (measurable_fst.prodMk ((measurable_of_countable eB).comp measurable_snd))
  let : IsProbabilityMeasure (Measure.map (fun z : X×C => if good z.2 then V z else 0)
      (μ.prod (finiteUniform C))) :=
    (Measure.isProbabilityMeasure_map_iff hm0.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (Measure.map (fun z : X×A => V (z.1,eA z.2))
      (μ.prod (finiteUniform A))) :=
    (Measure.isProbabilityMeasure_map_iff hmA.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (Measure.map (fun z : X×B => V (z.1,eB z.2))
      (μ.prod (finiteUniform B))) :=
    (Measure.isProbabilityMeasure_map_iff hmB.aemeasurable).mpr inferInstance
  apply compoundPoisson_superposition_centered
  intro L
  rw [centered_finite_mark μ _ hm0,centered_finite_mark μ _ hmA,centered_finite_mark μ _ hmB]
  have he (c : C) : (∫ x, Complex.exp ((L (if good c then V (x,c) else 0):ℂ)*Complex.I)-1 ∂μ) =
      if good c then (∫ x,Complex.exp ((L (V (x,c)):ℂ)*Complex.I)-1 ∂μ) else 0 := by
    split_ifs <;> simp
  simp only [he]
  rw [hs]
  have ha : (Fintype.card A:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card C:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp
  simp only [mul_comm Complex.I]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavitySplit
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

lemma cavityOldRate_card (α : ℝ≥0) (q N : ℕ) :
    (α*(N+1))*Fintype.card (Fin (q+1) → Fin N)/Fintype.card (Fin (q+1) → Fin (N+1)) =
      reservoirRate α q N := by
  simp only [Fintype.card_fun,Fintype.card_fin,
    reservoirRate,div_pow,pow_succ]
  have hn : (N:ℝ≥0)+1 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

lemma cavityOneRate_card (α : ℝ≥0) (q N : ℕ) :
    (α*(N+1))*Fintype.card (Fin (q+1) × (Fin q → Fin N))/Fintype.card (Fin (q+1) → Fin (N+1)) =
      oneNewRate α q N := by
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_mul,
    Nat.cast_add,Nat.cast_one,oneNewRate,div_pow,pow_succ]
  have hn : (N:ℝ≥0)+1 ≠ 0 := by positivity
  field_simp

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

open Classical in
/-- Exact old-site / one-new-site split of the physical Poisson energy after
 discarding only indices meeting the new site at least twice. No symmetry of
 the interaction has yet been used; the distinguished coordinate is explicit. -/
lemma cavity_compound_split (α : ℝ≥0) (q N : ℕ) [NeZero N]
    (V : X × (Fin (q+1) → Fin (N+1)) → E) (hV : Measurable V) :
    compoundPoisson (α*(N+1)) (Measure.map (fun z => if CavityGood z.2 then V z else 0)
      (μ.prod (finiteUniform (Fin (q+1) → Fin (N+1))))) =
      compoundPoisson (reservoirRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) → Fin N) => V (z.1,fun i => (z.2 i).succ))
          (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
      compoundPoisson (oneNewRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            V (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
          (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N))))) := by
  simpa only [cavityOldRate_card,cavityOneRate_card] using
    finite_poisson_split μ (fun x : Fin (q+1) → Fin N => fun i => (x i).succ)
      (fun z : Fin (q+1) × (Fin q → Fin N) => z.1.insertNth 0 (fun i => (z.2 i).succ))
      CavityGood (fun f => sum_cavityKeep f) V hV (α*(N+1))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityRateLimits
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology NNReal BigOperators

open Classical in
lemma cavity_bad_count (q N : ℕ) :
    (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (0:ℝ) else 1) =
      (N+1:ℝ)^(q+1)-(N:ℝ)^(q+1)-(q+1:ℝ)*(N:ℝ)^q := by
  have hg := sum_cavityKeep (q := q) (N := N) (fun _ => (1:ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_prod,nsmul_eq_mul,mul_one,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_mul] at hg
  have he : (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (0:ℝ) else 1) =
      (∑ _x : Fin (q+1) → Fin (N+1),(1:ℝ))-
      (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (1:ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> norm_num
  rw [he,hg]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  ring

open Classical in
lemma cavityBadRate_count (α : ℝ≥0) (q N : ℕ) :
    cavityBadRate α q N = (α:ℝ)*(N+1)*
      (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (0:ℝ) else 1)/(N+1)^(q+1) := by
  rw [cavity_bad_count]
  simp only [cavityBadRate,oneNewRate,reservoirRate,NNReal.coe_mul,NNReal.coe_add,
    NNReal.coe_natCast,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_div,div_pow,pow_succ]
  have hd : (N:ℝ)+1≠0 := by positivity
  field_simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

lemma integral_root_prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) × (Fin n → Y) → ℝ)
    (hF : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => ν)))) :
    (∫ z : RootPath (X×Y) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod ν)) =
      ∫ x : Fin n → X,∫ y : Fin n → Y,F (x,y)
        ∂Measure.pi (fun _ : Fin n => ν) ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_rootArray_eq_pi (μ.prod ν) n (fun z : Fin n → X×Y => F ((fun i => (z i).1),(fun i => (z i).2)))]
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin n)
    (fun _ => μ) (fun _ => ν)).integral_comp' F
  exact he.trans (integral_prod F hF)

lemma integral_root_prod_finite {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (hF : Measurable F)
    {B : ℝ} (hb : ∀ z,|F z|≤B) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (PMF.uniformOfFintype J).toMeasure)) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  have hi : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype J).toMeasure))) :=
    Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hb z))
  rw [integral_root_prod μ (PMF.uniformOfFintype J).toMeasure n F hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ j,F (x,j) ∂Measure.pi (fun _ : Fin n => finiteUniform J)) = _
  rw [finiteUniform_pi,integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

end DilutedSpinGlass

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

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma rootSample_eq_spinRoot
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (k : ℕ) (x : RootPath (X × (Fin p → Fin N)) k)
    (l : ℕ) (a : RootPath (I × Fin N) l) :
    rootSample (indexedPotential theta) field (fun i : I × Fin N => Q i.1)
      m (locatedFactor ψ) h k x l a =
    SizeCoupling.spinRoot (fun j => Q (rootArray l a j).1) m
      (fun j => theta (rootArray k x j).1) (fun i => field (rootArray N h i))
      (fun j => (rootArray k x j).2) (fun j => (rootArray l a j).2)
      (fun j => ψ (rootArray l a j).1) := by
  unfold rootSample SizeCoupling.spinRoot
  have he := root_pullback (fun j : Fin l => rootArray l a j) id
    (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I × Fin N => Q i.1) m
    (fun y => energy (indexedPotential theta) field h k x (terminalState L y))
    (locatedFactor ψ)
  convert he.symm using 1 <;> rfl

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonCountThinning
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
variable {E X A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]

lemma finite_poisson_deletion (r : ℝ≥0) (good : A → Prop) [DecidablePred good]
    (V : X×A → E) (hV : Measurable V) {D : ℝ} (hD : 0≤D) (hbound : ∀ z,‖V z‖≤D)
    {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r (Measure.map V (μ.prod (finiteUniform A))))-
      (∫ x, f x ∂compoundPoisson r (Measure.map (fun z : X×A => if good z.2 then V z else 0)
        (μ.prod (finiteUniform A))))| ≤
      C*r*(D/(Fintype.card A)*(∑ a : A,if good a then (0:ℝ) else 1)) := by
  let W : X×A → E := fun z => if good z.2 then V z else 0
  have hW : Measurable W := hV.ite
    ((Set.to_countable {a | good a}).measurableSet.preimage measurable_snd) measurable_const
  let J : X×A → E×E := fun z => (V z,W z)
  have hJ : Measurable J := hV.prodMk hW
  have hWb (z : X×A) : ‖W z‖≤D := by dsimp [W]; split <;> simp_all
  have hJb (z : X×A) : ‖J z‖≤D := by
    change max ‖V z‖ ‖W z‖ ≤ D
    exact max_le (hbound z) (hWb z)
  let ξ := Measure.map J (μ.prod (finiteUniform A))
  let : IsProbabilityMeasure ξ :=
    (Measure.isProbabilityMeasure_map_iff hJ.aemeasurable).mpr inferInstance
  have hJi : Integrable id ξ := by
    rw [integrable_map_measure aestronglyMeasurable_id hJ.aemeasurable]
    exact Integrable.of_bound hJ.aestronglyMeasurable D (Filter.Eventually.of_forall hJb)
  have hh := compoundPoisson_lipschitz_coupling r ξ hJi hf
  have h1 : Measure.map Prod.fst ξ = Measure.map V (μ.prod (finiteUniform A)) := by
    rw [show ξ=Measure.map J (μ.prod (finiteUniform A)) from rfl,Measure.map_map measurable_fst hJ]
    rfl
  have h2 : Measure.map Prod.snd ξ = Measure.map W (μ.prod (finiteUniform A)) := by
    rw [show ξ=Measure.map J (μ.prod (finiteUniform A)) from rfl,Measure.map_map measurable_snd hJ]
    rfl
  rw [h1,h2] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show ξ=Measure.map J (μ.prod (finiteUniform A)) from rfl,
    integral_map hJ.aemeasurable (by fun_prop)]
  have hdif : Integrable (fun z : X×A => ‖V z-W z‖) (μ.prod (finiteUniform A)) := by
    apply Integrable.of_bound ((hV.sub hW).norm.aestronglyMeasurable) D
    apply Filter.Eventually.of_forall
    intro z
    change ‖‖V z-W z‖‖≤D
    rw [norm_norm]
    dsimp [W]
    split <;> simp_all
  have hg : Integrable (fun z : X×A => D*(if good z.2 then 0 else 1))
      (μ.prod (finiteUniform A)) := by
    apply Integrable.of_bound ((measurable_of_countable (fun a : A => D*(if good a then (0:ℝ) else 1))).comp measurable_snd).aestronglyMeasurable D
    apply Filter.Eventually.of_forall
    intro z
    change ‖D*(if good z.2 then (0:ℝ) else 1)‖≤D
    split_ifs <;> simp [abs_of_nonneg hD,hD]
  calc
    _ ≤ ∫ z : X×A, D*(if good z.2 then 0 else 1) ∂μ.prod (finiteUniform A) := by
      apply integral_mono hdif hg
      intro z
      dsimp [J,W]
      split_ifs <;> simp_all
    _ = _ := by
      rw [integral_prod_symm _ hg]
      change (∫ a : A, (∫ _x : X, D*(if good a then (0:ℝ) else 1) ∂μ) ∂finiteUniform A) = _
      simp only [integral_const,probReal_univ,one_smul]
      rw [integral_finiteUniform]
      simp only [smul_eq_mul,Finset.mul_sum]
      ring_nf

end DilutedSpinGlass

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
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

open Classical in
/-- The actual finite-volume Poisson cavity split, with only the discarded
multiple-new-index energy as error. The bound is uniform over the rooted
finite power-mean functional, its old disorder and every auxiliary level. -/
lemma cavity_split_lipschitz_bound (α : ℝ≥0) (q N : ℕ) [NeZero N]
    (V : X × (Fin (q+1) → Fin (N+1)) → E) (hV : Measurable V)
    {D : ℝ} (hD : 0≤D) (hbound : ∀ z,‖V z‖≤D)
    {f : E → ℝ} (hf : LipschitzWith 1 f) :
    |(∫ x, f x ∂compoundPoisson (α*(N+1))
        (Measure.map V (μ.prod (finiteUniform (Fin (q+1) → Fin (N+1))))))-
      (∫ x, f x ∂(compoundPoisson (reservoirRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) → Fin N) => V (z.1,fun i => (z.2 i).succ))
          (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
      compoundPoisson (oneNewRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            V (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
          (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))))))| ≤
      D*cavityBadRate α q N := by
  rw [← cavity_compound_split μ α q N V hV]
  apply (finite_poisson_deletion μ (α*(N+1)) CavityGood V hV hD hbound hf).trans_eq
  rw [cavityBadRate_count]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
    NNReal.coe_one,one_mul,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast]
  ring

end DilutedSpinGlass

end

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

namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory HeterogeneousMarks
variable {Z : Type} [MeasurableSpace Z]
lemma measurable_spinRoot {N p k l r : ℕ} {A : Fin l → Type} [∀ i,Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Z → Fin k → InteractionSample p) (h : Z → Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hθ : ∀ j σ,Measurable (fun z => (theta z j).1 σ))
    (hh : ∀ i,Measurable (fun z => h z i)) :
    Measurable (fun z => spinRoot Q m (theta z) (h z) indices sites ψ) := by
  apply measurable_root
  · intro x
    exact (Finset.measurable_sum _ (fun j _ => hθ j _)).add
      (Finset.measurable_sum _ (fun i _ => (hh i).mul_const _))
  · intro i x a
    exact measurable_const

lemma spinRoot_bound {N p k l r : ℕ} {A : Fin l → Type} [∀ i,Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j,0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ,|(theta j).1 σ|≤C) (hh : ∀ i,|h i|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |spinRoot Q m theta h indices sites ψ|≤H*N+C*k+D*l :=
  root_uniform_bound _ Q m hm _ id _
    (fun x => finite_logWeight_bound theta h indices (KernelTower.terminalState r x) hθ hh)
    (fun i _ a => hψ i _ a)
end DilutedSpinGlass.SizeCoupling

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionPoint
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory SizeCoupling
variable {X Y J W : Type} [MeasurableSpace X] [MeasurableSpace Y] [Fintype J] [Fintype W]

lemma expect_double_integral (P : FiniteLaw W) (Q : FiniteLaw J)
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (F : X → Y → J → W → ℝ)
    (hf : ∀ j w,Measurable (fun z : X × Y => F z.1 z.2 j w))
    {B : ℝ} (hb : ∀ x y j w,|F x y j w|≤B) :
    P.expect (fun w => ∫ x,Q.expect (fun j => ∫ y,F x y j w ∂ν) ∂μ) =
      ∫ x,∫ y,Q.expect (fun j => P.expect (fun w => F x y j w)) ∂ν ∂μ := by
  have hmj (j : J) (w : W) : Measurable (fun x => ∫ y,F x y j w ∂ν) :=
    (hf j w).stronglyMeasurable.integral_prod_right'.measurable
  rw [← integral_expect_bounded P μ (fun x w => Q.expect (fun j => ∫ y,F x y j w ∂ν))
    (fun w => measurable_expect _ (fun j => hmj j w))
    (fun x w => abs_expect_le _ (fun j => abs_integral_le_const _ (fun y => hb x y j w)))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [expect_comm]
  symm
  rw [integral_expect_bounded Q ν (fun y j => P.expect (fun w => F x y j w))
    (fun j => measurable_expect _ (fun w => (hf j w).comp (measurable_const.prodMk measurable_id)))
    (fun y j => abs_expect_le _ (fun w => hb x y j w))]
  apply expect_congr
  intro j
  exact integral_expect_bounded P ν (fun y w => F x y j w)
    (fun w => (hf j w).comp (measurable_const.prodMk measurable_id)) (fun y w => hb x y j w)

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountArrayBridge
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower SizeCoupling
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L k l : ℕ}

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma arrayRoot_measurable (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (a : Fin l → I) (j : Fin k → Fin p → Fin N) (w : Fin l → Fin N) :
    Measurable (fun z : (Fin k → X) × RootPath Y N => arrayRoot theta field Q m ψ a z.1 z.2 j w) := by
  apply measurable_spinRoot
  · intro t σ; exact (hθ σ).comp ((measurable_pi_apply t).comp measurable_fst)
  · intro t; exact hh.comp ((measurable_rootArray N t).comp measurable_snd)

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
  [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma arrayRoot_bound (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D)
    (a : Fin l → I) (x : Fin k → X) (h : RootPath Y N)
    (j : Fin k → Fin p → Fin N) (w : Fin l → Fin N) :
    |arrayRoot theta field Q m ψ a x h j w|≤H*N+C*k+D*l :=
  spinRoot_bound _ m hm _ _ j w _ (fun _ σ => hθ _ σ) (fun _ => hh _) (fun _ σ a => hψ _ σ a)

omit [Countable I] [MeasurableSingletonClass I] in
lemma countedMean_eq_arrays [NeZero N]
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ) (k l : ℕ) :
    countedMean (N := N) μ ξ ν theta field Q m ψ k l =
      ∫ a : Fin l → I,∫ x : Fin k → X,∫ h : RootPath Y N,
        (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
          (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect
            (fun w => arrayRoot theta field Q m ψ a x h j w))
        ∂rootLaw N (fun _ => ξ) ∂Measure.pi (fun _ : Fin k => μ)
        ∂Measure.pi (fun _ : Fin l => ν) := by
  unfold countedMean spinMean
  simp only [FiniteLaw.pi_uniform]
  let F := fun (a : Fin l → I) (x : Fin k → X) => ∫ h : RootPath Y N,
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
      (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect
        (fun w => arrayRoot theta field Q m ψ a x h j w)) ∂rootLaw N (fun _ => ξ)
  change (∫ a : RootPath I l,∫ x : RootPath X k,F (rootArray l a) (rootArray k x)
    ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν)) =
    ∫ a : Fin l → I,∫ x : Fin k → X,F a x ∂Measure.pi (fun _ : Fin k => μ)
      ∂Measure.pi (fun _ : Fin l => ν)
  rw [integral_rootArray_eq_pi ν l (fun a => ∫ x : RootPath X k,F a (rootArray k x) ∂rootLaw k (fun _ => μ))]
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_rootArray_eq_pi μ k (F a)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma arrayRoot_swap_expect [NeZero N]
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (a : Fin l → I) :
    (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect (fun w =>
      ∫ x : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun j => ∫ h : RootPath Y N,arrayRoot theta field Q m ψ a x h j w ∂rootLaw N (fun _ => ξ))
      ∂Measure.pi (fun _ : Fin k => μ)) =
    ∫ x : Fin k → X,∫ h : RootPath Y N,
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
        (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect (fun w => arrayRoot theta field Q m ψ a x h j w))
      ∂rootLaw N (fun _ => ξ) ∂Measure.pi (fun _ : Fin k => μ) := by
  exact FiniteLaw.expect_double_integral FiniteLaw.uniform FiniteLaw.uniform
    (Measure.pi (fun _ : Fin k => μ)) (rootLaw N (fun _ => ξ))
    (arrayRoot theta field Q m ψ a)
    (arrayRoot_measurable theta field hθm hhm Q m ψ a)
    (arrayRoot_bound theta field Q m hm ψ hθ hh hψ a)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRootCounts
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory SizeCoupling
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] {M : ℕ}

lemma integral_twoCompound_counts
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : RootPath X k × RootPath I n => F k z.1 n z.2))
    {B C D : ℝ} (hb : ∀ k x n a,|F k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,F z.1.1 z.1.2 z.2.1 z.2.2 ∂(compoundRootLaw μ r).prod (compoundRootLaw ν s)) =
      ∫ k : ℕ,∫ n : ℕ,∫ a,∫ x,F k x n a ∂rootLaw k (fun _ => μ)
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂poissonMeasure r := by
  have hm : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F z.1.1 z.1.2 z.2.1 z.2.2) := by
    exact measurable_sigmaProd (f := fun k x (a : Sigma (RootPath I)) => F k x a.1 a.2)
      (fun k => measurable_prodSigma (f := fun x n a => F k x n a) (hf k))
  have hi := twoCompound_integrable_quadratic μ ν r s hm hb
  rw [integral_prod _ hi]
  have hg (k : ℕ) : Measurable (fun x : RootPath X k => ∫ a : Sigma (RootPath I),
      F k x a.1 a.2 ∂compoundRootLaw ν s) := by
    exact (measurable_prodSigma (hf k)).stronglyMeasurable.integral_prod_right'.measurable
  change (∫ z : Sigma (RootPath X),∫ a : Sigma (RootPath I),F z.1 z.2 a.1 a.2
    ∂compoundRootLaw ν s ∂familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))) = _
  rw [integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k x => ∫ a : Sigma (RootPath I),F k x a.1 a.2 ∂compoundRootLaw ν s) hg hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with k
  have he (x : RootPath X k) :
      (∫ a : Sigma (RootPath I),F k x a.1 a.2 ∂compoundRootLaw ν s)=
        ∫ n : ℕ,∫ a,F k x n a ∂rootLaw n (fun _ => ν) ∂poissonMeasure s := by
    have hfm (n : ℕ) : Measurable (F k x n) := (hf k n).comp (measurable_const.prodMk measurable_id)
    exact integral_familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
      (F k x) hfm (familyLaw_integrable_bound _ _ _ hfm
        ((integrable_const (B+C*(k:ℝ)^2)).add ((poisson_integrable_count_sq s).const_mul D)) (hb k x))
  simp_rw [he]
  have hgm : Measurable (fun z : RootPath X k × ℕ =>
      ∫ a,F k z.1 z.2 a ∂rootLaw z.2 (fun _ => ν)) := by
    apply measurable_from_prod_countable_left
    intro n
    exact ((hf k n).stronglyMeasurable.integral_prod_right' (ν := rootLaw n (fun _ => ν))).measurable
  have hbi : Integrable (fun z : RootPath X k × ℕ => B+C*(k:ℝ)^2+D*(z.2:ℝ)^2)
      ((rootLaw k (fun _ => μ)).prod (poissonMeasure s)) :=
    (integrable_const (B+C*(k:ℝ)^2)).add
      (((poisson_integrable_count_sq s).const_mul D).comp_snd (rootLaw k (fun _ => μ)))
  have hgi : Integrable (fun z : RootPath X k × ℕ => ∫ a,F k z.1 z.2 a ∂rootLaw z.2 (fun _ => ν))
      ((rootLaw k (fun _ => μ)).prod (poissonMeasure s)) :=
    hbi.mono' hgm.aestronglyMeasurable (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hb k z.1 z.2)))
  rw [integral_integral_swap hgi]
  apply integral_congr_ae
  filter_upwards [] with n
  exact integral_integral_swap (Integrable.of_bound (hf k n).aestronglyMeasurable
    (B+C*(k:ℝ)^2+D*(n:ℝ)^2) (ae_of_all _ (fun z => by
      change |F k z.1 n z.2| ≤ _
      exact hb k z.1 n z.2)))

lemma integral_fullRootLaw_counts
    (ξ : Fin M → Measure Y) [∀ i,IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n a,|F h k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ k : ℕ,∫ n : ℕ,∫ a,∫ x,∫ h,F h k x n a ∂rootLaw M ξ
        ∂rootLaw k (fun _ => μ) ∂rootLaw n (fun _ => ν)
        ∂poissonMeasure s ∂poissonMeasure r := by
  have hi := fullRoot_integrable_quadratic ξ μ ν r s hf hb
  rw [fullRootLaw,integral_prod_symm _ hi]
  apply integral_twoCompound_counts μ ν r s
    (F := fun k x n a => ∫ h,F h k x n a ∂rootLaw M ξ) (B := B) (C := C) (D := D)
  · intro k n
    have hh : Measurable (fun z : (RootPath X k × RootPath I n) × RootPath Y M =>
        F z.2 k z.1.1 n z.1.2) :=
      (hf k n).comp ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  · intro k x n a
    exact abs_integral_le_const _ (fun h => hb h k x n a)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalCountLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower SizeCoupling
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ} [NeZero N]

lemma fixed_root_countedMean
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (k l : ℕ) :
    (∫ a : RootPath (I × Fin N) l,∫ x : RootPath (X × (Fin p → Fin N)) k,∫ h : RootPath Y N,
      rootSample (indexedPotential theta) field (fun i : I × Fin N => Q i.1)
        m (locatedFactor ψ) h k x l a
      ∂rootLaw N (fun _ => ξ)
      ∂rootLaw k (fun _ => μ.prod (finiteUniform (Fin p → Fin N)))
      ∂rootLaw l (fun _ => ν.prod (finiteUniform (Fin N)))) =
      countedMean (N := N) μ ξ ν theta field Q m ψ k l := by
  let F (a : Fin l → I) (w : Fin l → Fin N) (z : (Fin k → X) × (Fin k → Fin p → Fin N)) :=
    ∫ h : RootPath Y N,arrayRoot theta field Q m ψ a z.1 h z.2 w ∂rootLaw N (fun _ => ξ)
  have hf (a : Fin l → I) (w : Fin l → Fin N) : Measurable (F a w) := by
    apply measurable_from_prod_countable_left
    intro j
    exact (arrayRoot_measurable theta field hθm hhm Q m ψ a j w).stronglyMeasurable.integral_prod_right'.measurable
  have hb (a : Fin l → I) (w : Fin l → Fin N) (z) : |F a w z|≤H*N+C*k+D*l :=
    abs_integral_le_const _ (fun h => arrayRoot_bound theta field Q m hm ψ hθ hh hψ a z.1 h z.2 w)
  let G (z : (Fin l → I) × (Fin l → Fin N)) :=
    ∫ x : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
      (fun j => F z.1 z.2 (x,j)) ∂Measure.pi (fun _ : Fin k => μ)
  have hG : Measurable G := measurable_of_countable G
  have hGb (z) : |G z|≤H*N+C*k+D*l :=
    abs_integral_le_const _ (fun x => FiniteLaw.abs_expect_le _ (fun j => hb z.1 z.2 (x,j)))
  calc
    _ = ∫ a : RootPath (I × Fin N) l,
        G ((fun i => (rootArray l a i).1),(fun i => (rootArray l a i).2))
        ∂rootLaw l (fun _ => ν.prod (finiteUniform (Fin N))) := by
      apply integral_congr_ae
      filter_upwards [] with a
      simp_rw [rootSample_eq_spinRoot]
      exact integral_root_prod_finite μ k
        (F (fun i => (rootArray l a i).1) (fun i => (rootArray l a i).2)) (hf _ _) (hb _ _)
    _ = ∫ a : Fin l → I,(FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect
        (fun w => G (a,w)) ∂Measure.pi (fun _ : Fin l => ν) :=
      integral_root_prod_finite ν l G hG hGb
    _ = countedMean (N := N) μ ξ ν theta field Q m ψ k l := by
      rw [countedMean_eq_arrays]
      apply integral_congr_ae
      filter_upwards [] with a
      exact arrayRoot_swap_expect μ ξ theta field hθm hhm Q m hm ψ hθ hh hψ a

lemma fullRoot_countedMean
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ z,packRoot (rootSample (indexedPotential theta) field
      (fun i : I × Fin N => Q i.1) m (locatedFactor ψ)) z
      ∂fullRootLaw (fun _ : Fin N => ξ) (μ.prod (finiteUniform (Fin p → Fin N)))
        (ν.prod (finiteUniform (Fin N))) r s) =
      twoPoissonMean r s (countedMean (N := N) μ ξ ν theta field Q m ψ) := by
  let V : X × (Fin p → Fin N) → (Fin N → Spin) → ℝ := indexedPotential theta
  let Q' := fun i : I × Fin N => Q i.1
  let f := locatedFactor (N := N) ψ
  have hV : Measurable V := measurable_indexedPotential theta hθm
  have hVb : ∀ x σ, |V x σ| ≤ C := fun x σ => hθ x.1 _
  have hfb : ∀ i y a, |Real.log (f i y a)| ≤ D := fun i y a => hψ i.1 _ a
  let F := rootSample V field Q' m f
  have hfm : ∀ k l, Measurable (fun z : (RootPath Y N × RootPath (X × (Fin p → Fin N)) k) ×
      RootPath (I × Fin N) l => F z.1.1 k z.1.2 l z.2) :=
    measurable_rootSample V field hV hhm Q' m f
  have hfl : ∀ h k x l a, |F h k x l a| ≤ H*N+C*k+D*l :=
    rootSample_bound V field Q' m hm f hVb hh hfb
  have hfbq : ∀ h k x l a, |F h k x l a| ≤ H*N+C*(k:ℝ)^2+D*(l:ℝ)^2 :=
    fun h k x l a => (hfl h k x l a).trans (count_linear_le_quadratic hC hD k l)
  change (∫ z,packRoot F z ∂fullRootLaw (fun _ : Fin N => ξ)
    (μ.prod (finiteUniform (Fin p → Fin N))) (ν.prod (finiteUniform (Fin N))) r s) = _
  rw [integral_fullRootLaw_counts (fun _ : Fin N => ξ)
    (μ.prod (finiteUniform (Fin p → Fin N))) (ν.prod (finiteUniform (Fin N))) r s hfm hfbq]
  unfold twoPoissonMean
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_congr_ae
  filter_upwards [] with l
  exact fixed_root_countedMean μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ k l

end DilutedSpinGlass.PhysicalRoot

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

/-- The literal perturbed physical mean as a compound Poisson energy integral.
Counts, index repetitions, fields, and the full marked reservoir are retained. -/
lemma perturbedMean_energy_integral
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ r s =
      N*Real.log 2 + ∫ h,∫ a,∫ E,energyRoot (fun i : I×Fin N => Q i.1) m field
        (locatedFactor ψ) h a E
        ∂compoundPoisson r (Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin p → Fin N))))
        ∂compoundRootLaw (ν.prod (finiteUniform (Fin N))) s ∂rootLaw N (fun _ => ξ) := by
  unfold perturbedMean
  congr 1
  rw [← fullRoot_countedMean μ ξ ν r s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ]
  exact fullRoot_energy_integral ξ (μ.prod (finiteUniform (Fin p → Fin N)))
    (ν.prod (finiteUniform (Fin N))) r s (indexedPotential theta) field
    (measurable_indexedPotential theta hθm) hhm (fun i : I×Fin N => Q i.1) m hm
    (locatedFactor ψ) hC hD (fun z σ => hθ z.1 _) hh (fun i y a => hψ i.1 _ a)

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootIntegralOrder
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

lemma integrable_energyRoot_all (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (μ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    Integrable (fun z : ((RootPath Y N) × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
      energyRoot Q m field factor z.1.1 z.1.2 z.2)
      (((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s)).prod μ) := by
  have hc : Integrable (fun a : Sigma (RootPath I) => (a.1:ℝ)) (compoundRootLaw ν s) :=
    familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s
  have hb := ((hμ.norm.comp_snd ((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s))).add
    (integrable_const (H*N))).add (((hc.comp_snd (rootLaw N (fun _ => ξ))).comp_fst μ).const_mul D)
  apply hb.mono' (((measurable_energyRoot Q m field hhm factor).comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq,Function.comp_apply] using energyRoot_bound Q m hm field factor hh hf z.1.1 z.1.2 z.2)

lemma integral_averagedEnergyRoot (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (μ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    (∫ h,∫ a,∫ E,energyRoot Q m field factor h a E ∂μ
      ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ)) =
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor E ∂μ := by
  have hi := integrable_energyRoot_all ξ ν s μ hμ Q m hm field hhm factor hh hf
  rw [← integral_prod _ hi.integral_prod_left,integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [hi.swap.prod_right_ae] with E hE
  exact integral_prod _ hE

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalCavitySplit
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
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma perturbedMean_averagedEnergyRoot
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample q) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ r s =
      N*Real.log 2 + ∫ E,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ) E
        ∂compoundPoisson r (Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin q → Fin N)))) := by
  let : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) theta) (μ.prod (finiteUniform (Fin q → Fin N)))) :=
    Measure.isProbabilityMeasure_map (measurable_indexedPotential theta hθm).aemeasurable
  rw [perturbedMean_energy_integral μ ξ ν r s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ]
  congr 1
  exact integral_averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s _
    (compoundPoisson_integrable_id r _ (integrable_indexedPotential μ theta hθm hC hθ))
    (fun i : I×Fin N => Q i.1) m hm field hhm (locatedFactor ψ) hh
    (fun i _ a => hψ i.1 _ a)

/-- The actual new system differs from its reservoir-plus-cavity energy law
only by the double-new-coordinate rate. All physical field and mark averages
are retained, with their original counts and sites. -/
lemma perturbedMean_cavity_split_sat_oai
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) s -
      ((N+1:ℕ)*Real.log 2 + ∫ E,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) E
        ∂(compoundPoisson (reservoirRate α q N)
          (Measure.map (fun z : X × (Fin (q+1) → Fin N) =>
            indexedPotential theta (z.1,fun i => (z.2 i).succ))
            (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
        compoundPoisson (oneNewRate α q N)
          (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            indexedPotential theta (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
            (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))))))| ≤ C*cavityBadRate α q N := by
  rw [perturbedMean_averagedEnergyRoot μ ξ ν (α*(N+1)) s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ,
    add_sub_add_left_eq_sub]
  exact cavity_split_lipschitz_bound μ α q N (indexedPotential theta)
    (measurable_indexedPotential theta hθm) hC
    (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by
      simpa only [Real.norm_eq_abs,indexedPotential] using hθ z.1 (fun i => σ (z.2 i))))
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s
      (fun i : I×Fin (N+1) => Q i.1) m hm field hhm (locatedFactor ψ) hh
      (fun i _ a => hψ i.1 _ a))

end DilutedSpinGlass.SizeCoupling

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split_sat_oai := @OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split_sat_oai
