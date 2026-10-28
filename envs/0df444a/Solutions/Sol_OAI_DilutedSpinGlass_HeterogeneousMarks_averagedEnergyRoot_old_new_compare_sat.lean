-- Prove2me | solution 1 for OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:37.620435+00:00
-- url     : https://prove2.me/submissions/dfd3f20c-cd79-49ef-aaff-ff4fe4190116

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

/-- Finite independence identity, valid for arbitrary and distinct kernels. -/
theorem expect_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → ℝ) :
    (pi Q).expect (fun x => ∏ i, f i (x i)) = ∏ i, (Q i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib, Fintype.prod_sum]

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProducts
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
open scoped BigOperators

/-- Fubini at an arbitrary coordinate, retaining dependent finite sample types. -/
theorem expect_pi_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (Q : (i : ι) → FiniteLaw (α i))
    (i : ι) (H : ((i : ι) → α i) → ℝ) :
    (pi Q).expect H = (Q i).expect (fun a =>
      (pi (fun j : {j // j ≠ i} => Q j)).expect
        (fun rest => H ((Equiv.piSplitAt i α).symm (a,rest)))) := by
  classical
  have hprod (x : (i : ι) → α i) :
      (∏ j, (Q j).weight (x j)) =
        (Q i).weight (x i) * ∏ j : {j // j ≠ i}, (Q j).weight (x j) := by
    let : Fintype {j : ι // j = i} := Subtype.fintype (fun j => j = i)
    have hh := Fintype.prod_subtype_mul_prod_subtype (fun j => j = i)
      (fun j => (Q j).weight (x j))
    rw [Fintype.prod_subsingleton _ ⟨i,rfl⟩] at hh
    exact hh.symm
  simp only [expect, pi]
  rw [← (Equiv.piSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [hprod]
  have hh : (∏ j : {j // j ≠ i}, (Q j).weight
      ((Equiv.piSplitAt i α).symm (a,rest) j)) =
      ∏ j : {j // j ≠ i}, (Q j).weight (rest j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [Equiv.piSplitAt_symm_apply, dite_eq_right j.property]
  rw [hh]
  simp only [Equiv.piSplitAt_symm_apply, dite_true]
  ring

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

private theorem delta_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    (x y : (i : ι) → α i) :
    (∏ i, delta (x i) (y i)) = delta x y := by
  classical
  by_cases h : x = y
  · subst y
    simp [delta]
  · have hn : ∃ i, x i ≠ y i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i,hi⟩ := hn
    rw [delta, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [delta,hi])

private theorem expand_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (H : ((i : ι) → α i) → ℝ)
    (x : (i : ι) → α i) : H x = ∑ y, H y * ∏ i, delta (x i) (y i) := by
  classical
  simp_rw [delta_pi]
  simp [delta]

private theorem expect_pi_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : (i : ι) → FiniteLaw (α i)) (φ : (i : ι) → α i → β i)
    (w : (i : ι) → α i → ℝ) (H : ((i : ι) → β i) → ℝ) :
    (pi P).expect (fun x => H (fun i => φ i (x i)) * ∏ i, w i (x i)) =
      ∑ y, H y * ∏ i, (P i).expect (fun x => w i x * delta (φ i x) (y i)) := by
  classical
  have heq (x : (i : ι) → α i) :
      H (fun i => φ i (x i)) * (∏ i, w i (x i)) =
        ∑ y, H y * ∏ i, (w i (x i) * delta (φ i (x i)) (y i)) := by
    rw [expand_pi H (fun i => φ i (x i)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.prod_mul_distrib]
    ring
  rw [(pi P).expect_congr heq]
  simp only [expect_fintype_sum, expect_mul_left]
  apply Finset.sum_congr rfl
  intro y _
  rw [expect_pi_product P (fun i x => w i x * delta (φ i x) (y i))]

/-- Tensorization of arbitrary signed one-coordinate changes. This permits
inserting a marked new branch at a single child without assuming the test
factors across the old children. -/
theorem expect_pi_weighted_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : (i : ι) → FiniteLaw (α i)) (Q : (i : ι) → FiniteLaw (β i))
    (φ : (i : ι) → α i → β i) (w : (i : ι) → α i → ℝ) (v : (i : ι) → β i → ℝ)
    (h : ∀ i (g : β i → ℝ), (P i).expect (fun x => w i x * g (φ i x)) =
      (Q i).expect (fun y => v i y * g y)) (H : ((i : ι) → β i) → ℝ) :
    (pi P).expect (fun x => H (fun i => φ i (x i)) * ∏ i, w i (x i)) =
      (pi Q).expect (fun y => H y * ∏ i, v i (y i)) := by
  rw [expect_pi_expand P φ w H, expect_pi_expand Q (fun _ y => y) v H]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact h i (fun x => delta x (y i))

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw

theorem expect_pi_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : (i : ι) → FiniteLaw (α i))
    (i : ι) (f : α i → ℝ) : (pi P).expect (fun x => f (x i)) = (P i).expect f := by
  erw [expect_pi_split P i]
  simp! only [Equiv.piSplitAt_symm_apply, dite_true, expect_const]

end DilutedSpinGlass.FiniteLaw

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

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Coordinatewise pushforwards tensorize even for tests that do not factor. -/
theorem Projects.pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    {P : (i : ι) → FiniteLaw (α i)} {Q : (i : ι) → FiniteLaw (β i)}
    {π : (i : ι) → α i → β i} (h : ∀ i, Projects (P i) (Q i) (π i)) :
    Projects (FiniteLaw.pi P) (FiniteLaw.pi Q) (fun x i => π i (x i)) := by
  intro f
  have hh := expect_pi_weighted_map P Q π (fun _ _ => 1) (fun _ _ => 1)
    (fun i g => by simpa only [one_mul] using h i g) f
  simpa only [Finset.prod_const_one,mul_one] using hh

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

theorem oldIndex_projects (N : ℕ) [NeZero N] :
    (indexLaw N).Projects FiniteLaw.uniform oldIndex := by
  intro f
  unfold indexLaw
  rw [FiniteLaw.expect_bind,FiniteLaw.uniform_expect,Fin.sum_univ_succ]
  simp only [oldIndex, Fin.cases_zero, Fin.cases_succ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  change ((FiniteLaw.uniform : FiniteLaw (Fin N)).expect f+
    ∑ i, (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun _ => f i))/(N+1) = _
  simp only [FiniteLaw.expect_const,FiniteLaw.uniform_expect,Fintype.card_fin]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : (N:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem newIndex_projects (N : ℕ) [NeZero N] :
    (indexLaw N).Projects FiniteLaw.uniform newIndex := by
  intro f
  simp only [indexLaw,FiniteLaw.expect_bind,newIndex,FiniteLaw.expect_const]

/-- The exact probability of changing a site is 1/(N+1). -/
theorem newIndex_probability (N : ℕ) [NeZero N] :
    (indexLaw N).expect (fun z => if z.1 = 0 then (1:ℝ) else 0) = 1/(N+1) := by
  calc
    _ = (FiniteLaw.uniform : FiniteLaw (Fin (N+1))).expect
        (fun j => if j = 0 then (1:ℝ) else 0) :=
      newIndex_projects N (fun j => if j = 0 then (1:ℝ) else 0)
    _ = _ := by rw [FiniteLaw.uniform_expect]; simp

lemma same_index_off_new {N : ℕ} (z : Fin (N+1) × Fin N) (hz : z.1 ≠ 0) :
    (oldIndex z).succ = newIndex z := by
  rcases z with ⟨j,i⟩
  induction j using Fin.cases with
  | zero => exact (hz rfl).elim
  | succ j => rfl

theorem expected_new_count (N p : ℕ) [NeZero N] :
    (FiniteLaw.pi (fun _ : Fin p => indexLaw N)).expect
      (fun z => ∑ j, if (z j).1 = 0 then (1:ℝ) else 0) = (p:ℝ)/(N+1) := by
  rw [FiniteLaw.expect_fintype_sum]
  have hm (j : Fin p) :
      (FiniteLaw.pi (fun _ : Fin p => indexLaw N)).expect
        (fun z => if (z j).1 = 0 then (1:ℝ) else 0) = 1/(N+1) := by
    exact (FiniteLaw.expect_pi_marginal (fun _ : Fin p => indexLaw N) j
      (fun z => if z.1 = 0 then (1:ℝ) else 0)).trans (newIndex_probability N)
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end DilutedSpinGlass.SizeCoupling
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualPrefix
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
variable {Ω : Type*} [Fintype Ω]

theorem abs_expect_le_expect_abs (P : FiniteLaw Ω) (f : Ω → ℝ) :
    |P.expect f| ≤ P.expect (fun x => |f x|) := by
  unfold expect
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul,abs_of_nonneg (P.nonneg x)])

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSpinMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
theorem abs_expect_sub_le {f g : Ω → ℝ} {C : ℝ} (h : ∀ x, |f x-g x| ≤ C) :
    |P.expect f-P.expect g| ≤ C := by
  rw [← expect_sub]
  exact P.abs_expect_le h
end DilutedSpinGlass.FiniteLaw

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_IntegralError
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

lemma integrate_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g E : X → ℝ} (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hE : Integrable E μ) (h : ∀ᵐ x ∂μ,|f x-g x|≤E x) :
    Integrable f μ ∧ |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)|≤∫ x,E x ∂μ := by
  have hd : Integrable (fun x => f x-g x) μ := hE.mono' (hf.sub hg.aestronglyMeasurable) (by simpa only [Real.norm_eq_abs] using h)
  have hfi : Integrable f μ := by simpa only [Pi.add_def,sub_add_cancel] using hd.add hg
  refine ⟨hfi,?_⟩
  rw [← integral_sub hfi hg]
  calc
    _ ≤ ∫ x,|f x-g x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x-g x)
    _ ≤ _ := integral_mono_ae hd.abs hE h

end DilutedSpinGlass

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TerminalMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω Λ A : Type} [Fintype Ω] [Fintype Λ] [Fintype A]

lemma expMoment_bind_one (P : FiniteLaw Ω) (Q : FiniteLaw A) (F : Ω×A → ℝ) :
    (P.bind (fun _ => Q)).expMoment 1 F =
      Q.expect (fun a => P.expMoment 1 (fun s => F (s,a))) := by
  unfold expMoment
  rw [expect_bind]
  simp only [one_mul,expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma logMean_bind_one_congr (P : FiniteLaw Ω) (R : FiniteLaw Λ) (Q : FiniteLaw A)
    (F : Ω×A → ℝ) (G : Λ×A → ℝ)
    (h : ∀ a, P.expMoment 1 (fun s => F (s,a)) = R.expMoment 1 (fun s => G (s,a))) :
    (P.bind (fun _ => Q)).logMean 1 F = (R.bind (fun _ => Q)).logMean 1 G := by
  simp only [logMean,div_one,expMoment_bind_one]
  rw [show (fun a => P.expMoment 1 (fun s => F (s,a))) =
    (fun a => R.expMoment 1 (fun s => G (s,a))) from funext h]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ A : Type} [Fintype Ω] [Fintype Λ] [Fintype A]

/-- Equality of the genuine final-spin marginal propagates through every
auxiliary conditional power mean. The only required endpoint is m_L=1. -/
lemma terminal_marginal_congr (L : ℕ) (a : Ω) (b : Λ) (P : FiniteLaw Ω) (R : FiniteLaw Λ)
    (U : KernelTower A (L+1)) (m : Fin (L+1) → ℝ) (hm : m (Fin.last L)=1)
    (F : Ω → FinitePath A (L+1) → ℝ) (G : Λ → FinitePath A (L+1) → ℝ)
    (h : ∀ y, P.expMoment 1 (fun s => F s y) = R.expMoment 1 (fun s => G s y)) :
    backwardLog (L+1) (prod (L+1) (terminalTower a P L) U) m
      (fun y => F (terminalState L (pathFst (L+1) y)) (pathSnd (L+1) y)) =
    backwardLog (L+1) (prod (L+1) (terminalTower b R L) U) m
      (fun y => G (terminalState L (pathFst (L+1) y)) (pathSnd (L+1) y)) := by
  induction L with
  | zero =>
    change (P.bind (fun _ => U.1)).logMean (m 0) (fun z => F z.1 (z.2,())) =
      (R.bind (fun _ => U.1)).logMean (m 0) (fun z => G z.1 (z.2,()))
    change m 0=1 at hm
    rw [hm]
    exact FiniteLaw.logMean_bind_one_congr P R U.1 _ _ (fun u => h (u,()))
  | succ L ih =>
    change ( (FiniteLaw.point a).bind (fun _ => U.1)).logMean (m 0)
      (fun z => backwardLog (L+1) (prod (L+1) (terminalTower a P L) (U.2 z.2))
        (fun i => m i.succ)
        (fun y => F (terminalState L (pathFst (L+1) y)) (z.2,pathSnd (L+1) y))) =
      ((FiniteLaw.point b).bind (fun _ => U.1)).logMean (m 0)
      (fun z => backwardLog (L+1) (prod (L+1) (terminalTower b R L) (U.2 z.2))
        (fun i => m i.succ)
        (fun y => G (terminalState L (pathFst (L+1) y)) (z.2,pathSnd (L+1) y)))
    unfold FiniteLaw.logMean FiniteLaw.expMoment
    rw [FiniteLaw.expect_bind,FiniteLaw.expect_bind]
    simp only [FiniteLaw.expect_point]
    congr 1
    congr 1
    apply congrArg (FiniteLaw.expect U.1)
    funext u
    congr 1
    congr 1
    exact ih (U.2 u) (fun i => m i.succ) hm (fun s y => F s (u,y)) (fun s y => G s (u,y))
      (fun y => h (u,y))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpinMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma uniform_cons_expect (N : ℕ) (F : (Fin (N+1) → Spin) → ℝ) :
    (uniform : FiniteLaw (Fin (N+1) → Spin)).expect F =
      (uniform : FiniteLaw (Fin N → Spin)).expect (fun σ =>
        (uniform : FiniteLaw Spin).expect (fun ε => F (Fin.cons ε σ))) := by
  rw [uniform_expect,uniform_expect]
  simp_rw [uniform_expect]
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp F]
  simp only [Fintype.sum_prod_type,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,← Finset.sum_div,Fin.consEquiv,Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  push_cast
  rw [pow_succ]
  ring

lemma exp_logMean_one (P : FiniteLaw Spin) (F : Spin → ℝ) :
    Real.exp (P.logMean 1 F) = P.expect (fun ε => Real.exp (F ε)) := by
  rw [logMean,div_one,Real.exp_log (expMoment_pos P 1 F)]
  simp only [expMoment,one_mul]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ] {A : I → Type} [∀ i,Fintype (A i)]
    {k L N : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] in
lemma mark_eq_pathMap (roots : Fin k → I) (j : Fin k) (n : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) n) :
    mark j n y = pathMap (fun a : Row (A := A) roots => a j) n (pathSnd n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (y.1.2 j,mark j n y.2) = (y.1.2 j,pathMap _ n (pathSnd n y.2))
    rw [ih]

lemma terminalRoot_eq_backward (a : Ω) (P : FiniteLaw Ω)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (E : Ω → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ) :
    terminalRoot a P Q m E roots ψ =
      backwardLog (L+1) (prod (L+1) (terminalTower a P L)
        (markPrior (L+1) (fun d => FiniteLaw.pi (fun j => Q (roots j) d)))) m
        (fun y => E (terminalState L (pathFst (L+1) y))+
          ∑ j,Real.log (ψ (roots j) (terminalState L (pathFst (L+1) y))
            (pathMap (fun a : Row (A := A) roots => a j) (L+1) (pathSnd (L+1) y)))) := by
  simp only [terminalRoot,root,tower_eq_prod]
  congr 1
  funext y
  simp only [HeterogeneousMarks.logWeight,physical_eq_fst,mark_eq_pathMap]

lemma terminalRoot_marginal (a : Ω) (b : Λ) (P : FiniteLaw Ω) (R : FiniteLaw Λ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : Ω → ℝ) (G : Λ → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ)
    (φ : (i : I) → Λ → FinitePath (A i) (L+1) → ℝ)
    (h : ∀ y : FinitePath (Row (A := A) roots) (L+1),
      P.expMoment 1 (fun s => E s+∑ j, Real.log (ψ (roots j) s
        (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))) =
      R.expMoment 1 (fun s => G s+∑ j, Real.log (φ (roots j) s
        (pathMap (fun a : Row (A := A) roots => a j) (L+1) y)))) :
    terminalRoot a P Q m E roots ψ = terminalRoot b R Q m G roots φ := by
  rw [terminalRoot_eq_backward,terminalRoot_eq_backward]
  let U : KernelTower (Row (A := A) roots) (L+1) :=
    markPrior (L+1) (fun d => FiniteLaw.pi (fun j => Q (roots j) d))
  let F : Ω → FinitePath (Row (A := A) roots) (L+1) → ℝ := fun s y =>
    E s+∑ j, Real.log (ψ (roots j) s (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))
  let G' : Λ → FinitePath (Row (A := A) roots) (L+1) → ℝ := fun s y =>
    G s+∑ j, Real.log (φ (roots j) s (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))
  exact terminal_marginal_congr L a b P R U m hm F G' h

/-- Exact new-spin marginalization at the final exponent1. -/
lemma terminalRoot_spin_marginal
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ) (G : (Fin (N+1) → Spin) → ℝ)
    (roots : Fin k → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+G σ) roots (fun i σ a => ψ i (fun j => σ j.succ) a) =
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m
      (fun σ => E σ+(FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun ε => G (Fin.cons ε σ))) roots ψ := by
  apply terminalRoot_marginal _ _ _ _ Q m hm
  intro a
  unfold FiniteLaw.expMoment
  simp only [one_mul]
  rw [FiniteLaw.uniform_cons_expect]
  apply FiniteLaw.expect_congr
  intro σ
  simp only [Fin.cons_succ]
  let c := ∑ j,Real.log (ψ (roots j) σ (pathMap (fun a : Row (A := A) roots => a j) (L+1) a))
  change (FiniteLaw.uniform : FiniteLaw Spin).expect (fun ε => Real.exp (E σ+G (Fin.cons ε σ)+c)) =
    Real.exp (E σ+(FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun ε => G (Fin.cons ε σ))+c)
  simp_rw [Real.exp_add]
  rw [FiniteLaw.expect_mul_right,FiniteLaw.expect_mul_left,FiniteLaw.exp_logMean_one]

end DilutedSpinGlass.HeterogeneousMarks

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
namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower SizeCoupling
open scoped BigOperators
variable {I : Type} {A : I → Type} [∀ i,Fintype (A i)] {N k L : ℕ} [NeZero N]

omit [NeZero N] in
/-- Move only perturbation sites off the added spin, leaving energy and all
auxiliary mark labels and count laws unchanged. -/
lemma terminalRoot_mark_sites
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (E : (Fin (N+1) → Spin) → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {D : ℝ} (hψ : ∀ i s a,|Real.log (ψ i s a)|≤D)
    (z : Fin k → Fin (N+1) × Fin N) :
    |terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id
        (fun j σ a => ψ (roots j) (σ (newIndex (z j))) a) -
      terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id
        (fun j σ a => ψ (roots j) (σ (oldIndex (z j)).succ) a)| ≤
      2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0) := by
  have h := root_factor_stability (terminalTower (fun _ : Fin (N+1) => false)
    FiniteLaw.uniform L) (fun j : Fin k => Q (roots j)) m hm
    (fun y => E (terminalState L y)) id
    (fun j y a => ψ (roots j) (terminalState L y (newIndex (z j))) a)
    (fun j y a => ψ (roots j) (terminalState L y (oldIndex (z j)).succ) a)
    (fun j => if (z j).1=0 then 2*D else 0) (by
      intro j y a
      by_cases hj : (z j).1=0
      · simp only [hj,↓reduceIte]
        have h1 := hψ (roots j) (terminalState L y (newIndex (z j))) a
        have h2 := hψ (roots j) (terminalState L y (oldIndex (z j)).succ) a
        exact (abs_sub _ _).trans (by linarith)
      · simp only [hj,↓reduceIte,same_index_off_new (z j) hj,sub_self,abs_zero,le_refl])
  have he : (∑ j : Fin k,if (z j).1=0 then 2*D else 0) =
      2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0) := by
    simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero]
  exact h.trans_eq he

lemma terminalRoot_mark_site_expect
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (E : (Fin (N+1) → Spin) → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {D : ℝ} (hψ : ∀ i s a,|Real.log (ψ i s a)|≤D) :
    |(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j)) a)) -
      (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j).succ) a))| ≤
      2*D*k/(N+1) := by
  let R := FiniteLaw.pi (fun _ : Fin k => indexLaw N)
  have hn := FiniteLaw.Projects.pi (fun _ : Fin k => newIndex_projects N)
  have ho := FiniteLaw.Projects.pi (fun _ : Fin k => oldIndex_projects N)
  rw [← hn (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
      (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j)) a)),
    ← ho (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
      (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j).succ) a)),
    ← FiniteLaw.expect_sub]
  calc
    _ ≤ R.expect (fun z => |terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (newIndex (z j))) a)-
      terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (oldIndex (z j)).succ) a)|) :=
      FiniteLaw.abs_expect_le_expect_abs R _
    _ ≤ R.expect (fun z => 2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0)) :=
      R.expect_mono (terminalRoot_mark_sites Q m hm E roots ψ hψ)
    _ = _ := by rw [FiniteLaw.expect_mul_left,expected_new_count]; ring

end DilutedSpinGlass.HeterogeneousMarks

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityTrialIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {I : Type} {A : I → Type} [∀ i,Fintype (A i)] {N k p l L : ℕ}

lemma terminalRoot_cavity_marginal
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (roots : Fin l → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) roots
      (fun i σ z => ψ i (fun v => σ v.succ) z) =
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m
      (fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a))) roots ψ := by
  have he : (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+h*spin (σ 0)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) =
      (fun σ => E (fun i => σ i.succ)+(h*spin (σ 0)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))) := by
    funext σ; ring
  rw [he,terminalRoot_spin_marginal Q m hm]
  congr 1
  funext σ
  congr 1
  simp only [Fin.cons_succ,Fin.cons_zero]
  simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.uniform_expect,
    Fintype.card_bool,Nat.cast_ofNat,cavitySiteEnergy]

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkMeanProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N J k L : ℕ}

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma locatedTerminalRoot_bound
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (a : RootPath (I×Fin J) k) :
    |locatedTerminalRoot Q m ψ site E a|≤‖E‖+D*k := by
  unfold locatedTerminalRoot terminalRoot
  apply root_uniform_bound (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I×Fin J => Q i.1) m hm _ (rootArray k a) _ (B := ‖E‖) (C := D)
      (hf := fun i _ b => hf i.1 _ b)
  intro y
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma locatedTerminalRoot_pullback
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ) (a : RootPath (I×Fin J) k) :
    locatedTerminalRoot Q m ψ site E a =
      terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
        (fun j : Fin k => Q (rootArray k a j).1) m E id
        (fun j σ b => ψ (rootArray k a j).1 (σ (site (rootArray k a j).2)) b) := by
  unfold locatedTerminalRoot terminalRoot
  exact (root_pullback (fun j : Fin k => rootArray k a j) id
    (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I×Fin J => Q i.1) m _ _).symm

lemma integral_locatedTerminalRoot [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
      ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))=
      ∫ a : Fin k → I,(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))).expect
        (fun sites => terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
          (fun j : Fin k => Q (a j)) m E id (fun j σ b => ψ (a j) (σ (site (sites j))) b))
        ∂Measure.pi (fun _ : Fin k => ν) := by
  simp_rw [locatedTerminalRoot_pullback]
  have he : FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin J)) := by
    apply FiniteLaw.ext
    intro a
    simp [FiniteLaw.pi,FiniteLaw.uniform]
  rw [he]
  apply integral_root_prod_finite ν k
    (fun z : (Fin k → I) × (Fin k → Fin J) => terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
      (fun j : Fin k => Q (z.1 j)) m E id (fun j σ b => ψ (z.1 j) (σ (site (z.2 j))) b))
    (measurable_of_countable _) (B := ‖E‖+D*k)
  intro z
  unfold terminalRoot
  apply root_uniform_bound (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun j : Fin k => Q (z.1 j)) m hm _ id _ (B := ‖E‖) (C := D)
      (hf := fun j y b => hf (z.1 j) _ b)
  intro y
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)

lemma terminalMean_count_integral [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    terminalMean ν s Q m ψ site E =
      ∫ k,∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
        ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))) ∂poissonMeasure s := by
  apply integral_familyLaw (poissonMeasure s) (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
  exact familyLaw_integrable_bound (poissonMeasure s)
    (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
    ((integrable_const ‖E‖).add ((poisson_integrable_count s).const_mul D))
    (fun k a => locatedTerminalRoot_bound Q m hm ψ site E hf a)

/-- The original Poisson marked system may move mark sites off the added
spin at cost exactly twice the mark amplitude times its expected new-site count. -/
lemma terminalMean_mark_projection [NeZero N]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin (N+1) → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |terminalMean ν s Q m ψ (id : Fin (N+1) → Fin (N+1)) E-
      terminalMean ν s Q m ψ (Fin.succ : Fin N → Fin (N+1)) E|≤2*D*s/(N+1) := by
  have hx (J : ℕ) [NeZero J] (site : Fin J → Fin (N+1)) (k : ℕ) :
      Integrable (fun a : Fin k → I =>
        (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (a j)) m E id (fun j σ b => ψ (a j) (σ (site (sites j))) b)))
        (Measure.pi (fun _ : Fin k => ν)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (‖E‖+D*k)
    apply ae_of_all
    intro a
    simp only [Real.norm_eq_abs]
    apply FiniteLaw.abs_expect_le
    intro sites
    unfold terminalRoot
    apply root_uniform_bound (terminalTower (fun _ : Fin (N+1) => false) FiniteLaw.uniform L)
      (fun j : Fin k => Q (a j)) m hm _ id _ (B := ‖E‖) (C := D)
        (hf := fun j y b => hf (a j) _ b)
    intro y
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)
  have hi (J : ℕ) [NeZero J] (site : Fin J → Fin (N+1)) :
      Integrable (fun k => ∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
        ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J)))) (poissonMeasure s) := by
    apply poisson_average_integrable s _
    intro k
    exact abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a)
  rw [terminalMean_count_integral ν s Q m hm ψ id E hf,
    terminalMean_count_integral ν s Q m hm ψ Fin.succ E hf,← integral_sub (hi (N+1) id) (hi N Fin.succ)]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ k : ℕ,2*D*k/(N+1) ∂poissonMeasure s := by
      apply integral_mono ((hi (N+1) id).sub (hi N Fin.succ)).abs
        ((((poisson_integrable_count s).const_mul (2*D)).div_const (N+1)))
      intro k
      simp only [Pi.sub_apply]
      rw [integral_locatedTerminalRoot ν Q m hm ψ id E hf,
        integral_locatedTerminalRoot ν Q m hm ψ Fin.succ E hf,← integral_sub (hx (N+1) id k) (hx N Fin.succ k)]
      exact abs_integral_le_bound (fun a => terminalRoot_mark_site_expect Q m hm E a ψ hf)
    _ = _ := by rw [integral_div,integral_const_mul,poisson_mean]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TerminalMeanCavity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

omit [Countable I] [MeasurableSingletonClass I] in
lemma terminalMean_cavity_marginal [NeZero N]
    (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalMean ν s Q m ψ Fin.succ
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) =
    terminalMean ν s Q m ψ id
      (fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a))) := by
  unfold terminalMean
  apply integral_congr_ae
  filter_upwards [] with a
  exact terminalRoot_cavity_marginal (fun i : I×Fin N => Q i.1) m hm E
    (rootArray a.1 a.2) (fun i σ b => ψ i.1 (σ i.2) b) θ h j

omit [Countable I] [MeasurableSingletonClass I] in
lemma averagedEnergyRoot_eq_terminalMean [NeZero N]
    (ξ : Measure Y) (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin N → Spin) → ℝ) :
    averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1)
      m field (locatedFactor ψ) E =
      ∫ h,terminalMean ν s Q m ψ id
        (fun σ => E σ+∑ i,field (rootArray N h i)*spin (σ i)) ∂rootLaw N (fun _ => ξ) := rfl

lemma integrable_locatedTerminalRoot [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    Integrable (fun a : Sigma (RootPath (I×Fin J)) => locatedTerminalRoot Q m ψ site E a.2)
      (compoundRootLaw (ν.prod (finiteUniform (Fin J))) s) := by
  exact familyLaw_integrable_bound (poissonMeasure s)
    (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
    ((integrable_const ‖E‖).add ((poisson_integrable_count s).const_mul D))
    (fun k a => locatedTerminalRoot_bound Q m hm ψ site E hf a)

lemma terminalMean_bound [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |terminalMean ν s Q m ψ site E|≤‖E‖+D*s := by
  rw [terminalMean_count_integral ν s Q m hm ψ site E hf]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ k : ℕ,‖E‖+D*k ∂poissonMeasure s := by
      apply integral_mono
      · exact (poisson_average_integrable s _
          (fun k => abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a))).abs
      · exact (integrable_const _).add ((poisson_integrable_count s).const_mul D)
      · intro k
        exact abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a)
    _ = _ := by
      rw [integral_add (integrable_const _) ((poisson_integrable_count s).const_mul D),
        integral_const_mul,poisson_mean]
      simp

lemma terminalMean_lipschitz [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    LipschitzWith 1 (terminalMean ν s Q m ψ site) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,terminalMean]
  rw [← integral_sub (integrable_locatedTerminalRoot ν s Q m hm ψ site E hf)
    (integrable_locatedTerminalRoot ν s Q m hm ψ site F hf)]
  apply abs_integral_le_bound
  intro a
  apply root_base_stability _ (fun i : I×Fin J => Q i.1) m hm
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (terminalState L y)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TerminalMeanField
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

lemma measurable_fieldEnergy (field : Y → ℝ) (hh : Measurable field) :
    Measurable (fieldEnergy (N := N) field) := by
  apply Measurable.of_eval
  intro σ
  exact Finset.measurable_sum _ (fun i _ => (hh.comp (measurable_rootArray N i)).mul_const _)

omit [MeasurableSpace Y] in
lemma fieldEnergy_bound (field : Y → ℝ) {H : ℝ} (hh : ∀ y,|field y|≤H)
    (h : RootPath Y N) (σ : Fin N → Spin) : |fieldEnergy field h σ|≤H*N := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin N,H := Finset.sum_le_sum (fun _ _ => by
      rw [abs_mul,abs_spin,mul_one]; exact hh _)
    _ = _ := by simp [mul_comm]

omit [MeasurableSpace Y] in
lemma fieldEnergy_norm (field : Y → ℝ) {H : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (h : RootPath Y N) : ‖fieldEnergy field h‖≤H*N := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hH (Nat.cast_nonneg N))).mpr
  intro σ
  simpa only [Real.norm_eq_abs] using fieldEnergy_bound field hh h σ

omit [MeasurableSpace Y] in
lemma fieldEnergy_cons (field : Y → ℝ) (h : Y×RootPath Y N) (σ : Fin (N+1) → Spin) :
    fieldEnergy field h σ=field h.1*spin (σ 0)+fieldEnergy field h.2 (fun i => σ i.succ) := by
  simp [fieldEnergy,Fin.sum_univ_succ,rootArray]

lemma terminalMean_field_integrable [NeZero J]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    Integrable (fun h => terminalMean ν s Q m ψ site (E+fieldEnergy field h)) (rootLaw N (fun _ => ξ)) := by
  apply Integrable.of_bound
    ((terminalMean_lipschitz ν s Q m hm ψ site hf).continuous.measurable.comp
      (measurable_const.add (measurable_fieldEnergy field hhm))).aestronglyMeasurable
    (‖E‖+H*N+D*s)
  filter_upwards [] with h
  change |terminalMean ν s Q m ψ site (E+fieldEnergy field h)|≤_
  calc
    _ ≤ ‖E+fieldEnergy field h‖+D*s := terminalMean_bound ν s Q m hm ψ site _ hf
    _ ≤ (‖E‖+‖fieldEnergy field h‖)+D*s := by have := norm_add_le E (fieldEnergy field h); linarith
    _ ≤ _ := by have := fieldEnergy_norm field hH hh h; linarith

lemma averagedEnergyRoot_mark_projection [NeZero N]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin (N+1) → Spin) → ℝ)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s (fun i : I×Fin (N+1) => Q i.1)
      m field (locatedFactor ψ) E-
      (∫ h,terminalMean ν s Q m ψ Fin.succ (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))|≤
        2*D*s/(N+1) := by
  let : IsProbabilityMeasure (rootLaw (N+1) (fun _ => ξ)) := rootLawProbability _ _
  rw [averagedEnergyRoot_eq_terminalMean]
  change |(∫ h,terminalMean ν s Q m ψ id (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))-
    (∫ h,terminalMean ν s Q m ψ Fin.succ (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))|≤_
  rw [← integral_sub (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm id E hH hh hf)
    (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm Fin.succ E hH hh hf)]
  exact abs_integral_le_bound (fun _ => terminalMean_mark_projection ν s Q m hm ψ _ hf)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalNewSpin
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N k p L : ℕ} [NeZero N]

lemma newSpin_field_marginal
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin N → Spin) → ℝ)
    (θ : Fin k → InteractionSample p) (j : Fin k × Fin (p-1) → Fin N)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ h,terminalMean ν s Q m ψ Fin.succ
      ((fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
          ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))+fieldEnergy field h)
        ∂rootLaw (N+1) (fun _ => ξ)) =
      ∫ h,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
        (fun σ => E σ+cavitySiteEnergy θ (field h) (fun a => σ (j a))) ∂ξ := by
  rw [show rootLaw (N+1) (fun _ => ξ)=ξ.prod (rootLaw N (fun _ => ξ)) from rfl]
  rw [integral_prod _ (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm Fin.succ _ hH hh hf)]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [averagedEnergyRoot_eq_terminalMean]
  apply integral_congr_ae
  filter_upwards [] with h'
  have he : ((fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))+fieldEnergy field (h,h')) =
      (fun σ => (E+fieldEnergy field h') (fun i => σ i.succ)+field h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) := by
    funext σ
    simp only [Pi.add_apply,fieldEnergy_cons]
    ring
  rw [he,terminalMean_cavity_marginal ν s Q m hend]
  congr 1
  funext σ
  change (E σ+fieldEnergy field h' σ)+_=(E σ+_)+fieldEnergy field h' σ
  ring

/-- Removing marks on the new site and then summing out that spin gives the
actual cavity-site root, with precisely the O(s/N) projection error. -/
lemma averagedEnergyRoot_newSpin
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin N → Spin) → ℝ)
    (θ : Fin k → InteractionSample p) (j : Fin k × Fin (p-1) → Fin N)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
      (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
      (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) -
      (∫ h,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
        (fun σ => E σ+cavitySiteEnergy θ (field h) (fun a => σ (j a))) ∂ξ)|≤2*D*s/(N+1) := by
  rw [← newSpin_field_marginal ξ ν s Q m hm hend ψ field hhm E θ j hH hh hf]
  exact averagedEnergyRoot_mark_projection ξ ν s Q m hm ψ field hhm _ hH hh hf

end DilutedSpinGlass.HeterogeneousMarks

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

lemma measurable_cavityArrayValue (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (E : (Fin N → Spin) → ℝ) :
    Measurable (cavityArrayValue (k := k) ξ theta field F E) := by
  apply FiniteLaw.measurable_expect
  intro j
  exact (hF.measurable.comp (measurable_cavityArrayEnergy theta field hθ hh E j)).stronglyMeasurable.integral_prod_right'.measurable

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
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

lemma compound_sample_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) (hVi : Integrable V μ) :
    Integrable (fun z : Sigma (RootPath X) => F (∑ i,V (rootArray z.1 z.2 i)))
      (compoundRootLaw μ r) := by
  have : IsProbabilityMeasure (Measure.map V μ) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hiV : Integrable id (Measure.map V μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hV.aemeasurable).mpr hVi
  have hi := integrable_lipschitz_of_id (compoundPoisson r (Measure.map V μ))
    (compoundPoisson_integrable_id r _ hiV) hF
  rw [← map_compoundRoot_energy μ V hV r] at hi
  exact (integrable_map_measure hF.continuous.aestronglyMeasurable
    (measurable_compound_sample V hV).aemeasurable).mp hi

lemma integral_compound_sample (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) (hVi : Integrable V μ) :
    (∫ E,F E ∂compoundPoisson r (Measure.map V μ))=
      ∫ k,∫ z : RootPath X k,F (∑ i,V (rootArray k z i)) ∂rootLaw k (fun _ => μ) ∂poissonMeasure r := by
  rw [← map_compoundRoot_energy μ V hV r,
    integral_map (measurable_compound_sample V hV).aemeasurable hF.continuous.aestronglyMeasurable]
  exact integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k z => F (∑ i,V (rootArray k z i)))
    (fun k => by
      apply hF.continuous.measurable.comp
      apply Finset.measurable_sum
      intro i _
      exact hV.comp (measurable_rootArray k i))
    (compound_sample_integrable μ V hV r hF hVi)

lemma integral_compound_finite_sample {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (V : X×J → E) (hV : Measurable V)
    {C : ℝ} (hVb : ∀ x,‖V x‖≤C) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) :
    (∫ E,F E ∂compoundPoisson r (Measure.map V (μ.prod (finiteUniform J))))=
      ∫ k,∫ z : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → J)).expect
        (fun j => F (∑ i,V (z i,j i))) ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r := by
  rw [integral_compound_sample (μ.prod (finiteUniform J)) V hV r hF
    (Integrable.of_bound hV.aestronglyMeasurable C (ae_of_all _ hVb))]
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_root_prod_finite μ k (fun z => F (∑ i,V (z.1 i,z.2 i)))
  · apply hF.continuous.measurable.comp
    exact Finset.measurable_sum _ (fun i _ => hV.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))
  · intro z
    have hn : ‖∑ i : Fin k,V (z.1 i,z.2 i)‖ ≤ C*k := by
      calc
        _ ≤ ∑ i : Fin k,‖V (z.1 i,z.2 i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin k,C := Finset.sum_le_sum (fun _ _ => hVb _)
        _ = _ := by simp [mul_comm]
    have hh := hF.dist_le_mul (∑ i,V (z.1 i,z.2 i)) 0
    simp only [dist_eq_norm,sub_zero,Real.norm_eq_abs] at hh
    calc
      _ = |F (∑ i,V (z.1 i,z.2 i))-F 0+F 0| := by rw [sub_add_cancel]
      _ ≤ |F (∑ i,V (z.1 i,z.2 i))-F 0|+|F 0| := abs_add_le _ _
      _ ≤ (c:ℝ)*(C*k)+|F 0| := add_le_add (hh.trans
        (mul_le_mul_of_nonneg_left hn c.coe_nonneg)) le_rfl

end DilutedSpinGlass

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

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot HeterogeneousMarks
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N q : ℕ} [NeZero N]

lemma cavity_poisson_bridge
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    {H C B δ : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} {G : ((Fin (N+1) → Spin) → ℝ) → ℝ}
    (hF : Continuous F) (hFb : ∀ v,|F v|≤‖v‖+B) (hG : LipschitzWith 1 G)
    (E : (Fin N → Spin) → ℝ) (r : ℝ≥0)
    (he : ∀ k (z : Fin k → X) (j : Fin k → Fin q → Fin N),
      |G (fun σ => E (fun i => σ i.succ)+∑ a,(theta (z a)).1
        (appendSpin (fun b => σ (j a b).succ) (σ 0)))-
        ∫ h,F (cavityArrayEnergy theta field E j (z,h)) ∂ξ|≤δ) :
    |(∫ v,G (fun σ => E (fun i => σ i.succ)+v σ)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))))-
      (∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)|≤δ := by
  have hGs : LipschitzWith 1 (fun v : (Fin (N+1) → Spin) → ℝ => G (fun σ => E (fun i => σ i.succ)+v σ)) := by
    simpa only [mul_one,Function.comp_def,Pi.add_def] using
      hG.comp (isometry_add_left (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ))).lipschitz
  have hVb (z : X×(Fin q → Fin N)) : ‖newPotential theta z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1))
  rw [integral_compound_finite_sample μ (newPotential theta)
    (measurable_newPotential theta hθm) hVb r hGs]
  let f (k : ℕ) (z : Fin k → X) :=
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin q → Fin N)).expect
      (fun j => G (fun σ => E (fun i => σ i.succ)+∑ a,newPotential theta (z a,j a) σ))
  let g (k : ℕ) (z : Fin k → X) := cavityArrayValue ξ theta field F E z
  have hgm k : Measurable (g k) := measurable_cavityArrayValue ξ theta field hθm hhm hF E
  have hgb k z : |g k z|≤‖E‖+H+C*k+B := cavityArrayValue_bound ξ theta field hH hC hθ hh hFb E z
  have hgi k : Integrable (g k) (Measure.pi (fun _ : Fin k => μ)) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable _ (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hgb k z))
  have hfm k : Measurable (f k) := by
    apply FiniteLaw.measurable_expect
    intro j
    apply hG.continuous.measurable.comp
    apply Measurable.of_eval
    intro σ
    change Measurable (fun z : Fin k → X => E (fun i => σ i.succ)+∑ a,(theta (z a)).1 (appendSpin (fun b => σ (j a b).succ) (σ 0)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ => (hθm _).comp (measurable_pi_apply a)))
  have he' k z : |f k z-g k z|≤δ := by
    apply FiniteLaw.abs_expect_sub_le
    intro j
    exact he k z j
  have hb k : |(∫ z,f k z ∂Measure.pi (fun _ : Fin k => μ))-
      ∫ z,g k z ∂Measure.pi (fun _ : Fin k => μ)|≤δ := by
    have h := integrate_error (Measure.pi (fun _ : Fin k => μ))
      (hfm k).aestronglyMeasurable (hgi k) (integrable_const δ) (ae_of_all _ (he' k))
    simpa using h.2
  have hgI : Integrable (fun k => ∫ z,g k z ∂Measure.pi (fun _ : Fin k => μ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := ‖E‖+H+B) (B := C)
    intro k
    calc
      _ ≤ ‖E‖+H+C*k+B := abs_integral_le_bound (hgb k)
      _ = _ := by ring
  have h := integrate_error (poissonMeasure r) (measurable_of_countable _).aestronglyMeasurable
    hgI (integrable_const δ) (ae_of_all _ hb)
  simpa only [Pi.add_apply,Finset.sum_apply,Real.norm_eq_abs,integral_const,
    Measure.real,measure_univ,ENNReal.toReal_one,one_smul,f,g] using h.2

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
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_newSpin_poisson
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    |(∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
        (fun σ => E (fun i => σ i.succ)+v σ)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))))-
      (∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) E z
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)|≤2*D*s/(N+1) := by
  apply cavity_poisson_bridge μ ξ theta field hθm hhm hH hC hθ hh
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous
    (fun v => by
      simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i y a => hf i.1 _ a) v)
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)) E r
  intro k z j
  exact averagedEnergyRoot_newSpin ξ ν s Q m hm hend ψ field hhm E
    (fun a => theta (z a)) (fun a => j a.1 a.2) hH hh hf

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperRealEndpoint
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N q : ℕ} [NeZero N]

lemma cavity_old_average_error
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (θ : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (θ x).1 σ)) (hhm : Measurable field)
    {C H B δ : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ x,‖(θ x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (hFb : ∀ E,|F E|≤‖E‖+B)
    {G : ((Fin (N+1) → Spin) → ℝ) → ℝ} (hG : Continuous G) (r : ℝ≥0)
    (he : ∀ E,|(∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r
        (Measure.map (newPotential (N := N) θ) (μ.prod (finiteUniform (Fin q → Fin N)))))-
      cavityPoissonValue μ ξ θ field F r E|≤δ) :
    |(∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r
        (Measure.map (newPotential (N := N) θ) (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ θ field F r E ∂ρ)|≤δ := by
  let : IsProbabilityMeasure (Measure.map (newPotential (N := N) θ)
      (μ.prod (finiteUniform (Fin q → Fin N)))) := Measure.isProbabilityMeasure_map (measurable_newPotential θ hθm).aemeasurable
  have hgb (E : (Fin N → Spin) → ℝ) :
      |cavityPoissonValue μ ξ θ field F r E|≤‖E‖+(H+C*r+B) := by
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ θ field hH hC hθ hh hFb r E
  have hgi : Integrable (cavityPoissonValue μ ξ θ field F r) ρ :=
    (hρ.norm.add (integrable_const (H+C*r+B))).mono'
      (measurable_cavityPoissonValue μ ξ θ field hθm hhm hF r).aestronglyMeasurable
      (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hgb E))
  have hfm : AEStronglyMeasurable (fun E => ∫ v,G (liftOldEnergy E+v)
      ∂compoundPoisson r (Measure.map (newPotential (N := N) θ)
        (μ.prod (finiteUniform (Fin q → Fin N))))) ρ := by
    have hc : Continuous (fun z : ((Fin N → Spin) → ℝ)×((Fin (N+1) → Spin) → ℝ) =>
        G (liftOldEnergy z.1+z.2)) := hG.comp
      (((liftOldEnergy (N := N)).continuous.comp continuous_fst).add continuous_snd)
    exact hc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have h := integrate_error ρ hfm hgi (integrable_const δ) (ae_of_all _ he)
  simpa only [integral_const,probReal_univ,one_smul] using h.2

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavitySiteMean
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_old_new_compare_sat_oai
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) (liftOldEnergy E+v)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)|≤2*D*s/(N+1) := by
  apply cavity_old_average_error μ ξ ρ hρ theta field hθm hhm hC hH hθ hh
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous
    (B := H*N+D*s) _
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous r
  · intro E
    simpa only [cavityPoissonValue,liftOldEnergy,ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk,AddHom.coe_mk,Pi.add_def] using
      averagedEnergyRoot_newSpin_poisson μ ξ ν r s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf E
  · intro E
    simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
      (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i y a => hf i.1 _ a) E

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare_sat_oai := @OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare_sat_oai
