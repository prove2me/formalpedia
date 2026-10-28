-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.clippedPhysicalMean_reservoir_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:03:02.837996+00:00
-- url     : https://prove2.me/submissions/6823041a-90c5-4215-a098-f2171e5adb11

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section
-- module Solutions.OAIQ041_DS.Compat
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

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

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProducts
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTowers
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousMarks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_UniformIndexCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SizeSpinRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualPrefix
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSuperposition
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSpinMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_GeneralRootArrayLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem abs_spin (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_UniversalDictionary
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRegularSelection
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

noncomputable local instance fullRegularSelectionDecidableEq_ra7fbd9_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter _root_.MeasureTheory
open scoped NNReal Topology

lemma reservoirRate_le (α : ℝ≥0) (q N : ℕ) : reservoirRate α q N ≤ α*N := by
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr (by simp))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IntegralError
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
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionStability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundMoment
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundCoupling
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

lemma interaction_clip_symmetric {p : ℕ} (M : Model p) (C : ℝ)
    (hsym : ∀ e : Equiv.Perm (Fin p),IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => (clipSample C z).1)
      (fun z : InteractionSample p => fun s => (clipSample C z).1 (fun i => s (e i)))
      M.disorder.toMeasure M.disorder.toMeasure := by
  exact (hsym e).comp (show Measurable (fun f : (Fin p → Spin) → ℝ => fun s => clipReal C (f s)) from
    Measurable.of_eval (fun spin => (measurable_clipReal C).comp (measurable_pi_apply spin)))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RandomInsertion
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPhysicalMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperMoments
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePoissonSplit
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySplit
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityRateLimits
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

lemma appendSpin_castSucc {q : ℕ} (s : Fin q → Spin) (ε : Spin) (i : Fin q) :
    appendSpin (p := q+1) s ε i.castSucc = s i := by
  simp only [appendSpin,Nat.add_sub_cancel,Fin.val_castSucc,dite_eq_left i.isLt]
  rfl

lemma appendSpin_last {q : ℕ} (s : Fin q → Spin) (ε : Spin) :
    appendSpin (p := q+1) s ε (Fin.last q) = ε := by
  simp [appendSpin]

lemma cavityCoordinate_append {q : ℕ} (j : Fin (q+1)) (s : Fin q → Spin) (ε : Spin) :
    (fun l => appendSpin (p := q+1) s ε (cavityCoordinateEquiv j l)) = j.insertNth ε s := by
  funext l
  refine Fin.succAboveCases j ?_ (fun i => ?_) l
  · simp only [cavityCoordinateEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same,appendSpin_last]
  · simp only [cavityCoordinateEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_succAbove,appendSpin_castSucc]

/-- iid coordinate symmetry is sufficient for all one-new-index classes to
 have the exact same interaction as the last-coordinate cavity convention. -/
lemma cavity_coordinate_identDistrib {q : ℕ} {X : Type} [MeasurableSpace X]
    (μ : Measure X) (θ : X → Interaction (q+1))
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)), IdentDistrib θ
      (fun z s => θ z (fun l => s (e l))) μ μ)
    (j : Fin (q+1)) :
    IdentDistrib (fun z (v : (Fin q → Spin) × Spin) => θ z (appendSpin v.1 v.2))
      (fun z (v : (Fin q → Spin) × Spin) => θ z (j.insertNth v.2 v.1)) μ μ := by
  have h := (hsym (cavityCoordinateEquiv j)).comp
    (show Measurable (fun t : Interaction (q+1) => fun v : (Fin q → Spin) × Spin => t (appendSpin v.1 v.2)) by fun_prop)
  simpa only [Function.comp_def,cavityCoordinate_append] using h

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X E A B : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

lemma map_redundant_finite_mark (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X×(A×B) → E) (W : X×B → E) (hV : Measurable V) (hW : Measurable W)
    (h : ∀ a b,IdentDistrib (fun x => V (x,(a,b))) (fun x => W (x,b)) μ μ) :
    Measure.map V (μ.prod (finiteUniform (A×B))) = Measure.map W (μ.prod (finiteUniform B)) := by
  apply Measure.ext_of_charFunDual
  funext L
  suffices heq : charFunDual (Measure.map V (μ.prod (finiteUniform (A×B)))) L-1 =
      charFunDual (Measure.map W (μ.prod (finiteUniform B))) L-1 by exact sub_left_inj.mp heq
  rw [centered_finite_mark μ V hV,centered_finite_mark μ W hW]
  have he (a : A) (b : B) :
      (∫ x,Complex.exp ((L (V (x,(a,b))):ℂ)*Complex.I)-1 ∂μ)=
      (∫ x,Complex.exp ((L (W (x,b)):ℂ)*Complex.I)-1 ∂μ) := ((h a b).comp (show Measurable (fun v : E => Complex.exp ((L v:ℂ)*Complex.I)-1) by fun_prop)).integral_eq
  simp only [Fintype.sum_prod_type,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_prod,Nat.cast_mul]
  have hA : (Fintype.card A:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp only [mul_comm Complex.I]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkSiteCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonCountThinning
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CountBridgeTools
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoint
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integral_conv_increment (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    (∫ x,f x ∂(μ∗ν))-(∫ x,f x ∂μ)=∫ x,∫ y,f (x+y)-f x ∂ν ∂μ := by
  have hfi := integrable_lipschitz_of_id μ hμ hf
  have hfc := integrable_lipschitz_of_id (μ∗ν) (integrable_id_conv μ ν hμ hν) hf
  have hfp : Integrable (fun z : E×E => f (z.1+z.2)) (μ.prod ν) :=
    (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable (by fun_prop)).mp hfc
  rw [integral_conv hfc,← integral_sub hfp.integral_prod_left hfi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : Integrable (fun y => f (x+y)) ν := by
    apply integrable_lipschitz_of_id ν hν
    simpa only [mul_one,Function.comp_def] using hf.comp (isometry_add_left x).lipschitz
  rw [integral_sub hx (integrable_const _)]
  simp

/-- Exact old-system addition formula at the level of physical energy laws. -/
lemma compoundPoisson_increment (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    (∫ x,f x ∂compoundPoisson (r+s) μ)-(∫ x,f x ∂compoundPoisson r μ)=
      ∫ x,∫ y,f (x+y)-f x ∂compoundPoisson s μ ∂compoundPoisson r μ := by
  rw [compoundPoisson_add]
  exact integral_conv_increment _ _ (compoundPoisson_integrable_id r μ hμ)
    (compoundPoisson_integrable_id s μ hμ) hf

end DilutedSpinGlass

end

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
-- module Solutions.OAIQ041_DS.DilutedSpin_CountArrayBridge
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootCounts
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalCountLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionAlgebra
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PerturbedEnergyMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedEnergyRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityTrialIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoissonAlgebra
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkMeanProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMeanCavity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMeanField
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalNewSpin
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedRootBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySeparable
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSample
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_OneNewLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

omit [NeZero N] in
lemma spin_insertNth (j : Fin (q+1)) (i : Fin q → Fin N) (σ : Fin (N+1) → Spin) :
    (fun d => σ (j.insertNth (α := fun _ => Fin (N+1)) (0 : Fin (N+1)) (fun b => (i b).succ) d)) =
      j.insertNth (α := fun _ => Spin) (σ 0) (fun b => σ (i b).succ) := by
  funext d
  refine Fin.succAboveCases j ?_ (fun b => ?_) d <;> simp

lemma oneNew_markLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ))
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun x => (theta x).1)
      (fun x s => (theta x).1 (fun l => s (e l))) μ μ) :
    Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
        indexedPotential theta (z.1,z.2.1.insertNth (α := fun _ => Fin (N+1)) (0 : Fin (N+1)) (fun i => (z.2.2 i).succ)))
      (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))) =
    Measure.map (newPotential (N := N) theta) (μ.prod (finiteUniform (Fin q → Fin N))) := by
  apply map_redundant_finite_mark μ _ _
  · apply measurable_from_prod_countable_left
    intro b
    exact Measurable.of_eval (fun σ => by
      change Measurable (fun c => (theta c).1 (fun d => σ (b.1.insertNth (α := fun _ => Fin (N+1)) 0 (fun i => (b.2 i).succ) d)))
      exact hθ _)
  · exact measurable_newPotential theta hθ
  · intro j i
    have h := (cavity_coordinate_identDistrib μ (fun x => (theta x).1) hsym j).symm.comp
      (show Measurable (fun e : ((Fin q → Spin) × Spin) → ℝ =>
        fun σ : Fin (N+1) → Spin => e ((fun b => σ (i b).succ),σ 0)) by fun_prop)
    change IdentDistrib
      (fun x (σ : Fin (N+1) → Spin) => (theta x).1
        (fun d => σ (j.insertNth (α := fun _ => Fin (N+1)) 0 (fun b => (i b).succ) d)))
      (fun x (σ : Fin (N+1) → Spin) => (theta x).1 (appendSpin (fun b => σ (i b).succ) (σ 0))) μ μ
    simp only [spin_insertNth]
    exact h

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_RootIntegralOrder
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalCavitySplit
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
    (Measure.isProbabilityMeasure_map (measurable_indexedPotential (N := N) theta hθm).aemeasurable)
  rw [perturbedMean_energy_integral μ ξ ν r s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ]
  congr 1
  exact integral_averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s _
    (compoundPoisson_integrable_id r _ (integrable_indexedPotential μ theta hθm hC hθ))
    (fun i : I×Fin N => Q i.1) m hm field hhm (locatedFactor ψ) hh
    (fun i _ a => hψ i.1 _ a)

/-- The actual new system differs from its reservoir-plus-cavity energy law
only by the double-new-coordinate rate. All physical field and mark averages
are retained, with their original counts and sites. -/
lemma perturbedMean_cavity_split
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

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalCavityPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_OldEnergyEmbedding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
open scoped NNReal
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

lemma old_markLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measure.map (fun z : X×(Fin (q+1) → Fin N) =>
      indexedPotential theta (z.1,fun i => (z.2 i).succ))
      (μ.prod (finiteUniform (Fin (q+1) → Fin N)))=
    Measure.map (liftOldEnergy (N := N))
      (Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) := by
  rw [Measure.map_map (liftOldEnergy (N := N)).measurable (measurable_indexedPotential theta hθ)]
  rfl

lemma old_compoundLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (r : ℝ≥0) :
    compoundPoisson r (Measure.map (fun z : X×(Fin (q+1) → Fin N) =>
      indexedPotential theta (z.1,fun i => (z.2 i).succ))
      (μ.prod (finiteUniform (Fin (q+1) → Fin N))))=
    Measure.map (liftOldEnergy (N := N))
      (compoundPoisson r (Measure.map (indexedPotential theta)
        (μ.prod (finiteUniform (Fin (q+1) → Fin N))))) := by
  haveI : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) theta) (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) :=
    Measure.isProbabilityMeasure_map (measurable_indexedPotential (N := N) theta hθ).aemeasurable
  rw [old_markLaw μ theta hθ,compoundPoisson_map_linear]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityOldNewMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]
lemma cavityLaw_mean_eq (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ))
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun x => (theta x).1)
      (fun x s => (theta x).1 (fun l => s (e l))) μ μ)
    {C : ℝ} (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (r s : ℝ≥0) {F : ((Fin (N+1) → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F) :
    (∫ E,F E ∂(compoundPoisson r
      (Measure.map (fun z : X×(Fin (q+1) → Fin N) =>
        indexedPotential theta (z.1,fun i => (z.2 i).succ))
        (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
      compoundPoisson s (Measure.map (fun z : X×(Fin (q+1)×(Fin q → Fin N)) =>
        indexedPotential theta (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
        (μ.prod (finiteUniform (Fin (q+1)×(Fin q → Fin N)))))))=
    ∫ E,∫ v,F (liftOldEnergy E+v)
      ∂compoundPoisson s (Measure.map (newPotential (N := N) theta)
        (μ.prod (finiteUniform (Fin q → Fin N))))
      ∂compoundPoisson r (Measure.map (indexedPotential theta)
        (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) := by
  let μo := Measure.map (indexedPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin (q+1) → Fin N)))
  let μn := Measure.map (newPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin q → Fin N)))
  let : IsProbabilityMeasure μo := Measure.isProbabilityMeasure_map (measurable_indexedPotential (N := N) theta hθm).aemeasurable
  let : IsProbabilityMeasure μn := Measure.isProbabilityMeasure_map (measurable_newPotential theta hθm).aemeasurable
  have hio : Integrable id μo := integrable_indexedPotential μ theta hθm hC (fun x σ =>
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta x).1 σ : |(theta x).1 σ|≤‖(theta x).1‖).trans (hθ x))
  have hin : Integrable id μn := by
    apply (integrable_map_measure aestronglyMeasurable_id (measurable_newPotential theta hθm).aemeasurable).mpr
    apply Integrable.of_bound (measurable_newPotential theta hθm).aestronglyMeasurable C
    exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun _ =>
      (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1)))
  have hiO := compoundPoisson_integrable_id r μo hio
  have hiN := compoundPoisson_integrable_id s μn hin
  let ρo := Measure.map (liftOldEnergy (N := N)) (compoundPoisson r μo)
  let : IsProbabilityMeasure ρo := Measure.isProbabilityMeasure_map (liftOldEnergy (N := N)).measurable.aemeasurable
  have hiL : Integrable id ρo :=
    (integrable_map_measure aestronglyMeasurable_id (liftOldEnergy (N := N)).measurable.aemeasurable).mpr
      ((liftOldEnergy (N := N)).integrable_comp hiO)
  rw [old_compoundLaw μ theta hθm,oneNew_markLaw μ theta hθm hsym]
  change (∫ E,F E ∂(ρo ∗ compoundPoisson s μn))=_
  rw [integral_conv (integrable_lipschitz_of_id _ (integrable_id_conv _ _ hiL hiN) hF)]
  have hm : StronglyMeasurable (fun E : (Fin (N+1) → Spin) → ℝ =>
      ∫ v,F (E+v) ∂compoundPoisson s μn) :=
    (show StronglyMeasurable (Function.uncurry (fun E v : (Fin (N+1) → Spin) → ℝ => F (E+v))) from
      (hF.continuous.comp continuous_add).stronglyMeasurable).integral_prod_right
  exact integral_map (liftOldEnergy (N := N)).measurable.aemeasurable hm.aestronglyMeasurable

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRealEndpoint
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
      (μ.prod (finiteUniform (Fin q → Fin N)))) :=
    Measure.isProbabilityMeasure_map (measurable_newPotential θ hθm).aemeasurable
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
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySiteMean
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

lemma averagedEnergyRoot_old_new_compare
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

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalReservoirIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

/-- The actual finite-size physical increment at a common score intensity has
its reservoir/cavity representation, with only the repeated-new-site and
mark-location displacement errors. -/
lemma perturbedMean_reservoir_increment
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun x => (theta x).1)
      (fun x σ => (theta x).1 (fun i => σ (e i))) μ μ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) s-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ (α*N) s)-
      energyCavityIncrement (N := N) μ ξ ν α s theta field Q m ψ|≤
      C*cavityBadRate α q N+2*D*s/(N+1) := by
  let F := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
    (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
  let G := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
  let μo := Measure.map (indexedPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin (q+1) → Fin N)))
  let ρ := compoundPoisson (reservoirRate α q N) μo
  let : IsProbabilityMeasure μo :=
    (Measure.isProbabilityMeasure_map_iff (measurable_indexedPotential theta hθm).aemeasurable).mpr inferInstance
  have hθb : ∀ x σ,|(theta x).1 σ|≤C := fun x σ =>
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta x).1 σ : |(theta x).1 σ|≤‖(theta x).1‖).trans (hθ x)
  have hio : Integrable id μo := integrable_indexedPotential μ theta hθm hC hθb
  have hiρ : Integrable id ρ := compoundPoisson_integrable_id _ μo hio
  have hFl : LipschitzWith 1 F := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
    (locatedFactor ψ) hh (fun i _ a => hf i.1 _ a)
  have hGl : LipschitzWith 1 G := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
    (locatedFactor ψ) hh (fun i _ a => hf i.1 _ a)
  have hs := perturbedMean_cavity_split (N := N) μ ξ ν α s theta field hθm hhm Q m hm ψ hC hD hθb hh hf
  rw [cavityLaw_mean_eq μ theta hθm hsym hC hθ _ _ hGl] at hs
  have hn := averagedEnergyRoot_old_new_compare μ ξ ν ρ hiρ (oneNewRate α q N) s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  have ho := perturbedMean_averagedEnergyRoot (N := N) μ ξ ν (α*N) s theta field hθm hhm Q m hm ψ hC hD hθb hh hf
  have hb := compoundPoisson_increment (reservoirRate α q N) (α*N-reservoirRate α q N) μo hio hFl
  rw [add_tsub_cancel_of_le (reservoirRate_le α q N)] at hb
  have hFi : Integrable F ρ := integrable_lipschitz_of_id ρ hiρ hFl
  have hFb : ∀ E,|F E|≤‖E‖+(H*N+D*s) := by
    intro E
    simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
      (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i _ a => hf i.1 _ a) E
  have hCb : ∀ E,|cavityPoissonValue μ ξ theta field F (oneNewRate α q N) E|≤
      ‖E‖+(H+C*(oneNewRate α q N)+(H*N+D*s)) := by
    intro E
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ theta field hH hC hθ hh hFb
      (oneNewRate α q N) E
  have hCi : Integrable (cavityPoissonValue μ ξ theta field F (oneNewRate α q N)) ρ :=
    (hiρ.norm.add (integrable_const _)).mono'
      (measurable_cavityPoissonValue μ ξ theta field hθm hhm hFl.continuous _).aestronglyMeasurable
      (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hCb E))
  change |(_-_)-(Real.log 2+(∫ E,cavityPoissonValue μ ξ theta field F (oneNewRate α q N) E-F E ∂ρ)-
    (∫ E,∫ v,F (E+v)-F E ∂compoundPoisson (α*N-reservoirRate α q N) μo ∂ρ))|≤_
  rw [integral_sub hCi hFi,← hb,ho]
  have hhabs := (abs_add_le _ _).trans (add_le_add hs hn)
  dsimp only [F,G,ρ,μo] at *
  convert hhabs using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.cast_add,Nat.cast_one]
  congr 1
  ring

end DilutedSpinGlass.SizeCoupling

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GridIncrementSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

lemma scoreRate_real (N : ℕ) : (scoreRate N : ℝ)=scoreScale N := rfl

lemma clippedPhysicalMean_reservoir_bound_oai {q L N : ℕ} [NeZero N]
    (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (u : Spec L×ℕ → ℝ) :
    |(clippedPhysicalMean M C H (N+1) (scoreRate N) u-clippedPhysicalMean M C H N (scoreRate N) u)-
      clippedReservoirIncrement M C H N u| ≤ C*cavityBadRate M.alpha q N+2*scoreScale N/(N+1) := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  have ht z : ‖(clipSample (p := q+1) C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa [Real.norm_eq_abs] using clipSample_bound hC z σ)
  simpa [clippedPhysicalMean,clippedReservoirIncrement,mul_one,one_mul,scoreRate_real,Nat.cast_add,Nat.cast_one,NNReal.coe_mk,Subtype.coe_mk] using
    perturbedMean_reservoir_increment (N := N) M.disorder.toMeasure M.field.toMeasure (weights L)
      M.alpha (scoreRate N) (clipSample C) (clipReal H) hθm (measurable_clipReal H)
      (interaction_clip_symmetric M C hsym) (fun i : Spec L×ℕ => prior i.1)
      (gridExponents L) (gridExponents_pos L) (gridExponents_last L) (spinFactor direction anchor u)
      hH hC (by norm_num : (0:ℝ)≤1) ht (fun y => clipReal_bound hH y)
      (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.clippedPhysicalMean_reservoir_bound_oai := @OAI.DilutedSpinGlass.UniversalDictionary.clippedPhysicalMean_reservoir_bound_oai
