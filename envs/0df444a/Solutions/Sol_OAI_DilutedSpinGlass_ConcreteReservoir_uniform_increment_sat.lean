-- Prove2me | solution 1 for OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:13.597578+00:00
-- url     : https://prove2.me/submissions/27e904cf-50ce-4f5d-8d21-8f911fc092af

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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem Projects.logMean {P : FiniteLaw Ω} {Q : FiniteLaw Λ} {π : Ω → Λ}
    (h : Projects P Q π) (m : ℝ) (f : Λ → ℝ) :
    P.logMean m (fun x => f (π x)) = Q.logMean m f := by
  unfold FiniteLaw.logMean FiniteLaw.expMoment
  rw [h (fun y => Real.exp (m*f y))]

theorem Projects.bind {P : FiniteLaw Ω} {Q : FiniteLaw Λ} {π : Ω → Λ}
    (h : Projects P Q π) (R : FiniteLaw Γ) :
    Projects (P.bind (fun _ => R)) (Q.bind (fun _ => R)) (fun z => (π z.1,z.2)) := by
  intro f
  simp only [expect_bind]
  exact h (fun y => R.expect (fun z => f (y,z)))

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

/-- Forgetting the added spin sends the uniform (N+1)-spin prior exactly
to the uniform N-spin prior, including N=0. -/
theorem uniform_spin_projection (N : ℕ) :
    Projects (uniform : FiniteLaw (Fin (N+1) → Spin))
      (uniform : FiniteLaw (Fin N → Spin)) (fun σ i => σ i.succ) := by
  intro f
  rw [uniform_expect,uniform_expect,
    ← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp (fun σ => f (fun i => σ i.succ))]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,Fin.cons_succ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul]
  push_cast
  rw [pow_succ]
  have hcard : (2:ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_of_projects {π : Ω → Λ} (n : ℕ) {T : KernelTower Ω n} {U : KernelTower Λ n}
    (h : Projects π n T U) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n T m (fun y => f (pathMap π n y)) = backwardLog n U m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.1.logMean (m 0) (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
      (fun y => f (π a,pathMap π n y))) = _
    have heq : (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
        (fun y => f (π a,pathMap π n y))) =
      (fun a => backwardLog n (U.2 (π a)) (fun j => m j.succ) (fun y => f (π a,y))) := by
      funext a
      exact ih (h.2 a) (fun j => m j.succ) (fun y => f (π a,y))
    rw [heq]
    exact h.1.logMean (m 0) (fun b => backwardLog n (U.2 b) (fun j => m j.succ) (fun y => f (b,y)))

theorem terminalTower_projects (π : Ω → Λ) (a : Ω)
    {P : FiniteLaw Ω} {Q : FiniteLaw Λ} (h : P.Projects Q π) (r : ℕ) :
    Projects π (r+1) (terminalTower a P r) (terminalTower (π a) Q r) := by
  induction r with
  | zero => exact ⟨h,fun _ => trivial⟩
  | succ r ih =>
    refine ⟨?_,fun _ => ih⟩
    intro f
    change (FiniteLaw.point a).expect (fun x => f (π x)) = (FiniteLaw.point (π a)).expect f
    simp only [FiniteLaw.expect_point]

end KernelTower
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeterogeneousProjection
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
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ]
  {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

/-- Adjoining an unused physical coordinate preserves every realized mark
prior, also when the mark spaces have type-dependent dimensions. -/
theorem tower_projects (π : Ω → Λ) (roots : Fin k → I)
    (T : KernelTower Ω L) (U : KernelTower Λ L) (h : KernelTower.Projects π L T U)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.Projects (fun z : Ω × Row (A := A) roots => (π z.1,z.2)) L
      (tower roots L T Q) (tower roots L U Q) := by
  induction L with
  | zero => trivial
  | succ L ih =>
    refine ⟨h.1.bind (FiniteLaw.pi (fun j => Q (roots j) 0)),?_⟩
    intro z
    exact ih (T.2 z.1) (U.2 (π z.1)) (h.2 z.1) (fun i j => Q i j.succ)

/-- Exact projection through the literal perturbed power-mean root. -/
theorem root_projection (π : Ω → Λ) (roots : Fin k → I)
    (T : KernelTower Ω L) (U : KernelTower Λ L) (h : KernelTower.Projects π L T U)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Λ L → ℝ)
    (factor : (i : I) → FinitePath Λ L → FinitePath (A i) L → ℝ) :
    root T Q m (fun y => base (KernelTower.pathMap π L y)) roots
      (fun i x y => factor i (KernelTower.pathMap π L x) y) =
    root U Q m base roots factor := by
  have hh := KernelTower.backwardLog_of_projects L (tower_projects π roots T U h Q) m
    (logWeight base roots factor)
  unfold root
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext y
  simp only [logWeight,physical_pathMap,mark_pathMap]

 
theorem root_projection_stability (π : Ω → Λ) (roots : Fin k → I)
    (T : KernelTower Ω L) (U : KernelTower Λ L) (h : KernelTower.Projects π L T U)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Λ L → ℝ) (base' : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Λ L → FinitePath (A i) L → ℝ)
    (factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B : ℝ} (D : I → ℝ)
    (hb : ∀ y, |base' y-base (KernelTower.pathMap π L y)| ≤ B)
    (hf : ∀ i x y, |Real.log (factor' i x y)-Real.log (factor i (KernelTower.pathMap π L x) y)| ≤ D i) :
    |root T Q m base' roots factor'-root U Q m base roots factor| ≤ B+∑ q, D (roots q) := by
  rw [← root_projection π roots T U h Q m base factor]
  apply (abs_sub_le _ (root T Q m (fun y => base (KernelTower.pathMap π L y)) roots factor') _).trans
  exact add_le_add (root_base_stability T Q m hm base' _ roots factor' hb)
    (root_factor_stability T Q m hm _ roots factor' _ D hf)

end DilutedSpinGlass.HeterogeneousMarks
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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators
open HeterogeneousMarks

lemma interaction_coupling_bound {N p : ℕ} (θ : Interaction p) {C : ℝ}
    (hC : 0 ≤ C) (hθ : ∀ σ, |θ σ| ≤ C)
    (z : Fin p → Fin (N+1) × Fin N) (σ : Fin (N+1) → Spin) :
    |θ (fun j => σ (newIndex (z j))) - θ (fun j => σ (oldIndex (z j)).succ)| ≤
      2*C*∑ j, if (z j).1 = 0 then (1:ℝ) else 0 := by
  classical
  by_cases hz : ∀ j, (z j).1 ≠ 0
  · have he : (fun j => σ (newIndex (z j))) = (fun j => σ (oldIndex (z j)).succ) := by
      funext j; rw [same_index_off_new (z j) (hz j)]
    rw [he,sub_self,abs_zero]
    positivity
  · push Not at hz
    rcases hz with ⟨j,hj⟩
    have hs : (1:ℝ) ≤ ∑ i, if (z i).1 = 0 then (1:ℝ) else 0 := by
      have hh := Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin p))) =>
          show (0:ℝ) ≤ (if (z i).1 = 0 then 1 else 0) by split <;> norm_num)
        (Finset.mem_univ j)
      simpa only [hj,ite_true] using hh
    exact (abs_sub _ _).trans ((add_le_add (hθ _) (hθ _)).trans (by nlinarith))

lemma energy_coupling_bound {N p k : ℕ} (θ : Fin k → InteractionSample p)
    (h : Fin (N+1) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hθ : ∀ j σ, |(θ j).1 σ| ≤ C)
    (z : Fin k → Fin p → Fin (N+1) × Fin N) (σ : Fin (N+1) → Spin) :
    |logWeight θ h (fun j q => newIndex (z j q)) σ -
      logWeight θ (fun i => h i.succ) (fun j q => oldIndex (z j q)) (fun i => σ i.succ)| ≤
      |h 0|+2*C*∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0 := by
  have hspin : |spin (σ 0)| = 1 := by cases σ 0 <;> norm_num [spin]
  unfold logWeight
  rw [Fin.sum_univ_succ (fun i => h i * spin (σ i))]
  have he : ((∑ j, (θ j).1 (fun q => σ (newIndex (z j q)))) +
      (h 0*spin (σ 0)+∑ i : Fin N, h i.succ*spin (σ i.succ)))-
      ((∑ j, (θ j).1 (fun q => σ (oldIndex (z j q)).succ))+
        ∑ i : Fin N, h i.succ*spin (σ i.succ)) =
      h 0*spin (σ 0)+∑ j, ((θ j).1 (fun q => σ (newIndex (z j q)))-
        (θ j).1 (fun q => σ (oldIndex (z j q)).succ)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,hspin,mul_one]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ j, |(θ j).1 (fun q => σ (newIndex (z j q)))-
        (θ j).1 (fun q => σ (oldIndex (z j q)).succ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, 2*C*∑ q, if (z j q).1 = 0 then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun j _ => interaction_coupling_bound _ hC (hθ j) _ _)
    _ = _ := by rw [Finset.mul_sum]

/-- Keeping exactly the same realized physical and mark samples, only the
uniformly coupled sites that hit the new spin can change the root. -/
theorem spinRoot_size_coupling {N p k l r : ℕ} {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin (N+1) → ℝ)
    (z : Fin k → Fin p → Fin (N+1) × Fin N) (w : Fin l → Fin (N+1) × Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinRoot Q m theta h (fun j q => newIndex (z j q)) (fun i => newIndex (w i)) ψ -
      spinRoot Q m theta (fun i => h i.succ) (fun j q => oldIndex (z j q))
        (fun i => oldIndex (w i)) ψ| ≤
      |h 0|+2*C*(∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0)+
        2*D*(∑ i, if (w i).1 = 0 then (1:ℝ) else 0) := by
  let π : (Fin (N+1) → Spin) → (Fin N → Spin) := fun σ i => σ i.succ
  have hp := KernelTower.terminalTower_projects π (fun _ : Fin (N+1) => false)
    (FiniteLaw.uniform_spin_projection N) r
  have hh := root_projection_stability π (id : Fin l → Fin l) _ _ hp Q m hm
    (fun x => logWeight theta (fun i => h i.succ) (fun j q => oldIndex (z j q)) (KernelTower.terminalState r x))
    (fun x => logWeight theta h (fun j q => newIndex (z j q)) (KernelTower.terminalState r x))
    (fun i x a => ψ i (KernelTower.terminalState r x (oldIndex (w i))) a)
    (fun i x a => ψ i (KernelTower.terminalState r x (newIndex (w i))) a)
    (fun i => 2*D*(if (w i).1 = 0 then (1:ℝ) else 0))
    (fun x => by
      rw [KernelTower.terminalState_pathMap]
      exact energy_coupling_bound theta h hC hθ z (KernelTower.terminalState r x))
    (fun i x a => by
      rw [KernelTower.terminalState_pathMap]
      by_cases hw : (w i).1 = 0
      · simp only [hw,ite_true,mul_one]
        exact (abs_sub _ _).trans ((add_le_add (hψ i _ a) (hψ i _ a)).trans (by linarith))
      · simp only [hw,ite_false,π]
        rw [same_index_off_new (w i) hw,sub_self,abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hD) (le_refl 0))
  simpa only [spinRoot,id_eq,← Finset.mul_sum] using hh

end DilutedSpinGlass.SizeCoupling
end

end

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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

theorem expected_total_new_count (N k p : ℕ) [NeZero N] :
    (FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N))).expect
      (fun z => ∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0) = (k:ℝ)*p/(N+1) := by
  rw [FiniteLaw.expect_fintype_sum]
  have hm (j : Fin k) :
      (FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N))).expect
        (fun z => ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0) = (p:ℝ)/(N+1) := by
    exact (FiniteLaw.expect_pi_marginal (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N)) j
      (fun z => ∑ q, if (z q).1 = 0 then (1:ℝ) else 0)).trans (expected_new_count N p)
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Exact with-replacement uniform-site coupling estimate before averaging
physical disorder or mark specifications. Both finite-size marginals are the
actual independent index laws. -/
theorem spinMean_size_coupling {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin (N+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinMean Q m theta h ψ-spinMean Q m theta (fun i => h i.succ) ψ| ≤
      |h 0|+2*C*k*p/(N+1)+2*D*l/(N+1) := by
  let P := FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N))
  let R := FiniteLaw.pi (fun _ : Fin l => indexLaw N)
  have po := FiniteLaw.Projects.pi (fun _ : Fin k =>
    FiniteLaw.Projects.pi (fun _ : Fin p => oldIndex_projects N))
  have pn := FiniteLaw.Projects.pi (fun _ : Fin k =>
    FiniteLaw.Projects.pi (fun _ : Fin p => newIndex_projects N))
  have ro := FiniteLaw.Projects.pi (fun _ : Fin l => oldIndex_projects N)
  have rn := FiniteLaw.Projects.pi (fun _ : Fin l => newIndex_projects N)
  let f := fun (z : Fin k → Fin p → Fin (N+1) × Fin N) (w : Fin l → Fin (N+1) × Fin N) => spinRoot Q m theta h (fun j q => newIndex (z j q)) (fun i => newIndex (w i)) ψ
  let g := fun (z : Fin k → Fin p → Fin (N+1) × Fin N) (w : Fin l → Fin (N+1) × Fin N) => spinRoot Q m theta (fun i => h i.succ)
    (fun j q => oldIndex (z j q)) (fun i => oldIndex (w i)) ψ
  have hn : P.expect (fun z => R.expect (f z)) = spinMean Q m theta h ψ := by
    unfold spinMean
    calc
      _ = P.expect (fun z => (FiniteLaw.pi (fun _ : Fin l =>
          (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
            (fun w => spinRoot Q m theta h (fun j q => newIndex (z j q)) w ψ)) :=
        P.expect_congr (fun z => rn (fun w => spinRoot Q m theta h (fun j q => newIndex (z j q)) w ψ))
      _ = _ := pn (fun indices =>
        (FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
          (fun sites => spinRoot Q m theta h indices sites ψ))
  have ho : P.expect (fun z => R.expect (g z)) = spinMean Q m theta (fun i => h i.succ) ψ := by
    unfold spinMean
    calc
      _ = P.expect (fun z => (FiniteLaw.pi (fun _ : Fin l =>
          (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
            (fun w => spinRoot Q m theta (fun i => h i.succ) (fun j q => oldIndex (z j q)) w ψ)) :=
        P.expect_congr (fun z => ro (fun w => spinRoot Q m theta (fun i => h i.succ) (fun j q => oldIndex (z j q)) w ψ))
      _ = _ := po (fun indices =>
        (FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
          (fun sites => spinRoot Q m theta (fun i => h i.succ) indices sites ψ))
  rw [← hn,← ho,← FiniteLaw.expect_sub]
  calc
    _ ≤ P.expect (fun z => |R.expect (f z)-R.expect (g z)|) := P.abs_expect_le_expect_abs _
    _ ≤ P.expect (fun z => R.expect (fun w => |f z w-g z w|)) := P.expect_mono (fun z => by
      rw [← FiniteLaw.expect_sub]
      exact R.abs_expect_le_expect_abs _)
    _ ≤ P.expect (fun z => R.expect (fun w =>
        |h 0|+2*C*(∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0)+
          2*D*(∑ i, if (w i).1 = 0 then (1:ℝ) else 0))) :=
      P.expect_mono (fun z => R.expect_mono (fun w => spinRoot_size_coupling Q m hm theta h z w ψ hC hD hθ hψ))
    _ = _ := by
      simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_mul_left,
        R,P,expected_new_count,expected_total_new_count]
      ring

end DilutedSpinGlass.SizeCoupling
end

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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConcentrationRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Filter
open scoped Topology

lemma scoreScale_le {N : ℕ} (hN : 1 ≤ N) : scoreScale N ≤ (N:ℝ) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  simpa only [scoreScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (3:ℝ)/4 ≤ 1)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSpinMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

/-- Measurability for the literal root before quenched averaging. Only the
interaction table values are read; auxiliary factorization witnesses are not. -/
theorem measurable_spinMean {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Z → Fin k → InteractionSample p) (h : Z → Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hθ : ∀ j σ, Measurable (fun z => (theta z j).1 σ))
    (hh : ∀ i, Measurable (fun z => h z i)) :
    Measurable (fun z => spinMean Q m (theta z) (h z) ψ) := by
  unfold spinMean
  apply FiniteLaw.measurable_expect
  intro indices
  apply FiniteLaw.measurable_expect
  intro sites
  apply measurable_root
  · intro x
    exact (Finset.measurable_sum _ (fun j _ => hθ j _)).add
      (Finset.measurable_sum _ (fun i _ => (hh i).mul_const _))
  · intro i x a
    exact measurable_const

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

theorem spinMean_bound {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ i, |h i| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinMean Q m theta h ψ| ≤ H*N+C*k+D*l := by
  apply FiniteLaw.abs_expect_le
  intro indices
  apply FiniteLaw.abs_expect_le
  intro sites
  exact root_uniform_bound _ Q m hm _ id _
    (fun x => finite_logWeight_bound theta h indices (KernelTower.terminalState r x) hθ hh)
    (fun i x a => hψ i _ a)

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

lemma abs_integral_le_const (μ : Measure Z) [IsProbabilityMeasure μ] {f : Z → ℝ} {B : ℝ}
    (h : ∀ z, |f z| ≤ B) : |∫ z, f z ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (ae_of_all μ (fun z => by simpa only [Real.norm_eq_abs] using h z)))

omit [Countable I] [MeasurableSingletonClass I] in
theorem countedMean_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ H*N+C*k+D*l := by
  apply abs_integral_le_const
  intro a
  apply abs_integral_le_const
  intro x
  apply abs_integral_le_const
  intro h
  exact spinMean_bound _ m hm _ _ _ (fun j σ => hθ _ σ) (fun i => hh _) (fun j σ a => hψ _ σ a)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Joint measurability in the genuine independent physical roots. -/
theorem measurable_countedIntegrand {p r N : ℕ} [NeZero N]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (k l : ℕ) (a : RootPath I l) :
    Measurable (fun z : RootPath X k × RootPath Y N =>
      spinMean (fun j => Q (rootArray l a j)) m (fun j => theta (rootArray k z.1 j))
        (fun i => field (rootArray N z.2 i)) (fun j => ψ (rootArray l a j))) := by
  apply measurable_spinMean
  · intro j σ
    exact (hθ σ).comp ((measurable_rootArray k j).comp measurable_fst)
  · intro j
    exact hh.comp ((measurable_rootArray N j).comp measurable_snd)

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

namespace DilutedSpinGlass.SizeCoupling
open HeterogeneousMarks
open scoped BigOperators

theorem spinRoot_interaction_step {N p k l r : ℕ} {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin (k+1) → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin (k+1) → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C : ℝ} (hθ : ∀ σ, |(theta 0).1 σ| ≤ C) :
    |spinRoot Q m theta h indices sites ψ-
      spinRoot Q m (fun j => theta j.succ) h (fun j => indices j.succ) sites ψ| ≤ C := by
  apply root_base_stability _ Q m hm
  intro x
  simpa only [DilutedSpinGlass.logWeight, Fin.sum_univ_succ,add_sub_add_right_eq_sub,
    add_sub_cancel_right] using hθ (fun q => KernelTower.terminalState r x (indices 0 q))

theorem spinMean_interaction_step {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin (k+1) → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C : ℝ} (hθ : ∀ σ, |(theta 0).1 σ| ≤ C) :
    |spinMean Q m theta h ψ-spinMean Q m (fun j => theta j.succ) h ψ| ≤ C := by
  unfold spinMean
  rw [FiniteLaw.expect_pi_cons]
  rw [← (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect_const
    ((FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N))))).expect _)]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  apply FiniteLaw.abs_expect_sub_le
  intro indices
  apply FiniteLaw.abs_expect_sub_le
  intro sites
  exact spinRoot_interaction_step Q m hm theta h (Fin.cons i indices) sites ψ hθ

/-- Deleting one realized factor integrates out only its own independent marks.
The surviving factors keep their alphabets and level priors exactly. -/
theorem spinRoot_mark_step {N p k l r : ℕ} {A : Fin (l+1) → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin (l+1)) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin (l+1) → Fin N)
    (ψ : (i : Fin (l+1)) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ σ a, |Real.log (ψ 0 σ a)| ≤ D) :
    |spinRoot Q m theta h indices sites ψ-
      spinRoot (fun j => Q j.succ) m theta h indices (fun j => sites j.succ) (fun j => ψ j.succ)| ≤ D := by
  have hid : Fin.cons 0 (fun j : Fin l => j.succ) = (id : Fin (l+1) → Fin (l+1)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hp := root_pullback (Fin.succ : Fin l → Fin (l+1)) id
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m
    (fun x => DilutedSpinGlass.logWeight theta h indices (KernelTower.terminalState r x))
    (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)
  unfold spinRoot
  rw [hp]
  exact (by
    simpa only [hid,Function.comp_id] using
      root_cons_bound
        (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m hm
        (fun x => DilutedSpinGlass.logWeight theta h indices (KernelTower.terminalState r x))
        (fun j : Fin l => j.succ) 0
        (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)
        (fun x a => hψ _ a))

theorem spinMean_mark_step {N p k l r : ℕ} [NeZero N] {A : Fin (l+1) → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin (l+1)) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin (l+1)) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ σ a, |Real.log (ψ 0 σ a)| ≤ D) :
    |spinMean Q m theta h ψ-
      spinMean (fun j => Q j.succ) m theta h (fun j => ψ j.succ)| ≤ D := by
  apply FiniteLaw.abs_expect_sub_le
  intro indices
  rw [FiniteLaw.expect_pi_cons]
  rw [← (FiniteLaw.uniform : FiniteLaw (Fin N)).expect_const
    ((FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect _)]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  apply FiniteLaw.abs_expect_sub_le
  intro sites
  exact spinRoot_mark_step Q m hm theta h indices (Fin.cons i sites) ψ hψ

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSizeCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

lemma abs_integral_sub_le_const {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {f g : Z → ℝ} {B : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ z, |f z-g z| ≤ B) :
    |(∫ z, f z ∂μ)-(∫ z, g z ∂μ)| ≤ B := by
  rw [← integral_sub hf hg]
  exact abs_integral_le_const μ h

/-- The independent additional field is integrated under its original law.
The per-count cost is uniform in every auxiliary mark prior and parameter. -/
theorem fieldMean_size_coupling (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (field : Y → ℝ) (hfm : Measurable field)
    (theta : Fin k → InteractionSample p)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |(∫ h : RootPath Y (N+1), spinMean Q m theta (fun i => field (rootArray (N+1) h i)) ψ
        ∂rootLaw (N+1) (fun _ => ξ))-
      (∫ h : RootPath Y N, spinMean Q m theta (fun i => field (rootArray N h i)) ψ
        ∂rootLaw N (fun _ => ξ))| ≤
      H+2*C*k*p/(N+1)+2*D*l/(N+1) := by
  let P := rootLaw N (fun _ => ξ)
  let f := fun h : Y × RootPath Y N => spinMean Q m theta
    (fun i => field (rootArray (N+1) h i)) ψ
  let g := fun h : Y × RootPath Y N => spinMean Q m theta
    (fun i => field (rootArray N h.2 i)) ψ
  have hfm' : Measurable f := measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hfm.comp (measurable_rootArray (N+1) i))
  have hgm' : Measurable g := measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hfm.comp ((measurable_rootArray N i).comp measurable_snd))
  have hf : Integrable f (ξ.prod P) := Integrable.of_bound hfm'.aestronglyMeasurable
    (H*(N+1)+C*k+D*l) (ae_of_all _ (fun h => by
      simpa only [Real.norm_eq_abs,Nat.cast_add,Nat.cast_one] using
        spinMean_bound Q m hm theta (fun i => field (rootArray (N+1) h i)) ψ hθ (fun i => hh _) hψ))
  have hg : Integrable g (ξ.prod P) := Integrable.of_bound hgm'.aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun h => by
      simpa only [Real.norm_eq_abs] using spinMean_bound Q m hm theta (fun i => field (rootArray N h.2 i)) ψ hθ (fun i => hh _) hψ))
  have he : (∫ h, g h ∂ξ.prod P) = ∫ h : RootPath Y N,
      spinMean Q m theta (fun i => field (rootArray N h i)) ψ ∂P := by
    rw [integral_prod _ hg]
    simp only [g,integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ h, f h ∂ξ.prod P)-_| ≤ _
  rw [← he]
  apply abs_integral_sub_le_const _ hf hg
  intro h
  have ha := spinMean_size_coupling Q m hm theta
    (fun i => field (rootArray (N+1) h i)) ψ hC hD hθ hψ
  have hh0 : |field (rootArray (N+1) h 0)| ≤ H := hh _
  exact ha.trans (by linarith)

/-- Uniform finite-size comparison for the same quenched countable dictionary
and the same counts. All three root measures are the actual independent laws. -/
theorem countedMean_size_coupling (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N+1) μ ξ ν theta field Q m ψ k l-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤
      H+2*C*k*p/(N+1)+2*D*l/(N+1) := by
  let F := fun (n : ℕ) [NeZero n] (a : RootPath I l) (x : RootPath X k) =>
    ∫ h : RootPath Y n, spinMean (fun j => Q (rootArray l a j)) m
      (fun j => theta (rootArray k x j)) (fun i => field (rootArray n h i))
      (fun j => ψ (rootArray l a j)) ∂rootLaw n (fun _ => ξ)
  have hFm (n : ℕ) [NeZero n] (a : RootPath I l) : Measurable (F n a) :=
    (measurable_countedIntegrand (N := n) theta field hθm hhm Q m ψ k l a).stronglyMeasurable.integral_prod_right'.measurable
  have hFb (n : ℕ) [NeZero n] (a : RootPath I l) (x : RootPath X k) :
      |F n a x| ≤ H*n+C*k+D*l := abs_integral_le_const _ (fun h =>
    spinMean_bound _ m hm _ _ _ (fun j σ => hθ _ σ) (fun i => hh _) (fun j σ a => hψ _ σ a))
  have hFi (n : ℕ) [NeZero n] (a : RootPath I l) : Integrable (F n a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm n a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb n a x))
  have hOi (n : ℕ) [NeZero n] : Integrable (fun a => ∫ x, F n a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*n+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb n a)))
  apply abs_integral_sub_le_const _ (hOi (N+1)) (hOi N)
  intro a
  apply abs_integral_sub_le_const _ (hFi (N+1) a) (hFi N a)
  intro x
  exact fieldMean_size_coupling ξ field hhm _ _ m hm _ hC hD
    (fun j σ => hθ _ σ) hh (fun j σ a => hψ _ σ a)

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonRateCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

/-- Common Poisson points give the exact first-moment rate coupling estimate.
This is a consequence of convolution, not a coupling hypothesis. -/
theorem poisson_average_rate_add (r s : ℝ≥0) {f : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hstep : ∀ n, |f (n+1)-f n| ≤ C) :
    |(∫ n, f n ∂poissonMeasure (r+s))-(∫ n, f n ∂poissonMeasure r)| ≤ C*(s:ℝ) := by
  have hl := nat_lipschitz_of_step hC hstep
  have hb (n : ℕ) : |f n| ≤ |f 0|+C*n := by
    have hh := hl n 0
    simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)] at hh
    calc
      |f n| = |(f n-f 0)+f 0| := by congr 1; ring
      _ ≤ |f n-f 0|+|f 0| := abs_add_le _ _
      _ ≤ |f 0|+C*n := by linarith
  have hi (q : ℝ≥0) : Integrable f (poissonMeasure q) := poisson_integrable_linear q hb
  have hin (n : ℕ) : Integrable (fun k => f (n+k)) (poissonMeasure s) := by
    apply poisson_integrable_linear s (A := |f 0|+C*n) (B := C)
    intro k
    convert hb (n+k) using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have hd (n : ℕ) : |(∫ k, f (n+k) ∂poissonMeasure s)-f n| ≤ C*(s:ℝ) := by
    have h := integral_mono ((hin n).sub (integrable_const (f n))).abs
      ((poisson_integrable_count s).const_mul C) (fun k => by
        change |f (n+k)-f n| ≤ C*(k:ℝ)
        have hh := hl (n+k) n
        simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)] using hh)
    simp only [Pi.sub_apply] at h
    rw [integral_const_mul,poisson_mean] at h
    have ha := abs_integral_le_integral_abs.trans h
    rw [integral_sub (hin n) (integrable_const (f n))] at ha
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ha
  have hj : Integrable (fun n => ∫ k, f (n+k) ∂poissonMeasure s) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := |f 0|+C*s) (B := C)
    intro n
    have hh := abs_sub_le_iff.mp (hd n)
    have hf := abs_le.mp (hb n)
    rw [abs_le]
    constructor <;> linarith
  have hconv : Integrable f (poissonMeasure r ∗ poissonMeasure s) := by
    rw [poissonMeasure_conv_poissonMeasure]
    exact hi (r+s)
  rw [← poissonMeasure_conv_poissonMeasure,integral_conv hconv,← integral_sub hj (hi r)]
  exact abs_integral_le_bound hd

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSteps
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

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

lemma fieldMean_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |fieldMean (N := N) ξ theta field Q m ψ| ≤ H*N+C*k+D*l :=
  abs_integral_le_const _ (fun root => spinMean_bound Q m hm theta _ ψ hθ
    (fun index => hh (rootArray N root index)) hψ)

lemma measurable_fieldMean {Z : Type} [MeasurableSpace Z] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Z → Fin k → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ j σ, Measurable (fun z => (theta z j).1 σ)) (hhm : Measurable field)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ) :
    Measurable (fun z => fieldMean (N := N) ξ (theta z) field Q m ψ) := by
  exact (measurable_spinMean Q m (fun z : Z × RootPath Y N => theta z.1)
    (fun z i => field (rootArray N z.2 i)) ψ
    (fun j σ => (hθm j σ).comp measurable_fst)
    (fun i => hhm.comp ((measurable_rootArray N i).comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_spinMean (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    Integrable (fun h : RootPath Y N => spinMean Q m theta
      (fun i => field (rootArray N h i)) ψ) (rootLaw N (fun _ => ξ)) := by
  apply Integrable.of_bound (measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hhm.comp (measurable_rootArray N i))).aestronglyMeasurable
    (H*N+C*k+D*l)
  filter_upwards [] with h
  simpa only [Real.norm_eq_abs,Function.comp_def] using
    spinMean_bound Q m hm theta (fun i => field (rootArray N h i)) ψ hθ (fun i => hh _) hψ

/-- Count insertion of the original independent physical interaction sample. -/
theorem countedMean_interaction_step (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ (k+1) l-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ C := by
  let F := fun (k : ℕ) (a : RootPath I l) (x : RootPath X k) =>
    fieldMean (N := N) ξ (fun j => theta (rootArray k x j)) field
      (fun j => Q (rootArray l a j)) m (fun j => ψ (rootArray l a j))
  have hFm (k : ℕ) (a : RootPath I l) : Measurable (F k a) :=
    measurable_fieldMean ξ _ field (fun j σ => (hθm σ).comp (measurable_rootArray k j)) hhm _ m _
  have hFb (k : ℕ) (a : RootPath I l) (x : RootPath X k) : |F k a x| ≤ H*N+C*k+D*l :=
    fieldMean_bound ξ _ field _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b)
  have hFi (k : ℕ) (a : RootPath I l) : Integrable (F k a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm k a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb k a x))
  have hOi (k : ℕ) : Integrable (fun a => ∫ x, F k a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb k a)))
  change |(∫ a, ∫ x, F (k+1) a x ∂rootLaw (k+1) (fun _ => μ) ∂rootLaw l (fun _ => ν))-
    (∫ a, ∫ x, F k a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν))| ≤ C
  apply abs_integral_sub_le_const _ (hOi (k+1)) (hOi k)
  intro a
  have hg : Integrable (fun x : X × RootPath X k => F k a x.2)
      (μ.prod (rootLaw k (fun _ => μ))) := (hFi k a).comp_snd μ
  have he : (∫ x : X × RootPath X k, F k a x.2 ∂μ.prod (rootLaw k (fun _ => μ))) =
      ∫ x, F k a x ∂rootLaw k (fun _ => μ) := by
    rw [integral_prod _ hg]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ x, F (k+1) a x ∂μ.prod (rootLaw k (fun _ => μ)))-_| ≤ C
  rw [← he]
  apply abs_integral_sub_le_const (μ.prod (rootLaw k (fun _ => μ))) (hFi (k+1) a) hg
  intro x
  apply abs_integral_sub_le_const _
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
  intro h
  exact spinMean_interaction_step _ m hm _ _ _ (hθ x.1)

/-- Count insertion draws the original countable dictionary type; its entire
finite mark alphabet and all level priors are kept. -/
theorem countedMean_mark_step (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ k (l+1)-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ D := by
  let F := fun (l : ℕ) (a : RootPath I l) (x : RootPath X k) =>
    fieldMean (N := N) ξ (fun j => theta (rootArray k x j)) field
      (fun j => Q (rootArray l a j)) m (fun j => ψ (rootArray l a j))
  have hFm (l : ℕ) (a : RootPath I l) : Measurable (F l a) :=
    measurable_fieldMean ξ _ field (fun j σ => (hθm σ).comp (measurable_rootArray k j)) hhm _ m _
  have hFb (l : ℕ) (a : RootPath I l) (x : RootPath X k) : |F l a x| ≤ H*N+C*k+D*l :=
    fieldMean_bound ξ _ field _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b)
  have hFi (l : ℕ) (a : RootPath I l) : Integrable (F l a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm l a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb l a x))
  have hOi (l : ℕ) : Integrable (fun a => ∫ x, F l a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb l a)))
  have hg := (hOi l).comp_snd ν
  have he : (∫ a : I × RootPath I l, (∫ x, F l a.2 x ∂rootLaw k (fun _ => μ))
      ∂ν.prod (rootLaw l (fun _ => ν))) =
      ∫ a, ∫ x, F l a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν) := by
    rw [integral_prod _ hg]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ a, ∫ x, F (l+1) a x ∂rootLaw k (fun _ => μ) ∂ν.prod (rootLaw l (fun _ => ν)))-
    (∫ a, ∫ x, F l a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν))| ≤ D
  rw [← he]
  apply abs_integral_sub_le_const (ν.prod (rootLaw l (fun _ => ν))) (hOi (l+1)) hg
  intro a
  apply abs_integral_sub_le_const _ (hFi (l+1) a) (hFi l a.2)
  intro x
  apply abs_integral_sub_le_const _
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
  intro h
  exact spinMean_mark_step _ m hm _ _ _ (hψ a.1)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma poisson_abs_mean_le (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A+B*n) : |∫ n, f n ∂poissonMeasure r| ≤ A+B*r := by
  have hi := poisson_integrable_linear r h
  have hg : Integrable (fun n : ℕ => A+B*n) (poissonMeasure r) :=
    (integrable_const A).add ((poisson_integrable_count r).const_mul B)
  calc
    _ ≤ ∫ n, |f n| ∂poissonMeasure r := abs_integral_le_integral_abs
    _ ≤ ∫ n : ℕ, A+B*n ∂poissonMeasure r := integral_mono hi.abs hg h
    _ = _ := by rw [integral_add (integrable_const A) ((poisson_integrable_count r).const_mul B),
        integral_const_mul,poisson_mean]; simp

lemma twoPoisson_inner_integrable (r s : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D : ℝ}
    (h : ∀ k l, |f k l| ≤ A+B*k+D*l) :
    Integrable (fun k => ∫ l, f k l ∂poissonMeasure s) (poissonMeasure r) := by
  apply poisson_integrable_linear r (A := A+D*s) (B := B)
  intro k
  have ht := poisson_abs_mean_le s (h k)
  linarith

lemma twoPoisson_abs_mean_le (r s : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D : ℝ}
    (h : ∀ k l, |f k l| ≤ A+B*k+D*l) :
    |twoPoissonMean r s f| ≤ A+B*r+D*s := by
  have ht := poisson_abs_mean_le r (A := A+D*s) (B := B) (f := fun k => ∫ l, f k l ∂poissonMeasure s)
    (fun k => by have := poisson_abs_mean_le s (h k); linarith)
  dsimp [twoPoissonMean]
  linarith

lemma twoPoissonMean_sub (r s : ℝ≥0) {f g : ℕ → ℕ → ℝ} {A B D A' B' D' : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hg : ∀ k l, |g k l| ≤ A'+B'*k+D'*l) :
    twoPoissonMean r s f-twoPoissonMean r s g = twoPoissonMean r s (fun k l => f k l-g k l) := by
  unfold twoPoissonMean
  rw [← integral_sub (twoPoisson_inner_integrable r s hf) (twoPoisson_inner_integrable r s hg)]
  apply integral_congr_ae
  exact ae_of_all _ (fun k => (integral_sub (poisson_integrable_linear s (hf k))
    (poisson_integrable_linear s (hg k))).symm)

lemma twoPoisson_abs_sub_le (r s : ℝ≥0) {f g : ℕ → ℕ → ℝ}
    {A B D A' B' D' E F G : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hg : ∀ k l, |g k l| ≤ A'+B'*k+D'*l)
    (h : ∀ k l, |f k l-g k l| ≤ E+F*k+G*l) :
    |twoPoissonMean r s f-twoPoissonMean r s g| ≤ E+F*r+G*s := by
  rw [twoPoissonMean_sub r s hf hg]
  exact twoPoisson_abs_mean_le r s h

lemma twoPoissonMean_rate_add_left (r s t : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D C : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hC : 0 ≤ C)
    (hs : ∀ k l, |f (k+1) l-f k l| ≤ C) :
    |twoPoissonMean (r+t) s f-twoPoissonMean r s f| ≤ C*t := by
  apply poisson_average_rate_add r t hC
  intro k
  exact SizeCoupling.abs_integral_sub_le_const _ (poisson_integrable_linear s (hf (k+1)))
    (poisson_integrable_linear s (hf k)) (hs k)

lemma twoPoissonMean_rate_add_right (r s t : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D C : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hC : 0 ≤ C)
    (hs : ∀ k l, |f k (l+1)-f k l| ≤ C) :
    |twoPoissonMean r (s+t) f-twoPoissonMean r s f| ≤ C*t := by
  apply SizeCoupling.abs_integral_sub_le_const _ (twoPoisson_inner_integrable r (s+t) hf)
    (twoPoisson_inner_integrable r s hf)
  intro k
  exact poisson_average_rate_add s t hC (hs k)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PerturbedSizeCoupling
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

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

theorem perturbedMean_size_rate_coupling (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (u v t w : ℝ≥0) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (u+t) (v+w)-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ u v| ≤
      Real.log 2+H+2*C*u*p/(N+1)+2*D*v/(N+1)+C*t+D*w := by
  let f := countedMean (N := N+1) μ ξ ν theta field Q m ψ
  let g := countedMean (N := N) μ ξ ν theta field Q m ψ
  have hf : ∀ k l, |f k l| ≤ H*(N+1)+C*k+D*l := by
    intro k l
    simpa only [Nat.cast_add,Nat.cast_one] using countedMean_bound (N := N+1) μ ξ ν theta field Q m hm ψ hθ hh hψ k l
  have hg : ∀ k l, |g k l| ≤ H*N+C*k+D*l :=
    countedMean_bound μ ξ ν theta field Q m hm ψ hθ hh hψ
  have hc : |twoPoissonMean u v f-twoPoissonMean u v g| ≤ H+2*C*u*p/(N+1)+2*D*v/(N+1) := by
    have ht := twoPoisson_abs_sub_le u v hf hg (E := H) (F := 2*C*p/(N+1)) (G := 2*D/(N+1))
      (fun k l => (countedMean_size_coupling μ ξ ν theta field hθm hhm Q m hm ψ hC hD hθ hh hψ k l).trans_eq (by ring))
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hl := twoPoissonMean_rate_add_left u (v+w) t hf hC
    (countedMean_interaction_step μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ)
  have hr := twoPoissonMean_rate_add_right u v w hf hD
    (countedMean_mark_step μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (u+t) (v+w)-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ u v =
      Real.log 2 + (twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f) +
      (twoPoissonMean u (v+w) f-twoPoissonMean u v f)+
      (twoPoissonMean u v f-twoPoissonMean u v g) := by
    simp only [perturbedMean,Nat.cast_add,Nat.cast_one,f,g]
    ring
  rw [he]
  have h1 := abs_add_le (Real.log 2) (twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f)
  have h2 := abs_add_le (Real.log 2+(twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f))
    (twoPoissonMean u (v+w) f-twoPoissonMean u v f)
  have h3 := abs_add_le (Real.log 2+(twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f)+
    (twoPoissonMean u (v+w) f-twoPoissonMean u v f)) (twoPoissonMean u v f-twoPoissonMean u v g)
  rw [abs_of_nonneg hlog] at h1
  linarith

end DilutedSpinGlass.SizeCoupling

namespace DilutedSpinGlass
open scoped NNReal

lemma scoreScale_mono : Monotone scoreScale := by
  intro M N hMN
  exact Real.rpow_le_rpow (Nat.cast_nonneg M) (by exact_mod_cast hMN) (by norm_num)

lemma scoreScale_succ_sub_le (N : ℕ) : scoreScale (N+1)-scoreScale N ≤ 1 := by
  have ht := Real.rpow_add_le_add_rpow (show (0:ℝ) ≤ N from Nat.cast_nonneg N)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3:ℝ)/4 ≤ 1)
  norm_num only [Real.one_rpow] at ht
  dsimp [scoreScale]
  push_cast
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

/-- The uniform lower and upper increment envelope needed by deterministic
parameter selection. Dependence on the entire dictionary and on all priors has
cancelled; the original uncapped N^(3/4) scale is used. -/
theorem perturbedMean_uniform_increment (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (α : ℝ≥0) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) (scoreRate (N+1))-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ (α*N) (scoreRate N)| ≤
      Real.log 2+H+(2*p+1)*C*α+3*D := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hs : scoreRate N ≤ scoreRate (N+1) := scoreScale_mono (Nat.le_succ N)
  have ha : α*(N:ℝ≥0)+α = α*(N+1) := by ring
  have hb : scoreRate N+(scoreRate (N+1)-scoreRate N) = scoreRate (N+1) :=
    add_tsub_cancel_of_le hs
  have ht := perturbedMean_size_rate_coupling (N := N) μ ξ ν theta field hθm hhm Q m hm ψ hC hD
    hθ hh hψ (α*N) (scoreRate N) α (scoreRate (N+1)-scoreRate N)
  rw [ha,hb] at ht
  apply ht.trans
  have hden : (0:ℝ) < N+1 := by positivity
  have hex : (↑(scoreRate (N+1)-scoreRate N):ℝ) ≤ 1 := by
    rw [NNReal.coe_sub hs]
    exact scoreScale_succ_sub_le N
  have hp : 2*C*↑(α*(N:ℝ≥0))*p/(N+1) ≤ 2*C*α*p := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith [mul_nonneg hC α.coe_nonneg, mul_nonneg (mul_nonneg hC α.coe_nonneg) (Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hm' : 2*D*(scoreRate N:ℝ)/(N+1) ≤ 2*D := by
    apply (div_le_iff₀ hden).mpr
    have hs' := scoreScale_le hN
    change scoreScale N ≤ (N:ℝ) at hs'
    change 2*D*scoreScale N ≤ _
    nlinarith
  have hw := mul_le_mul_of_nonneg_left hex hD
  linarith

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootAE
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

lemma measurePreserving_rootArray_coordinate {X : Type} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun z : RootPath X n => rootArray n z i) (rootLaw n μ) (μ i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact measurePreserving_fst
    | succ i =>
      exact (ih (fun j => μ j.succ) i).comp (measurePreserving_snd)

lemma rootLaw_ae_all {X : Type} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (P : Fin n → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ i, P i x) :
    ∀ᵐ z ∂rootLaw n μ, ∀ i, P i (rootArray n z i) := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_rootArray_coordinate n μ i).quasiMeasurePreserving.ae (hP i)

namespace SizeCoupling
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

omit [Countable I] [MeasurableSingletonClass I] in
lemma countedMean_congr (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta theta' : X → InteractionSample p) (field field' : Y → ℝ)
    (hθ : theta =ᵐ[μ] theta') (hh : field =ᵐ[ξ] field')
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (k l : ℕ) :
    countedMean (N := N) μ ξ ν theta field Q m ψ k l =
      countedMean (N := N) μ ξ ν theta' field' Q m ψ k l := by
  unfold countedMean
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [rootLaw_ae_all k (fun _ => μ) (fun _ x => theta x = theta' x) (fun _ => hθ)] with x hx
  apply integral_congr_ae
  filter_upwards [rootLaw_ae_all N (fun _ => ξ) (fun _ y => field y = field' y) (fun _ => hh)] with y hy
  congr 1
  · funext i; exact hx i
  · funext i; exact hy i

end SizeCoupling
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

lemma clipReal_eq {C x : ℝ} (hx : |x| ≤ C) : clipReal C x = x := by
  simp only [clipReal,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]

lemma clipSample_bound {p : ℕ} {C : ℝ} (hC : 0 ≤ C) (z : InteractionSample p) (σ) :
    |(clipSample C z).1 σ| ≤ C := clipReal_bound hC _

lemma clipSample_eq {p : ℕ} {C : ℝ} {z : InteractionSample p}
    (hz : ∀ σ, |z.1 σ| ≤ C) : clipSample C z = z := by
  apply Prod.ext
  · funext σ; exact clipReal_eq (hz σ)
  · rfl

namespace SizeCoupling
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

omit [Countable I] [MeasurableSingletonClass I] in
lemma perturbedMean_congr (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta theta' : X → InteractionSample p) (field field' : Y → ℝ)
    (hθ : theta =ᵐ[μ] theta') (hh : field =ᵐ[ξ] field')
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (u v : ℝ≥0) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ u v =
      perturbedMean (N := N) μ ξ ν theta' field' Q m ψ u v := by
  unfold perturbedMean twoPoissonMean
  simp_rw [countedMean_congr μ ξ ν theta theta' field field' hθ hh Q m ψ]

/-- The genuine bounded-model increment estimate, with AE (not vacuous global)
bounds on the original physical law. -/
theorem actual_uniform_increment_ae (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (M : Model p)
    {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |perturbedMean (N := N+1) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ
        (M.alpha*(N+1)) (scoreRate (N+1))-
      perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ
        (M.alpha*N) (scoreRate N)| ≤ Real.log 2+H+(2*p+1)*C*M.alpha+3*D := by
  have heθ : id =ᵐ[M.disorder.toMeasure] clipSample C := hθ.mono (fun z hz => (clipSample_eq hz).symm)
  have heh : id =ᵐ[M.field.toMeasure] clipReal H := hh.mono (fun h hh => (clipReal_eq hh).symm)
  rw [perturbedMean_congr _ _ ν id (clipSample C) id (clipReal H) heθ heh,
    perturbedMean_congr _ _ ν id (clipSample C) id (clipReal H) heθ heh]
  exact perturbedMean_uniform_increment _ _ ν (clipSample C) (clipReal H)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
    (measurable_clipReal H) Q m hm ψ hC hD (clipSample_bound hC) (clipReal_bound hH) hψ M.alpha

end SizeCoupling
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

omit [DecidableEq K] in
lemma uniform_increment_sat_oai (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H) (hm : ∀ l, 0 < m l)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (N : ℕ) (u : K×ℕ → ℝ) :
    |increment ν Q m D E M N u| ≤ Real.log 2+H+(2*p+1)*C*M.alpha+3 := by
  simpa only [increment,Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,add_assoc,one_add_one_eq_two,mul_one] using
    SizeCoupling.actual_uniform_increment_ae (N := N+1) ν M hC hH hθ hh (fun i => Q i.1) m hm
      (spinFactor D E u) (by norm_num : (0:ℝ) ≤ 1) (spinFactor_log_bound D E hD hE u)

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment_sat_oai := @OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment_sat_oai
