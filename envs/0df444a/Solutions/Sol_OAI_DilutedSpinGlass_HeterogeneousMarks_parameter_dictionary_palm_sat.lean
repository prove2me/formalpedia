-- Prove2me | solution 1 for OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:32:34.516897+00:00
-- url     : https://prove2.me/submissions/e49b36f5-d78f-44e3-9bd8-05032c153143

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

/-- Exact composition of two one-step insertions, with no support assumption. -/
theorem tilt_insertion (m : ℝ) (f a : Ω → ℝ) :
    (P.tilt m f).tilt m a = P.tilt m (fun x => f x + a x) := by
  apply weights_ext
  intro x
  have he : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  change (P.weight x * Real.exp (m * f x) / P.expMoment m f) * Real.exp (m * a x) /
    (P.tilt m f).expMoment m a = _
  rw [he]
  simp only [tilt, mul_add, Real.exp_add]
  field_simp [ne_of_gt (P.expMoment_pos m f)]

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



/-- Updated kernels after an insertion agree with the successive tilting of
all the old tilted kernels. This is tree:updated-kernel at every depth. -/
theorem tilt_insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    tilt n (tilt n T m f) m a = tilt n T m (fun x => f x + a x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.tilt (m 0) _).tilt (m 0) _ = T.1.tilt (m 0) _
      rw [FiniteLaw.tilt_insertion]
      congr 1
      funext x
      have h := insertion n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ + backwardLog n (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
        (fun j => m j.succ) (fun y => a (x,y)) = _
      linarith
    · funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))

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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem tilt_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).tilt m f = (P.tilt m (f ∘ e)).transport e := by
  apply eq_of_weights
  intro y
  change P.weight (e.symm y) * Real.exp (m * f y) /
    (P.transport e).expMoment m f =
      P.weight (e.symm y) * Real.exp (m * f (e (e.symm y))) / P.expMoment m (f ∘ e)
  rw [expMoment_transport, Equiv.apply_symm_apply]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem tilt_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    tilt n (transport e n T) m f =
      transport e n (tilt n T m (f ∘ pathEquiv e n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · simp only [tilt, transport, FiniteLaw.tilt_transport]
      congr 2
      funext a
      simp only [Function.comp_def, Equiv.symm_apply_apply, backwardLog_transport,
        pathEquiv_cons]
    · funext a
      simp only [tilt, transport, ih, Function.comp_def, pathEquiv_cons, Equiv.apply_symm_apply]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem sampleWeight_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (x : Sample Ω S) :
    (sampleLaw S (KernelTower.transport e n T)).weight (sampleEquiv e S x) =
      (sampleLaw S T).weight x := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases T with ⟨P, T⟩
    change (∏ i, P.weight (e.symm (e (x i).1)) *
      (sampleLaw (C i) (KernelTower.transport e n (T (e.symm (e (x i).1))))).weight
        (sampleEquiv e (C i) (x i).2)) =
      ∏ i, P.weight (x i).1 * (sampleLaw (C i) (T (x i).1)).weight (x i).2
    simp only [Equiv.symm_apply_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [ih]

theorem sampleExpect_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (f : Sample Λ S → ℝ) :
    (sampleLaw S (KernelTower.transport e n T)).expect f =
      (sampleLaw S T).expect (f ∘ sampleEquiv e S) := by
  unfold FiniteLaw.expect
  apply (Fintype.sum_equiv (sampleEquiv e S) _ _ ?_).symm
  intro x
  simp only [sampleWeight_transport, Function.comp_apply]

theorem tiltedSampleExpect_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ)
    (g : Sample Λ S → ℝ) :
    (sampleLaw S (KernelTower.tilt n (KernelTower.transport e n T) m f)).expect g =
      (sampleLaw S (KernelTower.tilt n T m (f ∘ KernelTower.pathEquiv e n))).expect
        (g ∘ sampleEquiv e S) := by
  rw [KernelTower.tilt_transport, sampleExpect_transport]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type}

/-- A leaf keeps its label under relabeling, even when two sampled paths agree. -/
theorem pathAt_sampleEquiv (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (x : Sample Ω S) :
    pathAt S a (sampleEquiv e S x) = KernelTower.pathEquiv e n (pathAt S a x) := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    change (e (x a.1).1, pathAt (C a.1) a.2 (sampleEquiv e (C a.1) (x a.1).2)) =
      (e (x a.1).1, KernelTower.pathEquiv e n (pathAt (C a.1) a.2 (x a.1).2))
    rw [ih]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

theorem tilt_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).tilt m (fun z => f z.1) =
      (P.tilt m f).bind (fun _ => Q) := by
  ext z
  change P.weight z.1 * Q.weight z.2 * Real.exp (m*f z.1) /
      (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) =
      (P.weight z.1 * Real.exp (m*f z.1) / P.expMoment m f) * Q.weight z.2
  have hh : (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) = P.expMoment m f := by
    simp [expMoment]
  rw [hh]
  ring
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

theorem tilt_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    tilt n (prod n T U) m (fun y => f (pathFst n y)) = prod n (tilt n T m f) U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.bind (fun _ => U.1)).tilt (m 0)
        (fun z => backwardLog n (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1,pathFst n y))) =
        (T.1.tilt (m 0) (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
          (fun y => f (x,y)))).bind (fun _ => U.1)
      have hh : (fun z : Ω × Λ => backwardLog n
          (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1, pathFst n y))) =
          (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
            (fun y => f (z.1,y))) := by
        funext z
        exact backwardLog_prod_fst n (T.2 z.1) (U.2 z.2) (fun j => m j.succ)
          (fun y => f (z.1,y))
      rw [hh]
      exact FiniteLaw.tilt_bind_fst T.1 U.1 (m 0)
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
    · funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_Perturbations
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
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem perturb_factor_lower {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    (1:ℝ)/2 ≤ 1+t*D q y+u*E q y := by
  have ht' := mul_le_mul_of_nonneg_left (hD q y) (abs_nonneg t)
  have hu' := mul_le_mul_of_nonneg_left (hE q y) (abs_nonneg u)
  rw [← abs_mul, mul_one] at ht' hu'
  linarith [(abs_le.mp (ht'.trans ht)).1, (abs_le.mp (hu'.trans hu)).1]

omit [Fintype Ω] in
theorem perturb_fraction_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    |E q y / (1+t*D q y+u*E q y)| ≤ 2 := by
  have hb := perturb_factor_lower D E hD hE ht hu q y
  have hp : 0 < 1+t*D q y+u*E q y := by linarith
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith [hE q y]

omit [Fintype Ω] in
theorem perturbScore_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    |perturbScore D E t u y| ≤ 2*n := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ q, |E q y / (1+t*D q y+u*E q y)|) ≤ ∑ _q : Fin n, (2:ℝ) :=
      Finset.sum_le_sum (fun q _ => perturb_fraction_bound D E hD hE ht hu q y)
    _ = _ := by simp [mul_comm]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_path_expect (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f g : X → FinitePath Ω L → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y))
    (hg : ∀ y, Measurable (fun x => g x y)) :
    Measurable (fun x => (law L (tilt L T m (f x))).expect (g x)) := by
  induction L with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ L ih =>
    simp_rw [law_succ_expect (Ω := Ω) L]
    exact T.1.measurable_tilt_expect (m 0)
      (fun a => measurable_backwardLog L (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)) (fun b => hg (a,b)))

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

omit [Fintype Ω] in
theorem measurable_perturbLog {L n : ℕ}
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbLog (base x) (D x) (E x) (t x) (u x) y) := by
  apply (hbase y).add
  apply Finset.measurable_sum
  intro q _
  exact ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y))).log

omit [Fintype Ω] in
theorem measurable_perturbScore {L n : ℕ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbScore (D x) (E x) (t x) (u x) y) := by
  apply Finset.measurable_sum
  intro q _
  exact (hE q y).div ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y)))

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

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountableReservoir
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
namespace DilutedSpinGlass.CountableReservoir
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

theorem integrable_row {n : ℕ} {f : (Fin n → I) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : Integrable f (Measure.pi (fun _ : Fin n => ν)) := by
  apply (integrable_const B).mono' (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hf x)

end DilutedSpinGlass.CountableReservoir

namespace DilutedSpinGlass.CountableReservoir
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

omit [Countable I] [MeasurableSingletonClass I] in
/-- The countable root labels are genuinely iid under finite permutations. -/
theorem integral_pi_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : (Fin n → I) → ℝ) :
    (∫ roots, f (roots ∘ σ) ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ roots, f roots ∂Measure.pi (fun _ : Fin n => ν) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) σ).symm.integral_comp' f
  exact h

/-- A new label has precisely the same independent law as each old label. -/
theorem integral_pi_cons (n : ℕ) (f : (Fin (n+1) → I) → ℝ) {B : ℝ}
    (hf : ∀ roots, |f roots| ≤ B) :
    (∫ roots, f roots ∂Measure.pi (fun _ : Fin (n+1) => ν)) =
      ∫ i, ∫ roots, f (Fin.cons i roots) ∂Measure.pi (fun _ : Fin n => ν) ∂ν := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm.integral_comp' f
  have he : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => I) 0).symm :
      I × (Fin n → I) → (Fin (n+1) → I)) =
      (fun z : I × (Fin n → I) => Fin.cons z.1 z.2) := by
    funext labels
    exact Fin.insertNth_zero' labels.1 labels.2
  rw [he] at h
  rw [← h]
  apply integral_prod
  apply (integrable_const B).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hf (Fin.cons z.1 z.2))

omit [Countable I] [MeasurableSingletonClass I] in
theorem integral_pi_equivariant {n : ℕ} (F : (Fin n → I) → Fin n → ℝ)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) roots q, F (roots ∘ σ) q = F roots (σ q))
    (q q' : Fin n) :
    (∫ roots, F roots q ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ roots, F roots q' ∂Measure.pi (fun _ : Fin n => ν) := by
  classical
  rw [← integral_pi_perm ν (Equiv.swap q q') (fun roots => F roots q)]
  apply integral_congr_ae
  exact ae_of_all _ (fun roots => by
    dsimp only
    rw [hF, Equiv.swap_apply_left])

/-- Palm for the full shared countable reservoir. It does not delete the
selected type or truncate the other types in the remaining law. -/
theorem poisson_add_label (s : ℝ≥0)
    (F : (n : ℕ) → (Fin n → I) → Fin n → ℝ) {B : ℝ}
    (hB : ∀ n roots q, |F n roots q| ≤ B)
    (hF : ∀ n (σ : Equiv.Perm (Fin n)) roots q, F n (roots ∘ σ) q = F n roots (σ q)) :
    (∫ n : ℕ, ∫ roots, ∑ q, F n roots q
      ∂Measure.pi (fun _ : Fin n => ν) ∂poissonMeasure s) =
      (s : ℝ) * ∫ n : ℕ, ∫ i, ∫ roots, F (n+1) (Fin.cons i roots) 0
        ∂Measure.pi (fun _ : Fin n => ν) ∂ν ∂poissonMeasure s := by
  let a : ℕ → ℝ := fun n => if h : 0 < n then
    ∫ roots, F n roots ⟨0,h⟩ ∂Measure.pi (fun _ : Fin n => ν) else 0
  have ha (n : ℕ) : a (n+1) =
      ∫ roots, F (n+1) roots 0 ∂Measure.pi (fun _ : Fin (n+1) => ν) := by
    simp only [a, Nat.zero_lt_succ, ↓reduceDIte]
    rfl
  have hsum (n : ℕ) :
      (∫ roots, ∑ q, F n roots q ∂Measure.pi (fun _ : Fin n => ν)) = (n : ℝ)*a n := by
    rw [integral_finsetSum _ (fun q _ => integrable_row ν (fun roots => hB n roots q))]
    by_cases hn : 0 < n
    · simp only [a, dite_eq_left hn]
      rw [show (fun q : Fin n => ∫ roots, F n roots q ∂Measure.pi (fun _ : Fin n => ν)) =
        (fun _ : Fin n => ∫ roots, F n roots ⟨0,hn⟩ ∂Measure.pi (fun _ : Fin n => ν)) from
          funext (fun q => integral_pi_equivariant ν (F n) (hF n) q ⟨0,hn⟩)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  have hi : Integrable (fun n => a (n+1)) (poissonMeasure s) := by
    apply poisson_integrable_linear s (A := B) (B := 0)
    intro n
    rw [ha]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one, zero_mul, add_zero] using
      (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin (n+1) => ν))
        (f := fun roots => F (n+1) roots 0) (C := B)
        (ae_of_all _ (fun roots => by simpa only [Real.norm_eq_abs] using hB (n+1) roots 0)))
  simp_rw [hsum]
  rw [poisson_add_one s a hi]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [ha]
    exact integral_pi_cons ν n (fun roots => F (n+1) roots 0) (fun roots => hB (n+1) roots 0))

end DilutedSpinGlass.CountableReservoir

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem treeScore_perm (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (σ : Equiv.Perm (Fin k)) (q : Fin k) :
    treeScore S a T Q m base (roots ∘ σ) factor numerator f q =
      treeScore S a T Q m base roots factor numerator f (σ q) := by
  have h := PrescribedTree.tiltedSampleExpect_transport (rowPerm roots σ) S (tower roots L T Q) m
    (logWeight base (roots ∘ σ) factor) (fun x =>
      f (fun b => physical (roots ∘ σ) L (S.pathAt b x)) *
        (numerator (roots (σ q)) (physical (roots ∘ σ) L (S.pathAt a x)) (mark q L (S.pathAt a x)) /
          factor (roots (σ q)) (physical (roots ∘ σ) L (S.pathAt a x)) (mark q L (S.pathAt a x))))
  have heq : logWeight base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm roots σ) L =
      logWeight base roots factor := funext (fun y => logWeight_rowPerm roots σ base factor y)
  rw [heq] at h
  rw [tower_transport] at h
  refine h.trans ?_
  apply congrArg
  funext x
  simp only [Function.comp_apply, PrescribedTree.pathAt_sampleEquiv, physical_rowPerm, mark_rowPerm]

theorem abs_treeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    |treeScore S a T Q m base roots factor numerator f q| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
  have hd : |numerator (roots q) (physical roots L (S.pathAt a x))
      (mark q L (S.pathAt a x))| /
      factor (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)) ≤ 2 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
    linarith [hn (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)),
      hA (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x))]
  calc
    _ ≤ |f (fun b => physical roots L (S.pathAt b x))| * 2 :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ ≤ B * 2 := mul_le_mul_of_nonneg_right (hf _) (by norm_num)
    _ = 2 * B := mul_comm _ _

end DilutedSpinGlass.HeterogeneousMarks



namespace DilutedSpinGlass.HeterogeneousMarks
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

/-- Literal change-of-variables and successive-tilt proof of the Palm insertion.
No conditional factorization of the tilted mark rows is being assumed. -/
theorem treeScore_insertion (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    treeScore S a T Q m base (Fin.cons i roots) factor numerator f 0 =
      insertedTreeScore S a T Q m base roots i factor numerator f := by
  have h := PrescribedTree.tiltedSampleExpect_transport (split roots i) S
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
    (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
      (numerator i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
        (KernelTower.pathSnd L (S.pathAt a x)) /
        factor i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
          (KernelTower.pathSnd L (S.pathAt a x))))
  have heq : insertedLog base roots factor i ∘
      KernelTower.pathEquiv (split roots i) L = logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  have ht : KernelTower.tilt L (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) m
      (insertedLog base roots factor i) =
      KernelTower.tilt L (KernelTower.prod L
        (KernelTower.tilt L (tower roots L T Q) m (logWeight base roots factor))
        (markPrior L (Q i))) m
        (fun y => Real.log (factor i (physical roots L (KernelTower.pathFst L y))
          (KernelTower.pathSnd L y))) := by
    rw [← KernelTower.tilt_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
      (logWeight base roots factor), KernelTower.tilt_insertion]
    rfl
  rw [ht] at h
  simp only [Function.comp_def, PrescribedTree.pathAt_sampleEquiv,
    physical_split, mark_split_zero] at h
  change _ = insertedTreeScore S a T Q m base roots i factor numerator f
  exact h.symm

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Full countable-type Palm for the literal tilted tree statistic. Its right
side uses the same original reservoir, plus one independently sampled mark. -/
theorem full_reservoir_palm {L : ℕ} (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    (∫ n : ℕ, ∫ roots, ∑ q, treeScore S a T Q m base roots factor numerator f q
      ∂Measure.pi (fun _ : Fin n => ν) ∂poissonMeasure s) =
      (s : ℝ) * ∫ n : ℕ, ∫ i, ∫ roots,
        insertedTreeScore S a T Q m base roots i factor numerator f
          ∂Measure.pi (fun _ : Fin n => ν) ∂ν ∂poissonMeasure s := by
  rw [CountableReservoir.poisson_add_label ν s
    (fun n roots q => treeScore S a T Q m base roots factor numerator f q)
    (fun _ roots q => abs_treeScore_le S a T Q m base roots factor numerator f q hf hn hA)
    (fun _ σ roots q => treeScore_perm S a T Q m base roots factor numerator f σ q)]
  simp_rw [treeScore_insertion]

end DilutedSpinGlass.HeterogeneousMarks

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSteps
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} {A : I → Type} {L n : ℕ}

theorem selectedCoefficient_bound (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) :
    |selectedCoefficient roots sel D q y| ≤ 1 := by
  unfold selectedCoefficient
  split
  · exact hD _ _ _
  · norm_num

/-- Every unselected term remains in the same log weight and the same finite
mark prior. This is an identity, not a distributional truncation. -/
theorem selected_perturbLog_eq (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.perturbLog (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      logWeight base roots (selectedFactor sel fixed D E t u) := by
  funext y
  unfold KernelTower.perturbLog otherLog logWeight
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedFactor,selectedCoefficient,h]

end DilutedSpinGlass.HeterogeneousMarks
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootParam
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
variable {X I Y U : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] [MeasurableSpace U] {M : ℕ}

/-- Joint measurability through both random counts, with an external parameter. -/
theorem measurable_packRoot_param
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → U → ℝ}
    (hF : ∀ k n, Measurable (fun z : ((RootPath Y M × RootPath X k) × RootPath I n) × U => F z.1.1.1 k z.1.1.2 n z.1.2 z.2)) :
    Measurable (fun z : FullRootState Y X I M × U => packRoot (fun h k x n y => F h k x n y z.2) z.1) := by
  have hn (k : ℕ) : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × Sigma (RootPath I) =>
      F z.1.1.1 k z.1.1.2 z.2.1 z.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × RootPath X k) × U) n y => F z.1.1 k z.1.2 n y z.2)
      (fun n => (hF k n).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  have hk : Measurable (fun z : ((RootPath Y M × Sigma (RootPath I)) × U) × Sigma (RootPath X) =>
      F z.1.1.1 z.2.1 z.2.2 z.1.1.2.1 z.1.1.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × Sigma (RootPath I)) × U) k x => F z.1.1 k x z.1.2.1 z.1.2.2 z.2)
      (fun k => (hn k).comp (((measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd).prodMk measurable_fst.fst.snd))
  exact hk.comp (((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd).prodMk measurable_fst.snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

omit [MeasurableSpace U] in
theorem fullRoot_count_memLp :
    MemLp (fun z : FullRootState Y X I M => (z.2.2.1 : ℝ)) 2 (fullRootLaw ξ μ ν r s) := by
  exact ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullSelectedError
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_nonneg (z : FullRootState Y X I M) (u center : ℝ) :
    0 ≤ fullSelectedDeviation T Q m base sel fixed D E t z u center :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) (center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤ 2*(z.2.2.1:ℝ)+|center| := by
  apply (FiniteLaw.expect_mono _ (fun y => (abs_sub _ _).trans
    (add_le_add (KernelTower.perturbScore_bound _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu y) le_rfl))).trans_eq
  exact FiniteLaw.expect_const _ _

theorem measurable_fullSelectedDeviation
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {center : ℝ → ℝ} (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedDeviation T Q m base sel fixed D E t z.1 z.2 (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    fullSelectedDeviation T Q m base sel fixed D E t (h,⟨k,x⟩,⟨n,y⟩) u (center u))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      fullSelectedDeviation T Q m base sel fixed D E t (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) z.1.2 (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    dsimp only [fullSelectedDeviation]
    apply KernelTower.measurable_path_expect L (tower (rootArray n y) L T Q) m
      (f := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        KernelTower.perturbLog (otherLog (base z.1.1 k z.1.2) (rootArray n y) sel fixed)
          (selectedCoefficient (rootArray n y) sel D) (selectedCoefficient (rootArray n y) sel E) t z.2)
      (g := fun z : (RootPath Y M × RootPath X k) × ℝ => fun w =>
        |KernelTower.perturbScore (selectedCoefficient (rootArray n y) sel D)
          (selectedCoefficient (rootArray n y) sel E) t z.2 w-center z.2|)
    · apply KernelTower.measurable_perturbLog
      · intro w
        exact ((hb k (physical (rootArray n y) L w)).comp measurable_fst).add measurable_const
      · exact fun _ _ => measurable_const
      · exact fun _ _ => measurable_const
      · exact measurable_const
      · exact measurable_snd
    · intro w
      exact ((KernelTower.measurable_perturbScore
        (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel D)
        (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel E)
        (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
        (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd w).sub
          (hc.comp measurable_snd)).abs
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ParameterProduct
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory

/-- Selecting one type in the complete dictionary law keeps its unmodified
conditional site law. This is the scalar normalization in the Palm identity. -/
lemma integral_select_product {J Z : Type*} [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [Countable J] [Countable Z] [MeasurableSingletonClass Z]
    [DecidableEq J] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (j : J) (F : J × Z → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    (∫ x, if x.1 = j then F x else 0 ∂ν.prod τ) =
      ν.real {j} * ∫ z, F (j,z) ∂τ := by
  have hm : Measurable (fun x : J × Z => if x.1 = j then F x else 0) := measurable_of_countable _
  have hi : Integrable (fun x : J × Z => if x.1 = j then F x else 0) (ν.prod τ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; split_ifs; exact hF x; simpa using hB)
  rw [integral_prod _ hi]
  have he : (fun x : J => ∫ z, if x = j then F (x,z) else 0 ∂τ) =
      Set.indicator {j} (fun x => ∫ z, F (x,z) ∂τ) := by
    funext x
    by_cases hx : x = j
    · simp [hx]
    · simp [hx]
  rw [he,integral_indicator (measurableSet_singleton j),integral_singleton]
  rfl

/-- Inserting with a pushed-forward site law is genuinely independent of the
old reservoir. The old state law is not changed by this relabeling. -/
lemma integral_fresh_label {W J Z : Type*} [MeasurableSpace W] [MeasurableSpace J]
    [MeasurableSpace Z] (ρ : Measure W) [IsProbabilityMeasure ρ]
    (τ : Measure Z) [IsProbabilityMeasure τ] (label : Z → J) (hl : Measurable label)
    (F : W × J → ℝ) (hF : Measurable F) {B : ℝ} (hb : ∀ z, |F z| ≤ B) :
    (∫ z, F z ∂ρ.prod (τ.map label)) = ∫ w, ∫ z, F (w,label z) ∂τ ∂ρ := by
  have hi : Integrable F (ρ.prod (τ.map label)) :=
    Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun w => integral_map hl.aemeasurable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeAnchor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every prescribed old leaf has exactly the one-path marginal, including
through shared prefixes and arbitrary (possibly unary) stretches. -/
theorem pathAt_expect {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω n) (f : FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x)) = (KernelTower.law n T).expect f := by
  induction S with
  | leaf =>
    change KernelTower.unitLaw.expect (fun _ => f ()) = _
    change KernelTower.unitLaw.expect (fun _ => f ()) = KernelTower.unitLaw.expect f
    apply FiniteLaw.expect_congr
    intro x
    cases x
    rfl
  | @node n k C ih =>
    rcases T with ⟨P,Q⟩
    rcases a with ⟨i,a⟩
    change (FiniteLaw.pi (fun i : Fin k => P.bind (fun z => sampleLaw (C i) (Q z)))).expect
      (fun x => f ((x i).1, (C i).pathAt a (x i).2)) = _
    have he := FiniteLaw.expect_pi_marginal
      (fun i : Fin k => P.bind (fun z => sampleLaw (C i) (Q z))) i
      (fun y => f (y.1, (C i).pathAt a y.2))
    refine he.trans ?_
    erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect]
    apply P.expect_congr
    intro z
    exact ih i a (Q z) (fun y => f (z,y))

/-- The anchor-marginal argument in `pert:score-identity`, before root
averaging. It uses the actual old-tree joint law, not independent replicas. -/
theorem anchor_centered_bound {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω n) (f : Sample Ω S → ℝ) (g : FinitePath Ω n → ℝ)
    {B center : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    |(S.sampleLaw T).expect (fun x => f x * g (S.pathAt a x)) -
      (S.sampleLaw T).expect f * center| ≤
      B * (KernelTower.law n T).expect (fun y => |g y-center|) := by
  have heq : (S.sampleLaw T).expect (fun x => f x * g (S.pathAt a x)) -
      (S.sampleLaw T).expect f * center =
      (S.sampleLaw T).expect (fun x => f x * (g (S.pathAt a x)-center)) := by
    simp only [mul_sub,FiniteLaw.expect_sub,FiniteLaw.expect_mul_right]
  rw [heq]
  have habs : |(S.sampleLaw T).expect (fun x => f x * (g (S.pathAt a x)-center))| ≤
      (S.sampleLaw T).expect (fun x => |f x * (g (S.pathAt a x)-center)|) := by
    apply abs_le.mpr
    constructor
    · have hh := (S.sampleLaw T).expect_mono (fun x => neg_abs_le (f x * (g (S.pathAt a x)-center)))
      simpa only [FiniteLaw.expect_neg] using hh
    · exact (S.sampleLaw T).expect_mono (fun x => le_abs_self _)
  apply habs.trans
  calc
    _ ≤ (S.sampleLaw T).expect (fun x => B * |g (S.pathAt a x)-center|) :=
      FiniteLaw.expect_mono _ (fun x => by
        rw [abs_mul]
        exact mul_le_mul (hf x) le_rfl (abs_nonneg _) hB)
    _ = _ := by
      rw [FiniteLaw.expect_mul_left]
      exact congrArg (fun z => B*z) (pathAt_expect S a T (fun y => |g y-center|))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- Measurability of every finite prescribed-tree probability for the actual
recursively tilted conditional kernels. -/
theorem measurable_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (a : S.Sample Ω) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) := by
  induction S with
  | leaf => exact measurable_const
  | @node n k C ih =>
    change Measurable (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2)
    apply Finset.measurable_prod
    intro i _
    exact (T.1.measurable_tilt_weight (m 0)
      (fun z => KernelTower.measurable_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

theorem measurable_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) := by
  apply Finset.measurable_sum
  intro a _
  exact (measurable_tilt_sample_weight S T m hf a).mul (hg a)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SelectedTree
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
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma measurable_fullSelectedTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedTreeMean S T Q m base sel fixed D E t u f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only [selectedTreeMean]
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · intro w
    exact (hb k _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_fullSelectedTreeScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedTreeScore S a T Q m base sel fixed D E t u f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only [selectedTreeScore]
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · intro w
    exact (hb k _).add measurable_const
  · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |fullSelectedTreeMean S T Q m base sel fixed D E t u f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeScore_bound {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    |fullSelectedTreeScore S a T Q m base sel fixed D E t u f z| ≤ 2*B*(z.2.2.1:ℝ) := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul]
  have hscore := KernelTower.perturbScore_bound _ _
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu (S.pathAt a x)
  have hb := mul_le_mul (hf (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x))) hscore (abs_nonneg _) hB
  exact hb.trans_eq (by ring)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
/-- Exact old-tree/one-path estimate at every disorder realization, with the
identical selected tower used in the globally centered score error. -/
lemma fullSelectedTree_centered_bound {B center : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (z : FullRootState Y X I M) :
    |fullSelectedTreeScore S a T Q m base sel fixed D E t u f z -
      fullSelectedTreeMean S T Q m base sel fixed D E t u f z * center| ≤
      B * fullSelectedDeviation T Q m base sel fixed D E t z u center := by
  dsimp only [fullSelectedDeviation]
  rw [selected_perturbLog_eq]
  exact PrescribedTree.anchor_centered_bound S a _ _ _ hB (fun x => hf _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullTreeScore
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
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma integrable_fullSelectedTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    Integrable (fullSelectedTreeMean S T Q m base sel fixed D E t u f) (fullRootLaw ξ μ ν r s) := by
  apply (integrable_const B).mono' (measurable_fullSelectedTreeMean S T Q m base sel fixed D E t u f hb).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using fullSelectedTreeMean_bound S T Q m base sel fixed D E t u f hf z)

lemma integrable_fullSelectedTreeScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    Integrable (fullSelectedTreeScore S a T Q m base sel fixed D E t u f) (fullRootLaw ξ μ ν r s) := by
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  apply (hci.const_mul (2*B)).mono' (measurable_fullSelectedTreeScore S a T Q m base sel fixed D E t u f hb).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using fullSelectedTreeScore_bound S a T Q m base sel fixed D E t u f hB hf hD hE ht hu z)

 
theorem fullTree_score_error
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    |(∫ z, fullSelectedTreeScore S a T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) -
      (∫ z, fullSelectedTreeMean S T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) *
      (∫ z, fullSelectedRawScore T Q m base sel fixed D E t z u ∂fullRootLaw ξ μ ν r s)| ≤
      B * fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ z, fullSelectedRawScore T Q m base sel fixed D E t z u ∂P
  have hiM := integrable_fullSelectedTreeMean ξ μ ν r s S T Q m base sel fixed D E t u f hb hf
  have hiS := integrable_fullSelectedTreeScore ξ μ ν r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hh := abs_integral_le_integral_abs.trans (integral_mono
    (hiS.sub (hiM.mul_const center)).abs (hiD.const_mul B)
    (fun z => fullSelectedTree_centered_bound S a T Q m base sel fixed D E t u f hB hf z))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hiS (hiM.mul_const center),integral_mul_const,integral_const_mul] at hh
  exact hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SelectedPalm
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
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma selectedNumerator_bound (sel : I → Bool)
    (E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hE : ∀ i x y, |E i x y| ≤ 1) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |selectedNumerator sel E i x y| ≤ 1 := by
  unfold selectedNumerator
  split <;> simp_all

lemma selectedTreeScore_sum (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    selectedTreeScore S a T Q m base roots sel fixed D E t u f =
      ∑ q, treeScore S a T Q m base roots (selectedFactor sel fixed D E t u)
        (selectedNumerator sel E) f q := by
  simp only [selectedTreeScore,KernelTower.perturbScore,Finset.mul_sum,treeScore,
    ← FiniteLaw.expect_sum]
  apply FiniteLaw.expect_congr
  intro x
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedCoefficient,selectedFactor,selectedNumerator,h]

lemma selectedTreeScore_one (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    selectedTreeScore S a T Q m base roots sel fixed D E t u (fun _ => 1) =
      selectedScore T Q m base roots sel fixed D E t u := by
  simp only [selectedTreeScore,one_mul,selectedScore]
  exact PrescribedTree.pathAt_expect S a _ _

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Selected score Palm at a fixed physical realization. The whole original
root-label reservoir is retained; only one independent label/mark is inserted. -/
theorem selected_palm (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ n : ℕ, ∫ y, selectedTreeScore S a T Q m base (rootArray n y) sel fixed D E t u f
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s) =
      (s:ℝ) * ∫ n : ℕ, ∫ i, ∫ y,
        insertedTreeScore S a T Q m base (rootArray n y) i
          (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
        ∂rootLaw n (fun _ => ν) ∂ν ∂poissonMeasure s := by
  have heL (n : ℕ) := integral_rootArray_eq_pi ν n
    (fun roots => selectedTreeScore S a T Q m base roots sel fixed D E t u f)
  have heR (n : ℕ) (i : I) := integral_rootArray_eq_pi ν n
    (fun roots => insertedTreeScore S a T Q m base roots i
      (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f)
  simp_rw [heL,heR,selectedTreeScore_sum]
  exact full_reservoir_palm ν S a s T Q m base _ _ f hf (selectedNumerator_bound sel E hE) hA

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullPalm
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
open scoped NNReal BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

lemma measurable_treeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin n)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => treeScore S a T Q m (base z) roots factor numerator f q) := by
  unfold treeScore
  refine PrescribedTree.measurable_tilt_sample_expect S (tower roots L T Q) m ?_ ?_
  · exact fun w => (hb _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_selectedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => selectedTreeScore S a T Q m (base z) roots sel fixed D E t u f) := by
  unfold selectedTreeScore
  refine PrescribedTree.measurable_tilt_sample_expect S (tower roots L T Q) m ?_ ?_
  · exact fun w => (hb _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_insertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => insertedTreeScore S a T Q m (base z) roots i factor numerator f) := by
  simpa only [treeScore_insertion] using measurable_treeScore S a T Q m base (Fin.cons i roots) factor numerator f 0 hb

lemma abs_insertedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i x y, |numerator i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ factor i x y) :
    |insertedTreeScore S a T Q m base roots i factor numerator f| ≤ 2*B := by
  rw [← treeScore_insertion]
  exact abs_treeScore_le S a T Q m base _ factor numerator f 0 hf hn hA

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
lemma measurable_averagedInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => averagedInsertedTreeScore ν S a T Q m (base z) roots factor numerator f) := by
  have hh : Measurable (fun z : Z × I => insertedTreeScore S a T Q m (base z.1) roots z.2 factor numerator f) := by
    apply measurable_from_prod_countable_left
    exact fun i => measurable_insertedTreeScore S a T Q m base roots i factor numerator f hb
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

omit [Countable I] [MeasurableSingletonClass I] in
lemma abs_averagedInsertedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i x y, |numerator i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ factor i x y) :
    |averagedInsertedTreeScore ν S a T Q m base roots factor numerator f| ≤ 2*B := by
  have hh := norm_integral_le_of_norm_le_const (μ := ν) (C := 2*B)
    (f := fun i => insertedTreeScore S a T Q m base roots i factor numerator f)
    (ae_of_all _ (fun i => by simpa only [Real.norm_eq_abs] using abs_insertedTreeScore_le S a T Q m base roots i factor numerator f hf hn hA))
  simpa only [averagedInsertedTreeScore,Real.norm_eq_abs,probReal_univ,mul_one] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I J X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma selectedParameterFactor_eq (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (j : J) (u : J → ℝ) :
    selectedFactor (fun i => decide (key i = j)) (parameterFactor key a b t D E u)
      D E (t j) (boundParameter (a j) (b j) (u j)) = parameterFactor key a b t D E u := by
  funext i x y
  by_cases h : key i = j <;> simp [selectedFactor,parameterFactor,h]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ParameterRate
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
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

lemma inserted_eq_external (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    insertedTreeScore S a T Q m base roots i factor numerator f =
      externalTreeScore S a T Q m base roots i factor (factor i) (numerator i) f := rfl

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalTaylor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

lemma measurable_externalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => externalTreeScore S a T Q m (base z) roots i old new E f) := by
  unfold externalTreeScore
  simp_rw [← KernelTower.tilt_prod_fst,KernelTower.tilt_insertion]
  refine PrescribedTree.measurable_tilt_sample_expect S
    (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) m ?_ ?_
  · exact fun y => ((hb _).add measurable_const).add measurable_const
  · exact fun x => measurable_const

lemma abs_externalTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ x y, |E x y| ≤ 1) (hA : ∀ x y, 1/2 ≤ new x y) :
    |externalTreeScore S a T Q m base roots i old new E f| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  let xa := physical roots L (KernelTower.pathFst L (S.pathAt a x))
  let ya := KernelTower.pathSnd L (S.pathAt a x)
  have hp : 0 < new xa ya := lt_of_lt_of_le (by norm_num) (hA xa ya)
  change |f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) * (E xa ya/new xa ya)| ≤ 2*B
  rw [abs_mul,abs_div,abs_of_pos hp]
  have hq : |E xa ya| / new xa ya ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    linarith [hE xa ya,hA xa ya]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))))
  calc
    _ ≤ B*2 := mul_le_mul (hf _) hq (div_nonneg (abs_nonneg _) hp.le) hB
    _ = 2*B := mul_comm _ _

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRootPalm
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
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ν : Measure I) [IsProbabilityMeasure ν]

lemma selected_palm_averaged (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ n : ℕ, ∫ y, selectedTreeScore S a T Q m base (rootArray n y) sel fixed D E t u f
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s) =
      (s:ℝ) * ∫ n : ℕ, ∫ y,
        averagedInsertedTreeScore ν S a T Q m base (rootArray n y)
          (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s := by
  rw [selected_palm ν S a s T Q m base sel fixed D E t u f hf hE hA]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro n
  apply integral_integral_swap
  exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (2*B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.uncurry] using
      abs_insertedTreeScore_le S a T Q m base (rootArray n z.2) z.1 _ _ f hf (selectedNumerator_bound sel E hE) hA))

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- Full-root Palm identity, including the original physical Poisson/sample
and field laws. The surviving root law on the right is exactly the left law. -/
theorem fullRoot_selected_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ z, fullSelectedTreeScore S a T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) =
      (s:ℝ) * ∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f z ∂fullRootLaw ξ μ ν r s := by
  let F := fun h k x n y => selectedTreeScore S a T Q m (base h k x) (rootArray n y) sel fixed D E t u f
  let G := fun h k x n y => averagedInsertedTreeScore ν S a T Q m (base h k x) (rootArray n y)
    (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedTreeScore S a T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) sel fixed D E t u f (hb k)
  have hG (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => G z.1.1 k z.1.2 n z.2) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_averagedInsertedTreeScore ν S a T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) _ _ f (hb k)
  have hFb (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |F h k x n y| ≤ 2*B+0*(k:ℝ)^2+2*B*(n:ℝ)^2 := by
    have hh := fullSelectedTreeScore_bound S a T Q m base sel fixed D E t u f hB hf hD hE ht hu (h,⟨k,x⟩,⟨n,y⟩)
    have hn : (n:ℝ) ≤ 1+(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1), (show 0 ≤ (n:ℝ) by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*B by positivity)
    dsimp only [fullSelectedTreeScore,packRoot] at hh
    dsimp only [F]
    nlinarith
  have hGb (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |G h k x n y| ≤ 2*B+0*(k:ℝ)^2+0*(n:ℝ)^2 := by
    simpa only [zero_mul,add_zero] using abs_averagedInsertedTreeScore_le ν S a T Q m (base h k x) (rootArray n y) _ _ f hf (selectedNumerator_bound sel E hE) hA
  change (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) = (s:ℝ) * ∫ z, packRoot G z ∂fullRootLaw ξ μ ν r s
  rw [integral_fullRootLaw_quadratic ξ μ ν r s hF hFb,
    integral_fullRootLaw_quadratic ξ μ ν r s hG hGb]
  dsimp only [F,G]
  simp_rw [selected_palm_averaged ν S a s T Q m _ sel fixed D E t u f hf hE hA,
    integral_const_mul]

end DilutedSpinGlass.HeterogeneousMarks
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
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

lemma measurable_rootExternalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old new E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × I => rootExternalTreeScore S a T Q m base old new E f z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  dsimp only [rootExternalTreeScore]
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  exact measurable_externalTreeScore S a T Q m
    (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) i old (new i) (E i) f (hb k)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PalmError
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
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeScore_one (z : FullRootState Y X I M) :
    fullSelectedTreeScore S a T Q m base sel fixed D E t u (fun _ => 1) z =
      fullSelectedRawScore T Q m base sel fixed D E t z u := by
  exact selectedTreeScore_one S a T Q m (base z.1 z.2.1.1 z.2.1.2)
    (rootArray z.2.2.1 z.2.2.2) sel fixed D E t u

/-- The Palm covariance bound under the same complete original reservoir.
Normalization by a type mass `c` can be done after this identity; no root
Poisson families have been deleted or resampled. -/
theorem fullRoot_palm_error
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) (hs : 0 < s) :
    |(∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f z ∂fullRootLaw ξ μ ν r s) -
      (∫ z, fullSelectedTreeMean S T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) *
      (∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) (fun _ => 1) z ∂fullRootLaw ξ μ ν r s)| ≤
      B * fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u / (s:ℝ) := by
  have hh := fullTree_score_error ξ μ ν r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu
  rw [fullRoot_selected_palm ν ξ μ r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu hA] at hh
  have hone := fullRoot_selected_palm ν ξ μ r s S a T Q m base sel fixed D E t u (fun _ => 1)
    hb (by norm_num : (0:ℝ) ≤ 1) (by intro x; norm_num : ∀ x, |(1:ℝ)| ≤ 1) hD hE ht hu hA
  simp_rw [fullSelectedTreeScore_one] at hone
  rw [hone] at hh
  have hsr : (0:ℝ) < s := by exact_mod_cast hs
  rw [mul_left_comm _ (s:ℝ), ← mul_sub,abs_mul,abs_of_pos hsr] at hh
  exact (le_div_iff₀ hsr).mpr (by nlinarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_DictionaryPalm
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

lemma insertedTreeScore_selected (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    insertedTreeScore S a T Q m base roots i (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f =
      if sel i then externalTreeScore S a T Q m base roots i (selectedFactor sel fixed D E t u)
        (fun x y => 1+t*D i x y+u*E i x y) (E i) f else 0 := by
  rw [inserted_eq_external]
  cases hi : sel i
  · have hn : selectedNumerator sel E i = fun _ _ => 0 := by funext x y; simp only [selectedNumerator,hi,Bool.false_eq_true,ite_false]
    rw [hn]
    simp only [externalTreeScore,zero_div,mul_zero,FiniteLaw.expect_const,Bool.false_eq_true,ite_false]
  · have hn : selectedNumerator sel E i = E i := by funext x y; simp only [selectedNumerator,hi,ite_true]
    have ha : selectedFactor sel fixed D E t u i = fun x y => 1+t*D i x y+u*E i x y := by
      funext x y
      simp only [selectedFactor,hi,ite_true]
    rw [hn,ha]
    simp only [ite_true]

variable {J Z X Y : Type} [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {M : ℕ}
    {C : J × Z → Type} [∀ i, Fintype (C i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (C i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (fixed D E : (i : J × Z) → FinitePath Ω L → FinitePath (C i) L → ℝ)
    (j : J) (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- The exact mass of a selected type emerges from the full law, with its
site average independent of the unchanged complete reservoir. -/
lemma fullInserted_select_type
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ 1+t*D i x y+u*E i x y) :
    (∫ z, fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base
      (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u)
      (selectedNumerator (fun i => decide (i.1 = j)) E) f z ∂fullRootLaw ξ μ (ν.prod τ) r s) =
      ν.real {j} * externalAverage ξ μ (ν.prod τ) (τ.map (fun z => (j,z))) r s S a T Q m base
        (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) D E f t u := by
  let old := selectedFactor (fun i : J × Z => decide (i.1 = j)) fixed D E t u
  let F : FullRootState Y X (J × Z) M × (J × Z) → ℝ := fun z =>
    rootExternalTreeScore S a T Q (fun l => m l.succ) base old
      (fun i x y => 1+t*D i x y+u*E i x y) E f z.1 z.2
  have hFm : Measurable F := measurable_rootExternalTreeScore S a T Q _ base old _ E f hb
  have hFb (z) : |F z| ≤ 2*B :=
    abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old _ _ f hf (hE z.2) (hA z.2)
  have he (z : FullRootState Y X (J × Z) M) :
      fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base old
        (selectedNumerator (fun i => decide (i.1 = j)) E) f z =
        ν.real {j} * ∫ q, F (z,(j,q)) ∂τ := by
    dsimp only [fullInsertedTreeScore,packRoot,averagedInsertedTreeScore,old]
    simp_rw [insertedTreeScore_selected]
    simpa only [decide_eq_true_eq,F,rootExternalTreeScore,packRoot,old] using
      integral_select_product ν τ j (fun i => F (z,i)) (by positivity) (fun i => hFb (z,i))
  change (∫ z, fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base old
    (selectedNumerator (fun i => decide (i.1 = j)) E) f z ∂fullRootLaw ξ μ (ν.prod τ) r s) = _
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  unfold externalAverage
  exact (integral_fresh_label (fullRootLaw ξ μ (ν.prod τ) r s) τ (fun q => (j,q))
    (measurable_const.prodMk measurable_id) F hFm hFb).symm

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalAverageTaylor
attribute [-instance] _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

lemma affine_two_lower {d e t u : ℝ} (hd : |d| ≤ 1) (he : |e| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) : 1/2 ≤ 1+t*d+u*e := by
  have htd : |t*d| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg t,abs_nonneg d]
  have hue : |u*e| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg u,abs_nonneg e]
  linarith [(abs_le.mp htd).1,(abs_le.mp hue).1]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_NormalizedPalm
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (fixed D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

 
theorem normalized_dictionary_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor (fun i => decide (i.1 = j)) fixed D E t u i x y)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S a T Q m base
      (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) D E f t u| ≤
      B * fullSelectedError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        (fun i => decide (i.1 = j)) fixed D E t u / (ν.real {j}*(s:ℝ)) := by
  have haff (i x y) : 1/2 ≤ 1+t*D i x y+u*E i x y := by
    have hd := mul_le_mul ht (hD i x y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
    have he := mul_le_mul hu (hE i x y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
    rw [← abs_mul] at hd he
    linarith [(abs_le.mp hd).1,(abs_le.mp he).1]
  have hh := fullRoot_palm_error ξ μ (ν.prod τ) r s S a T Q (fun l => m l.succ) base
    (fun i => decide (i.1 = j)) fixed D E t u f hb hB hf hD hE ht hu hA hs
  rw [fullInserted_select_type ξ μ ν τ r s S a T Q m base fixed D E j t u f hb hB hf hE haff,
    fullInserted_select_type ξ μ ν τ r s S a T Q m base fixed D E j t u (fun _ => 1) hb
      (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hE haff] at hh
  change |ν.real {j} * _ - oldTreeAverage ξ μ (ν.prod τ) r s S T Q (fun l => m l.succ) base
    (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) f * (ν.real {j} * _)| ≤ _ at hh
  rw [mul_left_comm _ (ν.real {j}), ← mul_sub,abs_mul,abs_of_pos hc] at hh
  unfold externalCovariance
  have hh' := (le_div_iff₀ hc).mpr (by simpa only [mul_comm (ν.real {j})] using hh)
  simpa only [div_div, mul_comm (s:ℝ)] using hh'

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ParameterPalm
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (a b t : J → ℝ) (D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- Actual parameter-score Palm inequality: all old factors are the literal
full dictionary factors at u, including the selected type. -/
theorem parameter_dictionary_palm_sat_oai
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S anchor T Q m base
      (parameterFactor Prod.fst a b t D E u) D E f (t j) (boundParameter (a j) (b j) (u j))| ≤
      B * (parameterError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        Prod.fst a b t D E j u / (ν.real {j}*(s:ℝ))) := by
  have hu (j : J) : |boundParameter (a j) (b j) (u j)| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI j (boundParameter_mem (hab j) (u j))).1],
      (hI j (boundParameter_mem (hab j) (u j))).2⟩
  have hA (i : J × Z) (x y) : 1/2 ≤ parameterFactor Prod.fst a b t D E u i x y :=
    affine_two_lower (hD i x y) (hE i x y) (ht i.1) (hu i.1)
  have he := selectedParameterFactor_eq Prod.fst a b t D E j u
  have hh := normalized_dictionary_palm ξ μ ν τ r s S anchor T Q m base
    (parameterFactor Prod.fst a b t D E u) D E j (t j) (boundParameter (a j) (b j) (u j)) f
    hb hB hf hD hE (ht j) (hu j) (by rw [he]; exact hA) hc hs
  rw [he] at hh
  simpa only [parameterError,mul_div_assoc] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm_sat_oai := @OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm_sat_oai
