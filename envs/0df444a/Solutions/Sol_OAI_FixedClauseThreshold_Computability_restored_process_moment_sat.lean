-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.restored_process_moment_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:51:49.025829+00:00
-- url     : https://prove2.me/submissions/66c56d8e-9bd0-44ec-b1d0-4f1cf68362dd

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A002

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
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedCandidates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem uniform_prod_expect {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (A × B)).expect f =
      (FiniteLaw.uniform : FiniteLaw A).expect (fun a =>
        (FiniteLaw.uniform : FiniteLaw B).expect (fun b => f (a, b))) := by
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, mul_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frozenFraction_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) : 0 ≤ frozenFraction U := by
  apply FiniteLaw.expect_nonneg
  intro l
  split <;> norm_num

theorem frozenFraction_le_half {n : ℕ} [NeZero n]
    {U : Finset (DeletionCandidate n)} (hU : U.Nonempty) :
    frozenFraction U ≤ (1 : ℝ) / 2 := by
  classical
  obtain ⟨x, hx⟩ := hU
  unfold frozenFraction
  rw [uniform_prod_expect]
  calc
    _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin n)).expect (fun _ => (1 : ℝ) / 2) := by
      apply FiniteLaw.expect_mono
      intro v
      calc
        _ ≤ (FiniteLaw.uniform : FiniteLaw Bool).expect
            (fun s => if literalFalse x (v, s) then 1 else 0) := by
          apply FiniteLaw.expect_mono
          intro s
          by_cases hf : frozenLiteral U (v, s)
          · rw [ite_eq_left hf, ite_eq_left (hf x hx)]
          · rw [ite_eq_right hf]
            split <;> norm_num
        _ ≤ 1 / 2 := by
          cases h : x v with
          | none => norm_num [literalFalse, h, FiniteLaw.expect, FiniteLaw.uniform] <;> split_ifs <;> first | contradiction | norm_num
          | some b => cases b <;>
              norm_num [literalFalse, h, FiniteLaw.expect, FiniteLaw.uniform, Fintype.sum_bool]
    _ = _ := FiniteLaw.expect_const _ _

theorem oneTestKill_eq {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) :
    oneTestKill U k = frozenFraction U ^ k := by
  classical
  have hi (c : Fin k → SignedLiteral n) :
      (if ∀ x ∈ U, ∀ l, literalFalse x (c l) then (1 : ℝ) else 0) =
        ∏ l, if frozenLiteral U (c l) then 1 else 0 := by
    rw [Fintype.prod_boole]
    congr 1
    simp only [frozenLiteral]
    apply propext
    constructor
    · intro h l x hx
      exact h x hx l
    · intro h x hx l
      exact h l x hx
  unfold oneTestKill
  simp_rw [hi]
  rw [uniformFiniteLaw_pi]
  calc
    _ = ∏ _ : Fin k, (FiniteLaw.uniform : FiniteLaw (SignedLiteral n)).expect
        (fun l => if frozenLiteral U l then 1 else 0) :=
      FiniteLaw.expect_pi_product
        (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (SignedLiteral n)))
        (fun _ l => if frozenLiteral U l then 1 else 0)
    _ = _ := by simp only [frozenFraction, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ReplacementEstimate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

private theorem cubic_loss_bound {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) :
    x^2 - d * x^3 / 2 ≤ 1 / d^2 := by
  have hp : (d*x)^2 - (d*x)^3 / 2 ≤ 1 := by
    have hs := mul_nonneg (sq_nonneg (d*x - 4/3))
      (show 0 ≤ d*x + 2/3 by positivity)
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

theorem two_to_three_exp_replacement {x d : ℝ}
    (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) (hd : 0 < d) :
    x^2 - (1 - Real.exp (-d*x^3)) ≤ 1 / d^2 := by
  let z := d*x^3
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have he : Real.exp (-z) ≤ 1 / (1+z) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity : 0 < 1+z) (by
      simpa only [add_comm] using Real.add_one_le_exp z)
  have he' : Real.exp (-d*x^3) ≤ 1 / (1+z) := by
    simpa only [z, neg_mul] using he
  by_cases hz1 : z ≤ 1
  · have hlin : z / 2 ≤ 1 - Real.exp (-d*x^3) := by
      have ht : 1 / (1+z) ≤ 1-z/2 := by
        apply (div_le_iff₀ (by positivity : 0 < 1+z)).mpr
        nlinarith
      linarith
    have hc := cubic_loss_bound hx hd
    dsimp [z] at hlin
    linarith
  · have hlarge : 1 / (1+z) ≤ (1:ℝ)/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 1+z)).mpr
      linarith
    have hxx : x^2 ≤ (1:ℝ)/4 := by nlinarith
    have hpos : 0 ≤ 1 / d^2 := by positivity
    linarith

theorem two_to_three_replacement {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1/2)
    {d : ℕ} (hd : 0 < d) :
    x^2 - (1 - (1-x^3)^d) ≤ 1 / (d : ℝ)^2 := by
  have hbase : 0 ≤ 1-x^3 := by nlinarith [sq_nonneg x]
  have he : (1-x^3)^d ≤ Real.exp (-((d : ℝ)*x^3)) := by
    calc
      _ ≤ (Real.exp (-(x^3)))^d := by
        apply pow_le_pow_left₀ hbase
        have := Real.add_one_le_exp (-(x^3))
        linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hr := two_to_three_exp_replacement hx hxhalf (show (0:ℝ) < d by exact_mod_cast hd)
  simp only [neg_mul] at hr
  linarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_BatchKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem batchKillProbability_ge {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) :
    1 - (1 - oneTestKill U k)^d ≤ batchKillProbability U k d := by
  let f : (Fin k → SignedLiteral n) → ℝ := fun c => if ¬testKills U c then 1 else 0
  have hf : (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect f =
      1 - oneTestKill U k := by
    have he (c : Fin k → SignedLiteral n) :
        f c = 1 - (if testKills U c then 1 else 0) := by
      dsimp [f]
      by_cases h : testKills U c <;> simp [h]
    rw [show f = (fun c => 1 - (if testKills U c then 1 else 0)) from funext he]
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
    simp only [oneTestKill, testKills]
    congr 1
    apply FiniteLaw.expect_congr
    intro c
    split_ifs with h
    · exact ite_eq_left h
    · exact ite_eq_right h
  have hp : (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
      (fun cs => ∏ j, f (cs j)) = (1 - oneTestKill U k)^d := by
    rw [uniformFiniteLaw_pi]
    calc
      _ = ∏ _ : Fin d, (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect f :=
        FiniteLaw.expect_pi_product (fun _ => FiniteLaw.uniform) (fun _ => f)
      _ = _ := by simp [hf]
  have hpoint (cs : Fin d → Fin k → SignedLiteral n) :
      1 - ∏ j, f (cs j) ≤ if batchKills U cs then 1 else 0 := by
    dsimp [f]
    rw [Fintype.prod_boole]
    by_cases h : ∀ j, ¬testKills U (cs j)
    · rw [ite_eq_left h, sub_self]
      split <;> norm_num
    · obtain ⟨j, hj⟩ := not_forall.mp h
      have hj' := not_not.mp hj
      have hb : batchKills U cs := fun x hx => ⟨j, hj' x hx⟩
      rw [ite_eq_right h, ite_eq_left hb]
      norm_num
  have hmean := (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect_mono hpoint
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, hp] at hmean
  exact hmean

theorem relaxed_one_replacement {n : ℕ} [NeZero n]
    {U : Finset (DeletionCandidate n)} (hU : U.Nonempty) {d : ℕ} (hd : 0 < d) :
    oneTestKill U 2 - 1 / (d : ℝ)^2 ≤ batchKillProbability U 3 d := by
  have hn := frozenFraction_nonneg U
  have hh := frozenFraction_le_half hU
  have hr := two_to_three_replacement hn hh hd
  have hb := batchKillProbability_ge U 3 d
  rw [oneTestKill_eq] at hb
  rw [oneTestKill_eq]
  linarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MarkovOccupation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators

theorem finiteKernelStep_mono {Ω : Type*} [Fintype Ω] (K : Ω → FiniteLaw Ω) :
    Monotone (finiteKernelStep K) := by
  intro f g h x
  exact (K x).expect_mono h

theorem finiteKernelStep_iterate_const {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (t : ℕ) (c : ℝ) :
    (finiteKernelStep K)^[t] (fun _ => c) = fun _ => c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    exact (K x).expect_const c

theorem finiteKernelStep_iterate_sub {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (t : ℕ) (f g : Ω → ℝ) :
    (finiteKernelStep K)^[t] (f-g) =
      (finiteKernelStep K)^[t] f - (finiteKernelStep K)^[t] g := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ_apply', ih]
    funext x
    exact (K x).expect_sub _ _

theorem finiteKernelStep_iterate_mul {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (t : ℕ) (c : ℝ) (f : Ω → ℝ) :
    (finiteKernelStep K)^[t] (fun x => c*f x) =
      fun x => c*((finiteKernelStep K)^[t] f x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ_apply', ih]
    funext x
    exact (K x).expect_mul_left c _

theorem sum_shift_difference_le (u : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t)
    (hu1 : ∀ t, u t ≤ 1) (M L : ℕ) :
    (∑ t ∈ Finset.range M, (u t-u (t+L))) ≤ L := by
  have hM := Finset.sum_range_add u M L
  have hL := Finset.sum_range_add u L M
  rw [Nat.add_comm L M] at hL
  have hnonneg : 0 ≤ ∑ t ∈ Finset.range L, u (M+t) :=
    Finset.sum_nonneg (fun t _ => hu0 _)
  have hbound : (∑ t ∈ Finset.range L, u t) ≤ L := by
    calc
      _ ≤ ∑ _t ∈ Finset.range L, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hu1 t)
      _ = _ := by simp
  have he : (∑ t ∈ Finset.range M, u (t+L)) =
      ∑ t ∈ Finset.range M, u (L+t) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_comm t L]
  rw [Finset.sum_sub_distrib, he]
  linarith

theorem finiteKernel_occupation {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (alive bin : Ω → ℝ)
    (ha0 : ∀ x, 0 ≤ alive x) (ha1 : ∀ x, alive x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hblock : ∀ x, δ * bin x ≤ alive x - (finiteKernelStep K)^[L] alive x)
    (M : ℕ) (x : Ω) :
    (∑ t ∈ Finset.range M, (finiteKernelStep K)^[t] bin x) ≤ (L : ℝ)/δ := by
  have hstep (t : ℕ) : δ * (finiteKernelStep K)^[t] bin x ≤
      (finiteKernelStep K)^[t] alive x - (finiteKernelStep K)^[t+L] alive x := by
    have h := (finiteKernelStep_mono K).iterate t hblock x
    rw [finiteKernelStep_iterate_mul] at h
    change δ * (finiteKernelStep K)^[t] bin x ≤
      (finiteKernelStep K)^[t] (alive - (finiteKernelStep K)^[L] alive) x at h
    rw [finiteKernelStep_iterate_sub] at h
    simpa only [Function.iterate_add_apply, Pi.sub_apply] using h
  have hbounds (t : ℕ) : 0 ≤ (finiteKernelStep K)^[t] alive x ∧
      (finiteKernelStep K)^[t] alive x ≤ 1 := by
    have hlo := (finiteKernelStep_mono K).iterate t ha0 x
    have hhi := (finiteKernelStep_mono K).iterate t ha1 x
    rw [finiteKernelStep_iterate_const] at hlo hhi
    exact ⟨hlo, hhi⟩
  apply (le_div_iff₀ hδ).mpr
  rw [mul_comm, Finset.mul_sum]
  apply (Finset.sum_le_sum (fun t _ => hstep t)).trans
  exact sum_shift_difference_le _ (fun t => (hbounds t).1) (fun t => (hbounds t).2) M L

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem candidateStep_mono {n : ℕ} [NeZero n] (k : ℕ) :
    Monotone (candidateStep (n := n) k) := by
  intro f g h U
  exact FiniteLaw.expect_mono _ (fun _ => h _)

theorem candidateStep_add_const {n : ℕ} [NeZero n] (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (c : ℝ) :
    candidateStep k (f + fun _ => c) = candidateStep k f + fun _ => c := by
  funext U
  exact (FiniteLaw.expect_add _ _ _).trans (by simp [candidateStep, Pi.add_apply])

theorem candidateStep_comm {n : ℕ} [NeZero n] (k l : ℕ) :
    Function.Commute (candidateStep (n := n) k) (candidateStep l) := by
  intro f
  funext U
  unfold candidateStep
  rw [FiniteLaw.expect_comm]
  apply FiniteLaw.expect_congr
  intro c
  apply FiniteLaw.expect_congr
  intro d
  congr 1
  ext x
  simp only [Finset.mem_filter]
  tauto

theorem candidateKill_iterate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) :
    batchKillProbability U k d = 1 - (candidateStep k)^[d] candidateAlive U := by
  rw [candidateStep_iterate]
  have he (cs : Fin d → Fin k → SignedLiteral n) :
      (if batchKills U cs then (1 : ℝ) else 0) =
        1 - candidateAlive (candidateResidual U cs) := by
    rw [candidateAlive, ← candidateResidual_empty_iff]
    by_cases h : candidateResidual U cs = ∅
    · simp [h]
    · simp [h, Finset.nonempty_iff_ne_empty]
  simp_rw [batchKillProbability, he, FiniteLaw.expect_sub, FiniteLaw.expect_const]

theorem operator_iterate_add_const {X : Type*} (A : (X → ℝ) → X → ℝ)
    (hA : ∀ f c, A (f + fun _ => c) = A f + fun _ => c)
    (m : ℕ) (f : X → ℝ) (c : ℝ) :
    A^[m] (f + fun _ => c) = A^[m] f + fun _ => c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hA, Function.iterate_succ_apply']

theorem operator_replacement {X : Type*} (A B : (X → ℝ) → X → ℝ)
    (hA : Monotone A) (hB : Monotone B)
    (hAc : ∀ f c, A (f + fun _ => c) = A f + fun _ => c)
    (hBc : ∀ f c, B (f + fun _ => c) = B f + fun _ => c)
    (hcomm : Function.Commute A B) (f : X → ℝ) (δ : ℝ)
    (hone : A f ≤ B f + fun _ => δ) (d : ℕ) :
    A^[d] f ≤ B^[d] f + fun _ => (d : ℝ)*δ := by
  induction d with
  | zero => intro x; simp
  | succ d ih =>
    have h₁ := hA.iterate d hone
    rw [operator_iterate_add_const A hAc, hcomm.iterate_left d f] at h₁
    have h₂ := hB ih
    rw [hBc, ← Function.iterate_succ_apply' B d f] at h₂
    intro x
    have h₁x := h₁ x
    have h₂x := h₂ x
    simp only [Pi.add_apply] at h₁x h₂x
    rw [Function.iterate_succ_apply]
    change A^[d] (A f) x ≤ B^[d+1] f x + ((d+1 : ℕ) : ℝ)*δ
    push_cast
    linarith

theorem relaxed_sequential_replacement {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) {d : ℕ} (hd : 0 < d) (L : ℕ) :
    batchKillProbability U 2 L - (L : ℝ)/(d : ℝ)^2 ≤
      batchKillProbability U 3 (L*d) := by
  have hone : (candidateStep (n := n) 3)^[d] candidateAlive ≤
      candidateStep 2 candidateAlive + fun _ => 1/(d : ℝ)^2 := by
    intro V
    by_cases hV : V.Nonempty
    · have h := relaxed_one_replacement hV hd
      have he : batchKillProbability V 2 1 = oneTestKill V 2 := by
        rw [candidateKill_iterate, Function.iterate_one, candidateStep]
        unfold oneTestKill
        rw [← FiniteLaw.expect_const (FiniteLaw.uniform : FiniteLaw (Fin 2 → SignedLiteral n)) 1,
          ← FiniteLaw.expect_sub]
        apply FiniteLaw.expect_congr
        intro c
        have hf : (V.filter (fun x => ¬∀ l, literalFalse x (c l))).Nonempty ↔
            ¬testKills V c := by
          constructor
          · rintro ⟨x, hx⟩ hk
            exact (Finset.mem_filter.mp hx).2 (hk x (Finset.mem_filter.mp hx).1)
          · intro hk
            by_contra he
            apply hk
            intro x hx
            by_contra hh
            exact he ⟨x, Finset.mem_filter.mpr ⟨hx, hh⟩⟩
        simp only [FiniteLaw.expect_const]
        by_cases hc : ∀ x ∈ V, ∀ l, literalFalse x (c l)
        · have he : ¬(V.filter (fun x => ¬∀ l, literalFalse x (c l))).Nonempty :=
            fun hne => (hf.mp hne) hc
          rw [candidateAlive, ite_eq_right he, ite_eq_left hc]
          norm_num
        · have he : (V.filter (fun x => ¬∀ l, literalFalse x (c l))).Nonempty := hf.mpr hc
          rw [candidateAlive, ite_eq_left he, ite_eq_right hc]
          norm_num
      rw [← he, candidateKill_iterate, candidateKill_iterate, Function.iterate_one] at h
      exact (by dsimp only [Pi.add_apply]; linarith)
    · have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      subst V
      simp [candidateStep_iterate, candidateStep, candidateResidual, candidateAlive]
  have h := operator_replacement (candidateStep (n := n) 3)^[d] (candidateStep 2)
    ((candidateStep_mono 3).iterate d) (candidateStep_mono 2)
    (operator_iterate_add_const _ (candidateStep_add_const 3) d)
    (candidateStep_add_const 2) ((candidateStep_comm 3 2).iterate_left d)
    candidateAlive (1/(d : ℝ)^2) hone L U
  rw [← Function.iterate_mul, Nat.mul_comm d L] at h
  rw [candidateKill_iterate, candidateKill_iterate]
  simp only [Pi.add_apply, mul_one_div] at h
  linarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateAlive_le_one {n : ℕ} (U : Finset (DeletionCandidate n)) :
    candidateAlive U ≤ 1 := by unfold candidateAlive; split <;> norm_num

theorem candidateStep_alive_le {n : ℕ} [NeZero n] (k : ℕ) :
    candidateStep (n := n) k candidateAlive ≤ candidateAlive := by
  intro U
  by_cases hU : U.Nonempty
  · calc
      _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect (fun _ => 1) :=
        FiniteLaw.expect_mono _ (fun _ => candidateAlive_le_one _)
      _ = candidateAlive U := by simp [candidateAlive, hU]
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simp [he, candidateStep, candidateAlive]

theorem batchKillProbability_mono {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) : Monotone (batchKillProbability U k) := by
  have hstep (d : ℕ) : (candidateStep k)^[d+1] candidateAlive ≤
      (candidateStep (n := n) k)^[d] candidateAlive := by
    rw [Function.iterate_succ_apply]
    exact (candidateStep_mono k).iterate d (candidateStep_alive_le k)
  have ha : Antitone (fun d => (candidateStep k)^[d] candidateAlive U) :=
    antitone_nat_of_succ_le (fun d => hstep d U)
  intro d e hde
  rw [candidateKill_iterate, candidateKill_iterate]
  linarith [ha hde]

theorem batchKillProbability_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : 0 ≤ batchKillProbability U k d := by
  apply FiniteLaw.expect_nonneg
  intro cs
  split <;> norm_num

theorem batchKillProbability_le_one {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : batchKillProbability U k d ≤ 1 := by
  apply (FiniteLaw.expect_mono _ (g := fun _ => 1) ?_).trans_eq (FiniteLaw.expect_const _ _)
  intro cs
  split <;> norm_num

theorem poisson_tail_dyadic (r : ℝ≥0) (L : ℕ) :
    (∫ m : ℕ, if L < m then (1 : ℝ) else 0 ∂poissonMeasure r) ≤
      Real.exp r / (2 : ℝ)^L := by
  have hi : Integrable (fun m : ℕ => if L < m then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => by split <;> norm_num)
  calc
    _ ≤ ∫ m : ℕ, (2 : ℝ)^m / (2 : ℝ)^L ∂poissonMeasure r := by
      apply integral_mono hi ((poisson_power_integrable r (by norm_num : (0 : ℝ) ≤ 2)).div_const _)
      intro m
      dsimp only
      split_ifs with hm
      · apply (le_div_iff₀ (by positivity)).mpr
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm.le)
      · positivity
    _ = _ := by rw [integral_div, poisson_power_integral r (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

theorem poissonKillProbability_truncate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k L : ℕ) (r : ℝ≥0) :
    poissonKillProbability U k r ≤ batchKillProbability U k L +
      Real.exp r / (2 : ℝ)^L := by
  have hi : Integrable (fun d => batchKillProbability U k d) (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => (abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k d], batchKillProbability_le_one U k d⟩))
  have ht : Integrable (fun d : ℕ => if L < d then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => by split <;> norm_num)
  unfold poissonKillProbability
  calc
    _ ≤ ∫ d : ℕ, batchKillProbability U k L +
        (if L < d then (1 : ℝ) else 0) ∂poissonMeasure r := by
      apply integral_mono hi ((integrable_const _).add ht)
      intro d
      dsimp only [Pi.add_apply]
      split_ifs with hd
      · linarith [batchKillProbability_le_one U k d, batchKillProbability_nonneg U k L]
      · simpa using batchKillProbability_mono U k (Nat.le_of_not_gt hd)
    _ = batchKillProbability U k L +
        (∫ d : ℕ, if L < d then (1 : ℝ) else 0 ∂poissonMeasure r) := by
      rw [integral_add (integrable_const _) ht, integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (poisson_tail_dyadic r L)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKernel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem poissonMixture_integrable_expect {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (f : Ω → ℝ) :
    Integrable (fun m => (P m).expect f) (poissonMeasure r) := by
  unfold FiniteLaw.expect
  exact integrable_finsetSum _ (fun x _ => (poisson_weight_integrable r P x).mul_const (f x))

theorem candidateBlock_expect {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k U).expect f =
      ∫ d, (candidateStep k)^[d] f U ∂poissonMeasure r := by
  rw [candidateBlock, poissonMixture_expect]
  simp only [candidateFixedBlock_expect]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonSemigroup
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem finite_expect_integral {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ x, Integrable (fun m => f m x) μ) :
    P.expect (fun x => ∫ m, f m x ∂μ) = ∫ m, P.expect (f m) ∂μ := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (P.weight x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_const_mul]

theorem candidateStep_iterate_bound {n : ℕ} [NeZero n]
    (k d : ℕ) (f : Finset (DeletionCandidate n) → ℝ) {B : ℝ}
    (hf : ∀ U, |f U| ≤ B) (U : Finset (DeletionCandidate n)) :
    |(candidateStep k)^[d] f U| ≤ B := by
  rw [← candidateFixedBlock_expect]
  exact FiniteLaw.abs_expect_le _ hf

theorem candidateBlock_comp {n : ℕ} [NeZero n]
    (r s : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock (r+s) k U).expect f =
      (candidateBlock r k U).expect (fun V => (candidateBlock s k V).expect f) := by
  let B := ∑ V : Finset (DeletionCandidate n), |f V|
  have hf : ∀ V, |f V| ≤ B := fun V =>
    Finset.single_le_sum (fun W _ => abs_nonneg (f W)) (Finset.mem_univ V)
  have hi (v : ℝ≥0) (V : Finset (DeletionCandidate n)) :
      Integrable (fun d => (candidateStep k)^[d] f V) (poissonMeasure v) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
    exact Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs] using candidateStep_iterate_bound k d f hf V)
  symm
  calc
    _ = (candidateBlock r k U).expect
        (fun V => ∫ e, (candidateStep k)^[e] f V ∂poissonMeasure s) := by
      simp only [candidateBlock_expect]
    _ = ∫ e, (candidateBlock r k U).expect
        (fun V => (candidateStep k)^[e] f V) ∂poissonMeasure s :=
      finite_expect_integral _ _ _ (hi s)
    _ = ∫ e, ∫ d, (candidateStep k)^[d] ((candidateStep k)^[e] f) U
        ∂poissonMeasure r ∂poissonMeasure s := by simp only [candidateBlock_expect]
    _ = ∫ e, ∫ d, (candidateStep k)^[e+d] f U
        ∂poissonMeasure r ∂poissonMeasure s := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun e => integral_congr_ae
        (Eventually.of_forall (fun d => by
          dsimp only
          rw [Nat.add_comm e d, Function.iterate_add_apply])))
    _ = ∫ m, (candidateStep k)^[m] f U ∂poissonMeasure (r+s) := by
      rw [add_comm r s, ← poissonMeasure_conv_poissonMeasure,
        integral_conv (by simpa only [poissonMeasure_conv_poissonMeasure] using hi (s+r) U)]
    _ = _ := (candidateBlock_expect _ _ _ _).symm

theorem poissonCandidateStep_iterate {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k m : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (poissonCandidateStep r k)^[m] f U = (candidateBlock (r*m) k U).expect f := by
  induction m generalizing U f with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, candidateBlock_expect]
    rw [integral_poissonMeasure]
    simp [zero_pow_eq, ite_div, ite_mul]
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    change (candidateBlock r k U).expect ((poissonCandidateStep r k)^[m] f) = _
    have he : (poissonCandidateStep r k)^[m] f =
        fun V => (candidateBlock (r*m) k V).expect f := funext (fun V => ih V f)
    rw [he, ← candidateBlock_comp]
    congr 2
    push_cast
    ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateSurvival
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateResidual_subset {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) : candidateResidual U cs ⊆ U := by
  classical
  exact Finset.filter_subset _ _

theorem candidateResidual_mono {n k d : ℕ} {U V : Finset (DeletionCandidate n)}
    (h : U ⊆ V) (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs ⊆ candidateResidual V cs := by
  classical
  exact Finset.filter_subset_filter _ h

theorem candidateAlive_mono {n : ℕ} :
    Monotone (candidateAlive (n := n)) := by
  intro U V h
  unfold candidateAlive
  split_ifs with hU hV
  · rfl
  · exact (hV (hU.mono h)).elim
  · norm_num
  · rfl

theorem candidateBlock_expect_mono_state {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) {f : Finset (DeletionCandidate n) → ℝ}
    (hf : Monotone f) : Monotone (fun U => (candidateBlock r k U).expect f) := by
  intro U V hUV
  simp only [candidateBlock, poissonMixture_expect]
  apply integral_mono (poissonMixture_integrable_expect r
    (fun d => candidateFixedBlock k d U) f)
    (poissonMixture_integrable_expect r (fun d => candidateFixedBlock k d V) f)
  intro d
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  exact FiniteLaw.expect_mono _ (fun cs => hf (candidateResidual_mono hUV cs))

theorem candidateBlock_expect_le_of_subset {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f g : Finset (DeletionCandidate n) → ℝ)
    (h : ∀ V ⊆ U, f V ≤ g V) :
    (candidateBlock r k U).expect f ≤ (candidateBlock r k U).expect g := by
  simp only [candidateBlock, poissonMixture_expect]
  apply integral_mono (poissonMixture_integrable_expect r _ f)
    (poissonMixture_integrable_expect r _ g)
  intro d
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  exact FiniteLaw.expect_mono _ (fun cs => h _ (candidateResidual_subset U cs))

theorem candidateBlock_survival_le {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock r k U).expect candidateAlive ≤ candidateAlive U := by
  apply (candidateBlock_expect_le_of_subset r k U candidateAlive
    (fun _ => candidateAlive U) (fun _ h => candidateAlive_mono h)).trans_eq
  exact FiniteLaw.expect_const _ _

theorem candidateBlock_occupation {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k L M : ℕ) (bin : Finset (DeletionCandidate n) → Prop)
    [DecidablePred bin] {δ : ℝ} (hδ : 0 < δ)
    (hbin : ∀ U, bin U → U.Nonempty ∧ δ ≤ poissonKillProbability U k (r*L))
    (U : Finset (DeletionCandidate n)) :
    (∑ t ∈ Finset.range M,
      (candidateBlock (r*t) k U).expect (fun V => if bin V then 1 else 0)) ≤
        (L : ℝ)/δ := by
  have hi (m : ℕ) (f : Finset (DeletionCandidate n) → ℝ) :
      (finiteKernelStep (candidateBlock r k))^[m] f U =
        (candidateBlock (r*m) k U).expect f := poissonCandidateStep_iterate r k m U f
  have h := finiteKernel_occupation (candidateBlock r k) candidateAlive
    (fun V => if bin V then 1 else 0) candidateAlive_nonneg candidateAlive_le_one hδ L
    (fun V => ?_) M U
  · simpa only [hi] using h
  · change δ * (if bin V then 1 else 0) ≤ candidateAlive V -
      (poissonCandidateStep r k)^[L] candidateAlive V
    rw [poissonCandidateStep_iterate]
    by_cases hb : bin V
    · obtain ⟨hne, hk⟩ := hbin V hb
      rw [ite_eq_left hb, mul_one, candidateAlive, ite_eq_left hne,
        candidateBlock_expect_alive]
      linarith
    · rw [ite_eq_right hb, mul_zero]
      exact sub_nonneg.mpr (candidateBlock_survival_le _ _ _)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped NNReal Classical

theorem candidateResidual_inter {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs = U ∩ candidateResidual Finset.univ cs := by
  ext x
  simp only [candidateResidual, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem candidateFixedBlock_mask {n : ℕ} [NeZero n] (k d : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateFixedBlock k d Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateFixedBlock k d U).expect f := by
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  apply FiniteLaw.expect_congr
  intro cs
  rw [candidateResidual_inter U cs]

theorem candidateBlock_mask {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateBlock r k U).expect f := by
  simp only [candidateBlock, poissonMixture_expect, candidateFixedBlock_mask]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonBlockBound
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem poisson_count_lower_half {M : ℕ} (hM : 0 < M) (μ : ℝ≥0)
    (hμ : 4 * (M : ℝ) ≤ μ) :
    (1 : ℝ)/2 ≤ ∫ m : ℕ, if M ≤ m then (1 : ℝ) else 0 ∂poissonMeasure μ := by
  have hMn : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hden : 0 < (μ : ℝ) - M := by linarith
  have hint : Integrable (fun m : ℕ => if m < M then (1 : ℝ) else 0)
      (poissonMeasure μ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => by split <;> norm_num)
  have hvar : Integrable (fun m : ℕ => ((m : ℝ)-(μ : ℝ))^2) (poissonMeasure μ) := by
    convert ((poisson_integrable_count_sq μ).sub
      ((poisson_integrable_count μ).const_mul (2*(μ : ℝ)))).add
      (integrable_const ((μ : ℝ)^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext m
    dsimp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htail : (∫ m : ℕ, if m < M then (1 : ℝ) else 0 ∂poissonMeasure μ) ≤
      (μ : ℝ) / ((μ : ℝ)-M)^2 := by
    calc
      _ ≤ ∫ m : ℕ, ((m : ℝ)-(μ : ℝ))^2 / ((μ : ℝ)-M)^2 ∂poissonMeasure μ := by
        apply integral_mono hint (hvar.div_const _)
        intro m
        dsimp only
        split_ifs with hm
        · have hm' : (m : ℝ) < M := by exact_mod_cast hm
          apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
          nlinarith [sq_nonneg ((m : ℝ)-(μ : ℝ))]
        · positivity
      _ = _ := by rw [integral_div, poisson_variance]
  have hnum : (μ : ℝ) / ((μ : ℝ)-M)^2 ≤ (1 : ℝ)/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hfour : (4 : ℝ) ≤ μ := by linarith
    have hproduct := mul_nonneg (show (0 : ℝ) ≤ μ-4*M by linarith)
      (show (0 : ℝ) ≤ μ+2*M-2 by linarith)
    have hMproduct := mul_nonneg (show (0 : ℝ) ≤ M-1 by linarith)
      (show (0 : ℝ) ≤ 9*M by positivity)
    nlinarith
  have he : (∫ m : ℕ, if M ≤ m then (1 : ℝ) else 0 ∂poissonMeasure μ) =
      1 - ∫ m : ℕ, if m < M then (1 : ℝ) else 0 ∂poissonMeasure μ := by
    have hp (m : ℕ) : (if M ≤ m then (1 : ℝ) else 0) =
        1 - (if m < M then (1 : ℝ) else 0) := by
      by_cases h : M ≤ m <;> simp [h, Nat.not_lt.mpr, Nat.lt_of_not_ge]
    simp_rw [hp]
    rw [integral_sub (integrable_const 1) hint]
    simp
  rw [he]
  linarith

theorem poisson_block_kill_lower {n M : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (hM : 0 < M) (μ : ℝ≥0)
    (hμ : 4 * (M : ℝ) ≤ μ) :
    batchKillProbability U k M / 2 ≤ poissonKillProbability U k μ := by
  have hi : Integrable (fun m => batchKillProbability U k m) (poissonMeasure μ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k m], batchKillProbability_le_one U k m⟩)
  have hj : Integrable (fun m : ℕ => if M ≤ m then (1 : ℝ) else 0)
      (poissonMeasure μ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => by split <;> norm_num)
  have h := integral_mono (hj.const_mul (batchKillProbability U k M)) hi (fun m => by
    dsimp only
    split_ifs with hm
    · simpa using batchKillProbability_mono U k hm
    · simpa using batchKillProbability_nonneg U k m)
  rw [integral_const_mul] at h
  have hl := mul_le_mul_of_nonneg_left (poisson_count_lower_half hM μ hμ)
    (batchKillProbability_nonneg U k M)
  unfold poissonKillProbability
  linarith

theorem poisson_two_to_three_block {n L d : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (hd : 0 < d) (hL : 0 < L)
    {q : ℝ} (hq : q ≤ poissonKillProbability U 2 60)
    (htail : Real.exp 60 / (2 : ℝ)^L ≤ q/4)
    (hrepl : (L : ℝ)/(d : ℝ)^2 ≤ q/4)
    (μ : ℝ≥0) (hμ : 4 * (L*d : ℕ) ≤ (μ : ℝ)) :
    q/4 ≤ poissonKillProbability U 3 μ := by
  have ht := poissonKillProbability_truncate U 2 L 60
  have hr := relaxed_sequential_replacement U hd L
  have hb := poisson_block_kill_lower U 3 (Nat.mul_pos hL hd) μ hμ
  norm_num only [NNReal.coe_ofNat] at ht
  linarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicBlocks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem dyadicLevel_pos (j : ℕ) : 0 < dyadicLevel j := by
  unfold dyadicLevel
  positivity

theorem dyadic_truncation_error (j : ℕ) :
    Real.exp 60 / (2 : ℝ)^(dyadicTruncation j) ≤ dyadicLevel j/4 := by
  have he : Real.exp 60 ≤ (2 : ℝ)^120 := by
    calc
      _ = (Real.exp 1)^60 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (4 : ℝ)^60 := pow_le_pow_left₀ (Real.exp_pos 1).le
        (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4)) 60
      _ = _ := by norm_num
  have hden : (2 : ℝ)^(dyadicTruncation j) = (2 : ℝ)^j * (2 : ℝ)^122 := by
    rw [dyadicTruncation, pow_add]
  rw [dyadicLevel, hden]
  apply (div_le_iff₀ (by positivity)).mpr
  field_simp
  nlinarith

theorem dyadic_multiplicity_pos (j : ℕ) : 0 < dyadicMultiplicity j := by
  unfold dyadicMultiplicity
  positivity

theorem dyadic_replacement_error (j : ℕ) :
    (dyadicTruncation j : ℝ) / (dyadicMultiplicity j : ℝ)^2 ≤ dyadicLevel j/4 := by
  have hp : j ≤ (j+1)/2*2 := by omega
  have hpow : (2 : ℝ)^j ≤ ((2 : ℝ)^((j+1)/2))^2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hp
  have hL : (1 : ℝ) ≤ j+122 := by exact_mod_cast (show 1 ≤ j+122 by omega)
  have hmul : (4 : ℝ)*((j:ℝ)+122)*(2:ℝ)^j ≤
      (2*((j:ℝ)+122)*(2:ℝ)^((j+1)/2))^2 := by
    have hprod := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ 4*((j:ℝ)+122) by positivity)
    have hrest := mul_nonneg
      (show (0 : ℝ) ≤ (j:ℝ)+122-1 by linarith)
      (show (0 : ℝ) ≤ 4*((j:ℝ)+122)*((2:ℝ)^((j+1)/2))^2 by positivity)
    nlinarith
  unfold dyadicTruncation dyadicMultiplicity dyadicLevel
  push_cast
  apply (div_le_iff₀ (by positivity)).mpr
  rw [show (2^j : ℝ)⁻¹ / 4 * (2*((j:ℝ)+122)*2^((j+1)/2))^2 =
      (2*((j:ℝ)+122)*2^((j+1)/2))^2 / (4*2^j) by field_simp]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem dyadic_block_kills {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (j : ℕ) (rate : ℝ≥0)
    (hrate : (1 : ℝ)/8 ≤ rate)
    (hq : dyadicLevel j ≤ poissonKillProbability U 2 60) :
    dyadicLevel j/4 ≤ poissonKillProbability U 3 (rate*dyadicBlock j) := by
  apply poisson_two_to_three_block U (dyadic_multiplicity_pos j)
    (show 0 < dyadicTruncation j by unfold dyadicTruncation; omega) hq
    (dyadic_truncation_error j) (dyadic_replacement_error j)
  simp only [dyadicBlock, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_mul,
    Nat.cast_ofNat, NNReal.coe_ofNat]
  have h := mul_le_mul_of_nonneg_right hrate
    (show (0 : ℝ) ≤ 32*(dyadicTruncation j : ℝ)*dyadicMultiplicity j by positivity)
  nlinarith

theorem dyadic_bin_occupation {n : ℕ} [NeZero n]
    (rate : ℝ≥0) (hrate : (1 : ℝ)/8 ≤ rate) (j M : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (∑ t ∈ Finset.range M, (candidateBlock (rate*t) 3 U).expect
      (fun V => if dyadicBin j V then 1 else 0)) ≤
        4*(dyadicBlock j : ℝ)/dyadicLevel j := by
  classical
  have h := candidateBlock_occupation rate 3 (dyadicBlock j) M (dyadicBin j)
    (show 0 < dyadicLevel j/4 by positivity [dyadicLevel_pos j])
    (fun V hV => ⟨hV.1, dyadic_block_kills V j rate hrate hV.2.1⟩) U
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DiscreteDelay
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators

theorem finite_fractional_moment {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    P.expect (fun ω => (f ω)^(1/5 : ℝ)) ≤ (P.expect f)^(1/5 : ℝ) := by
  exact (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1/5)
    (by norm_num : (1/5 : ℝ) ≤ 1)).le_map_sum
      (fun ω _ => P.nonneg ω) P.total (fun ω _ => hf ω)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskLifetime
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal Classical

theorem maskLifetime_nonneg {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) : 0 ≤ maskLifetime m U xs := by
  induction m generalizing U with
  | zero => exact (le_rfl : (0 : ℝ) ≤ 0)
  | succ m ih => exact add_nonneg (candidateAlive_nonneg U) (ih _ _)

theorem maskLifetime_le {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) : maskLifetime m U xs ≤ m := by
  induction m generalizing U with
  | zero => simp [maskLifetime]
  | succ m ih =>
    simp only [maskLifetime, Nat.cast_add, Nat.cast_one]
    linarith [candidateAlive_le_one U, ih (U ∩ xs 0) (Fin.tail xs)]

theorem candidateBlock_zero_expect {n : ℕ} [NeZero n] (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock 0 k U).expect f = f U := by
  rw [candidateBlock_expect, ProbabilityTheory.integral_poissonMeasure]
  simp [zero_pow_eq, ite_div, ite_mul]

theorem maskLifetime_mean {n : ℕ} [NeZero n] (r : ℝ≥0) (k m : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (maskLifetime m U) =
      ∑ t ∈ Finset.range m, (candidateBlock (r*t) k U).expect candidateAlive := by
  induction m generalizing U with
  | zero => simp [maskLifetime]
  | succ m ih =>
    rw [FiniteLaw.expect_pi_cons]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons, FiniteLaw.expect_add,
      FiniteLaw.expect_const, ih, FiniteLaw.expect_sum]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, candidateBlock_zero_expect]
    rw [add_comm (candidateAlive U)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [candidateBlock_mask r k U (fun V => (candidateBlock (r*t) k V).expect candidateAlive)]
    rw [← candidateBlock_comp]
    congr 2
    push_cast
    ring

theorem candidateBlock_kill_antitone {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    {U V : Finset (DeletionCandidate n)} (hVU : V ⊆ U) :
    poissonKillProbability U k r ≤ poissonKillProbability V k r := by
  have h := candidateBlock_expect_mono_state r k candidateAlive_mono hVU
  change (candidateBlock r k V).expect candidateAlive ≤
    (candidateBlock r k U).expect candidateAlive at h
  rw [candidateBlock_expect_alive, candidateBlock_expect_alive] at h
  linarith

theorem maskLifetime_mean_le {n : ℕ} [NeZero n] (r : ℝ≥0) (k m L : ℕ)
    (U : Finset (DeletionCandidate n)) {δ : ℝ} (hδ : 0 < δ)
    (hkill : δ ≤ poissonKillProbability U k (r*L)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (maskLifetime m U) ≤ (L : ℝ)/δ := by
  let bin := fun V : Finset (DeletionCandidate n) => V.Nonempty ∧ V ⊆ U
  have hb (V : Finset (DeletionCandidate n)) (hV : bin V) :
      V.Nonempty ∧ δ ≤ poissonKillProbability V k (r*L) :=
    ⟨hV.1, hkill.trans (candidateBlock_kill_antitone _ _ hV.2)⟩
  have he (t : ℕ) : (candidateBlock (r*t) k U).expect candidateAlive =
      (candidateBlock (r*t) k U).expect (fun V => if bin V then 1 else 0) := by
    apply le_antisymm
    · apply candidateBlock_expect_le_of_subset
      intro V hV
      by_cases hne : V.Nonempty <;> simp [candidateAlive, bin, hne, hV]
    · apply candidateBlock_expect_le_of_subset
      intro V hV
      by_cases hne : V.Nonempty <;> simp [candidateAlive, bin, hne, hV]
  rw [maskLifetime_mean]
  simp_rw [he]
  exact candidateBlock_occupation r k L m bin hδ hb U

theorem maskLifetime_fractional_moment {n : ℕ} [NeZero n] (r : ℝ≥0) (k m L : ℕ)
    (U : Finset (DeletionCandidate n)) {δ : ℝ} (hδ : 0 < δ)
    (hkill : δ ≤ poissonKillProbability U k (r*L)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ ((L : ℝ)/δ)^(1/5 : ℝ) := by
  apply (finite_fractional_moment _ _ (maskLifetime_nonneg U)).trans
  apply Real.rpow_le_rpow (FiniteLaw.expect_nonneg _ (maskLifetime_nonneg U))
    (maskLifetime_mean_le r k m L U hδ hkill) (by norm_num)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskDelay
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators Classical NNReal

theorem sixth_fifth_increment {x : ℝ} (hx : 0 ≤ x) :
    (x+1)^(6/5 : ℝ) - x^(6/5 : ℝ) ≤
      (6/5 : ℝ) * (x+1)^(1/5 : ℝ) := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (show x ≤ x+1 by linarith)
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1/5))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (x+1)^(1/5 : ℝ))
      volume x (x+1))
    (fun y hy => Real.rpow_le_rpow (hx.trans hy.1) hy.2 (by norm_num : (0 : ℝ) ≤ 1/5))
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1/5)),
    intervalIntegral.integral_const] at h
  norm_num at h
  nlinarith

theorem maskLifetime_mono {n m : ℕ} {U V : Finset (DeletionCandidate n)}
    (hUV : U ⊆ V) (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m U xs ≤ maskLifetime m V xs := by
  induction m generalizing U V with
  | zero => exact le_rfl
  | succ m ih =>
    exact add_le_add (candidateAlive_mono hUV)
      (ih (Finset.inter_subset_inter_right hUV) (Fin.tail xs))

theorem maskLifetime_empty {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) : maskLifetime m ∅ xs = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [maskLifetime, candidateAlive, ih]

theorem maskDelayMoment_zero {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (U I : Finset (DeletionCandidate n)) : maskDelayMoment r k 0 U I = 0 := by
  simp [maskDelayMoment, maskLifetime]

theorem maskDelayMoment_step {n : ℕ} [NeZero n] (r : ℝ≥0) (k m : ℕ)
    (U I : Finset (DeletionCandidate n)) :
    maskDelayMoment r k (m+1) U I ≤
      (candidateBlock r k U).expect (fun V => maskDelayMoment r k m V I) +
      if U.Nonempty ∧ U ∩ I = ∅ then
        (6/5 : ℝ) *
          (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock r k Finset.univ)).expect
            (fun xs => (maskLifetime (m+1) U xs)^(1/5 : ℝ))
      else 0 := by
  let P := FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r k Finset.univ)
  have he : (candidateBlock r k Finset.univ).expect (fun V =>
      P.expect (fun xs => (maskLifetime m (U ∩ V) xs -
        maskLifetime m ((U ∩ V) ∩ I) xs)^(6/5 : ℝ))) =
      (candidateBlock r k U).expect (fun V => maskDelayMoment r k m V I) := by
    simpa only [maskDelayMoment, P] using
      candidateBlock_mask r k U (fun V => maskDelayMoment r k m V I)
  unfold maskDelayMoment
  rw [FiniteLaw.expect_pi_cons]
  by_cases h : U.Nonempty ∧ U ∩ I = ∅
  · rw [ite_eq_left h]
    rw [FiniteLaw.expect_pi_cons]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons]
    have hpoint (V : Finset (DeletionCandidate n)) (xs : Fin m → Finset (DeletionCandidate n)) :
        (candidateAlive U + maskLifetime m (U ∩ V) xs -
          (candidateAlive (U ∩ I) + maskLifetime m ((U ∩ I) ∩ V) xs))^(6/5 : ℝ) ≤
        (maskLifetime m (U ∩ V) xs - maskLifetime m ((U ∩ V) ∩ I) xs)^(6/5 : ℝ) +
          (6/5 : ℝ) * (candidateAlive U + maskLifetime m (U ∩ V) xs)^(1/5 : ℝ) := by
      simp only [h.2, Finset.empty_inter, maskLifetime_empty,
        show (U ∩ V) ∩ I = ∅ by rw [Finset.inter_right_comm, h.2, Finset.empty_inter],
        candidateAlive, ite_eq_left h.1, Finset.not_nonempty_empty, ite_false, zero_add, sub_zero]
      have hi := sixth_fifth_increment (maskLifetime_nonneg (U ∩ V) xs)
      simpa only [add_comm] using (sub_le_iff_le_add.mp hi)
    have hb := (candidateBlock r k Finset.univ).expect_mono (fun V =>
      P.expect_mono (hpoint V))
    simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul_left] at hb
    rw [he] at hb
    exact hb
  · rw [ite_eq_right h, add_zero]
    have halive : candidateAlive U = candidateAlive (U ∩ I) := by
      by_cases hU : U.Nonempty
      · have hI : (U ∩ I).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun he => h ⟨hU, he⟩)
        simp [candidateAlive, hU, hI]
      · have hI : ¬ (U ∩ I).Nonempty := fun hi => hU (hi.mono Finset.inter_subset_left)
        simp [candidateAlive, hU, hI]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons, halive, add_sub_add_left_eq_sub]
    simpa only [Finset.inter_right_comm, P, maskDelayMoment] using le_of_eq he

theorem finite_expect_comm {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Ξ) (f : Ω → Ξ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem finiteKernel_accumulation {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (g : ℕ → Ω → ℝ) (cost : Ω → ℝ) (M : ℕ)
    (hzero : ∀ x, g 0 x ≤ 0)
    (hstep : ∀ m < M, ∀ x, g (m+1) x ≤ (K x).expect (g m) + cost x) (x : Ω) :
    g M x ≤ ∑ t ∈ Finset.range M, (finiteKernelStep K)^[t] cost x := by
  have hi (m : ℕ) (hm : m ≤ M) :
      ∀ y, g m y ≤ ∑ t ∈ Finset.range m, (finiteKernelStep K)^[t] cost y := by
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
      intro y
      apply (hstep m (by omega) y).trans
      have hb := (K y).expect_mono (ih (by omega))
      apply (add_le_add hb le_rfl).trans_eq
      rw [FiniteLaw.expect_sum, Finset.sum_range_succ']
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply']
      rfl
  exact hi M le_rfl x

theorem maskDelayMoment_occupation {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k M : ℕ) (P : FiniteLaw (Finset (DeletionCandidate n)))
    (bound : Finset (DeletionCandidate n) → ℝ)
    (hbound : ∀ m < M, ∀ U,
      (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock (n := n) r k Finset.univ)).expect
        (fun xs => (maskLifetime (m+1) U xs)^(1/5 : ℝ)) ≤ bound U)
    (U : Finset (DeletionCandidate n)) :
    P.expect (fun I => maskDelayMoment r k M U I) ≤
      ∑ t ∈ Finset.range M, (candidateBlock (r*t) k U).expect (fun V =>
        (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * bound V) := by
  let cost := fun V => (6/5 : ℝ) *
    P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * bound V
  have hs (m : ℕ) (hm : m < M) (V : Finset (DeletionCandidate n)) :
      P.expect (fun I => maskDelayMoment r k (m+1) V I) ≤
        (candidateBlock r k V).expect (fun W => P.expect (fun I => maskDelayMoment r k m W I)) + cost V := by
    have hi := P.expect_mono (fun I => maskDelayMoment_step r k m V I)
    rw [FiniteLaw.expect_add, finite_expect_comm] at hi
    apply hi.trans
    apply add_le_add le_rfl
    have he : P.expect (fun I =>
        if V.Nonempty ∧ V ∩ I = ∅ then (6/5 : ℝ) *
          (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock (n := n) r k Finset.univ)).expect
            (fun xs => (maskLifetime (m+1) V xs)^(1/5 : ℝ)) else 0) =
        (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) *
          (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock (n := n) r k Finset.univ)).expect
            (fun xs => (maskLifetime (m+1) V xs)^(1/5 : ℝ)) := by
      let z := (FiniteLaw.pi (fun _ : Fin (m+1) =>
        candidateBlock (n := n) r k Finset.univ)).expect
          (fun xs => (maskLifetime (m+1) V xs)^(1/5 : ℝ))
      change P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then (6/5 : ℝ)*z else 0) =
        (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * z
      calc
        _ = P.expect (fun I => (if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * ((6/5 : ℝ)*z)) := by
          apply P.expect_congr
          intro I
          split_ifs <;> simp
        _ = _ := by rw [FiniteLaw.expect_mul_right]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (hbound m hm V)
      (mul_nonneg (by norm_num) (P.expect_nonneg (fun I => by split_ifs <;> norm_num)))
  have hz : ∀ V, P.expect (fun I => maskDelayMoment r k 0 V I) ≤ 0 := by
    intro V
    simp only [maskDelayMoment_zero, FiniteLaw.expect_const, le_refl]
  have h := finiteKernel_accumulation (candidateBlock r k)
    (fun m V => P.expect (fun I => maskDelayMoment r k m V I)) cost M hz hs U
  change P.expect (fun I => maskDelayMoment r k M U I) ≤
    ∑ t ∈ Finset.range M, (poissonCandidateStep r k)^[t] cost U at h
  simpa only [poissonCandidateStep_iterate, cost] using h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped BigOperators NNReal Topology

theorem dyadicLifetimeBound_nonneg (j : ℕ) : 0 ≤ dyadicLifetimeBound j := by
  unfold dyadicLifetimeBound
  positivity [dyadicLevel_pos j]

theorem dyadic_lifetime_bound {n : ℕ} [NeZero n] (r : ℝ≥0)
    (hr : (1 : ℝ)/8 ≤ r) (m j : ℕ) (U : Finset (DeletionCandidate n))
    (hU : dyadicBin j U) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r 3 Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ dyadicLifetimeBound j := by
  have h := maskLifetime_fractional_moment r 3 m (dyadicBlock j) U
    (show 0 < dyadicLevel j/4 by positivity [dyadicLevel_pos j])
    (dyadic_block_kills U j r hr hU.2.1)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold dyadicLifetimeBound
  congr 1
  field_simp

theorem capped_lifetime_fractional_bound {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k m M : ℕ) (hm : m ≤ M) (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r k Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ (M : ℝ)^(1/5 : ℝ) := by
  apply (FiniteLaw.expect_mono _ (g := fun _ => (M : ℝ)^(1/5 : ℝ)) (fun xs => Real.rpow_le_rpow
    (maskLifetime_nonneg U xs) ((maskLifetime_le U xs).trans (by exact_mod_cast hm))
    (by norm_num : (0 : ℝ) ≤ 1/5))).trans_eq
  exact FiniteLaw.expect_const _ _

theorem dyadicLevel_rpow (j : ℕ) : dyadicLevel j = (2 : ℝ)^(-(j : ℝ)) := by
  rw [dyadicLevel, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

theorem dyadicBlock_growth (j : ℕ) :
    (dyadicBlock j : ℝ) ≤ 128*((j : ℝ)+122)^2 * (2 : ℝ)^((j : ℝ)/2) := by
  have he : (((j+1)/2 : ℕ) : ℝ) ≤ (j : ℝ)/2+1 := by
    have h : 2*((j+1)/2) ≤ j+2 := by omega
    have h' : (2 : ℝ)*((j+1)/2 : ℕ) ≤ (j : ℝ)+2 := by exact_mod_cast h
    linarith
  have hp : (2 : ℝ)^((j+1)/2) ≤ 2*(2 : ℝ)^((j : ℝ)/2) := by
    rw [← Real.rpow_natCast]
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans_eq
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  unfold dyadicBlock dyadicMultiplicity dyadicTruncation
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 64*((j : ℝ)+122)^2 by positivity)]

theorem dyadicMomentCoefficient_nonneg (j : ℕ) : 0 ≤ dyadicMomentCoefficient j := by
  unfold dyadicMomentCoefficient
  positivity [dyadicLevel_pos j]

theorem dyadicMomentCoefficient_bound (j : ℕ) :
    dyadicMomentCoefficient j ≤
      (512 : ℝ)^(6/5 : ℝ) * ((j : ℝ)+122)^3 * ((2 : ℝ)^(-1/5 : ℝ))^j := by
  have hx : 0 < (j : ℝ)+122 := by positivity
  have hpow : (2 : ℝ)^((j : ℝ)/2) * (2 : ℝ)^(j : ℝ) =
      (2 : ℝ)^(3*(j : ℝ)/2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hA : 4*(dyadicBlock j : ℝ)/dyadicLevel j ≤
      512*((j : ℝ)+122)^2 * (2 : ℝ)^(3*(j : ℝ)/2) := by
    calc
      _ = 4*(dyadicBlock j : ℝ)*(2 : ℝ)^(j : ℝ) := by
        simp only [dyadicLevel, div_eq_mul_inv, inv_inv, Real.rpow_natCast]
      _ ≤ 4*(128*((j : ℝ)+122)^2*(2 : ℝ)^((j : ℝ)/2)) * (2 : ℝ)^(j : ℝ) := by
        gcongr
        exact dyadicBlock_growth j
      _ = _ := by rw [show 4*(128*((j : ℝ)+122)^2*(2 : ℝ)^((j : ℝ)/2)) *
          (2 : ℝ)^(j : ℝ) = 512*((j : ℝ)+122)^2 *
            ((2 : ℝ)^((j : ℝ)/2)*(2 : ℝ)^(j : ℝ)) by ring, hpow]
  have hq : (dyadicLevel j)^2 = (2 : ℝ)^(-2*(j : ℝ)) := by
    rw [dyadicLevel_rpow, pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hxp : (((j : ℝ)+122)^2)^(6/5 : ℝ) = ((j : ℝ)+122)^(12/5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have htwo : ((2 : ℝ)^(3*(j : ℝ)/2))^(6/5 : ℝ) = (2 : ℝ)^(9*(j : ℝ)/5) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have he : (2 : ℝ)^(-2*(j : ℝ)) * (2 : ℝ)^(9*(j : ℝ)/5) =
      ((2 : ℝ)^(-1/5 : ℝ))^j := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  calc
    _ ≤ (dyadicLevel j)^2 *
        (512*((j : ℝ)+122)^2*(2 : ℝ)^(3*(j : ℝ)/2))^(6/5 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity [dyadicLevel_pos j]) hA (by norm_num)) (sq_nonneg _)
    _ = (512 : ℝ)^(6/5 : ℝ) * ((j : ℝ)+122)^(12/5 : ℝ) *
        ((2 : ℝ)^(-1/5 : ℝ))^j := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) (sq_nonneg _), hq, hxp, htwo]
      calc
        _ = (512 : ℝ)^(6/5 : ℝ) * ((j : ℝ)+122)^(12/5 : ℝ) *
          ((2 : ℝ)^(-2*(j : ℝ))*(2 : ℝ)^(9*(j : ℝ)/5)) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := by
      gcongr
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by norm_num)

theorem dyadicMomentCoefficient_summable : Summable dyadicMomentCoefficient := by
  let ρ : ℝ := 2^(-1/5 : ℝ)
  have hρ : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpoly : Summable (fun j : ℕ => ((j : ℝ)+122)^3*ρ^j) := by
    have h0 := (summable_geometric_of_norm_lt_one hρ).mul_left (122^3 : ℝ)
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hρ).mul_left (3*122^2 : ℝ)
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hρ).mul_left (3*122 : ℝ)
    have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 hρ
    apply (h3.add (h2.add (h1.add h0))).congr
    intro j
    ring
  apply Summable.of_nonneg_of_le dyadicMomentCoefficient_nonneg dyadicMomentCoefficient_bound
  simpa only [mul_assoc, ρ] using hpoly.mul_left ((512 : ℝ)^(6/5 : ℝ))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ObstructionMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators Classical NNReal

theorem poissonKillProbability_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (r : ℝ≥0) :
    0 ≤ poissonKillProbability U k r :=
  integral_nonneg (fun d => batchKillProbability_nonneg U k d)

theorem dyadicIndex_spec {n : ℕ} [NeZero n] (U : Finset (DeletionCandidate n))
    (h : U.Nonempty ∧ 0 < poissonKillProbability U 2 60) : dyadicBin (dyadicIndex U) U := by
  simp only [dyadicIndex, dite_eq_left h]
  exact Nat.find_spec (positive_killing_in_dyadic_bin U h.1 h.2)

theorem dyadicCapBound_nonneg {n : ℕ} [NeZero n]
    (M : ℕ) (U : Finset (DeletionCandidate n)) : 0 ≤ dyadicCapBound M U := by
  unfold dyadicCapBound
  split_ifs
  · exact le_min (by positivity) (dyadicLifetimeBound_nonneg _)
  · positivity

theorem dyadicCapBound_le_cap {n : ℕ} [NeZero n]
    (M : ℕ) (U : Finset (DeletionCandidate n)) :
    dyadicCapBound M U ≤ (M : ℝ)^(1/5 : ℝ) := by
  unfold dyadicCapBound
  split_ifs
  · exact min_le_left _ _
  · rfl

theorem dyadicCapBound_controls {n : ℕ} [NeZero n] (r : ℝ≥0)
    (hr : (1 : ℝ)/8 ≤ r) (m M : ℕ) (hm : m ≤ M)
    (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r 3 Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ dyadicCapBound M U := by
  have hc := capped_lifetime_fractional_bound r 3 m M hm U
  unfold dyadicCapBound
  split_ifs with h
  · exact le_min hc (dyadic_lifetime_bound r hr m _ U (dyadicIndex_spec U h))
  · exact hc

theorem dyadicCapBound_weighted {n : ℕ} [NeZero n]
    (M J : ℕ) (U : Finset (DeletionCandidate n))
    (hJ : dyadicIndex U < J) (hU : U.Nonempty) :
    (poissonKillProbability U 2 60)^2 * dyadicCapBound M U ≤
      ∑ j ∈ Finset.range J, if dyadicBin j U then
        4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0 := by
  have hn : ∀ j, 0 ≤ if dyadicBin j U then
      4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0 := by
    intro j
    split_ifs <;> positivity [dyadicLifetimeBound_nonneg j]
  by_cases hp : 0 < poissonKillProbability U 2 60
  · have hb := dyadicIndex_spec U ⟨hU,hp⟩
    have hR : dyadicCapBound M U ≤ dyadicLifetimeBound (dyadicIndex U) := by
      simp only [dyadicCapBound, ite_eq_left (And.intro hU hp)]
      exact min_le_right _ _
    have hq : (poissonKillProbability U 2 60)^2 ≤ 4*(dyadicLevel (dyadicIndex U))^2 := by
      have hqp := dyadicLevel_pos (dyadicIndex U)
      nlinarith [hb.2.2]
    calc
      _ ≤ 4*(dyadicLevel (dyadicIndex U))^2 * dyadicLifetimeBound (dyadicIndex U) :=
        mul_le_mul hq hR (dyadicCapBound_nonneg M U) (by positivity)
      _ = (if dyadicBin (dyadicIndex U) U then
          4*(dyadicLevel (dyadicIndex U))^2*dyadicLifetimeBound (dyadicIndex U) else 0) :=
        (ite_eq_left hb).symm
      _ ≤ _ := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_range.mpr hJ)
  · have hz : poissonKillProbability U 2 60 = 0 :=
      le_antisymm (le_of_not_gt hp) (poissonKillProbability_nonneg U 2 60)
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact Finset.sum_nonneg (fun j _ => hn j)

theorem obstruction_cost_bound {n : ℕ} [NeZero n]
    (P : FiniteLaw (Finset (DeletionCandidate n))) (M J : ℕ) (ε : ℝ)
    (U : Finset (DeletionCandidate n)) (hJ : dyadicIndex U < J)
    (hP : P.expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
      (poissonKillProbability U 2 60 + ε)^2) :
    (6/5 : ℝ) * P.expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) *
      dyadicCapBound M U ≤
      (12/5 : ℝ) * (∑ j ∈ Finset.range J, if dyadicBin j U then
        4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0) +
      (12/5 : ℝ)*ε^2*(M : ℝ)^(1/5 : ℝ) := by
  by_cases hU : U.Nonempty
  · have hq := dyadicCapBound_weighted M J U hJ hU
    have he := mul_le_mul_of_nonneg_left (dyadicCapBound_le_cap M U) (sq_nonneg ε)
    have hs : (poissonKillProbability U 2 60 + ε)^2 ≤
        2*(poissonKillProbability U 2 60)^2 + 2*ε^2 := by
      nlinarith [sq_nonneg (poissonKillProbability U 2 60 - ε)]
    have hb := mul_le_mul_of_nonneg_right (hP.trans hs) (dyadicCapBound_nonneg M U)
    nlinarith
  · simp only [hU, false_and, ite_false, FiniteLaw.expect_const, mul_zero, zero_mul]
    apply add_nonneg
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity [dyadicLifetimeBound_nonneg j])
    · positivity

theorem dyadic_bin_cost_occupation {n : ℕ} [NeZero n]
    (r : ℝ≥0) (hr : (1 : ℝ)/8 ≤ r) (j M : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (∑ t ∈ Finset.range M, (candidateBlock (r*t) 3 U).expect
      (fun V => if dyadicBin j V then
        4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0)) ≤
      4*dyadicMomentCoefficient j := by
  let A : ℝ := 4*(dyadicBlock j : ℝ)/dyadicLevel j
  have hA : 0 < A := by
    dsimp [A, dyadicBlock, dyadicTruncation]
    positivity [dyadicLevel_pos j, dyadic_multiplicity_pos j]
  have he (V : Finset (DeletionCandidate n)) :
      (if dyadicBin j V then 4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0) =
      (4*(dyadicLevel j)^2*dyadicLifetimeBound j) * (if dyadicBin j V then 1 else 0) := by
    split_ifs <;> simp
  simp_rw [he, FiniteLaw.expect_mul_left]
  rw [← Finset.mul_sum]
  have ho := mul_le_mul_of_nonneg_left (dyadic_bin_occupation r hr j M U)
    (show 0 ≤ 4*(dyadicLevel j)^2*dyadicLifetimeBound j by
      positivity [dyadicLifetimeBound_nonneg j])
  apply ho.trans_eq
  have hp : A^(6/5 : ℝ) = A^(1/5 : ℝ)*A := by
    have h := Real.rpow_add hA (1/5 : ℝ) 1
    norm_num at h
    exact h
  change (4*(dyadicLevel j)^2*A^(1/5 : ℝ))*A = 4*((dyadicLevel j)^2*A^(6/5 : ℝ))
  rw [hp]
  ring

theorem maskDelayMoment_of_obstruction {n : ℕ} [NeZero n]
    (r : ℝ≥0) (hr : (1 : ℝ)/8 ≤ r) (M : ℕ)
    (P : FiniteLaw (Finset (DeletionCandidate n))) (ε : ℝ)
    (hP : ∀ U, P.expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
      (poissonKillProbability U 2 60 + ε)^2)
    (U : Finset (DeletionCandidate n)) :
    P.expect (fun I => maskDelayMoment r 3 M U I) ≤
      (48/5 : ℝ) * (∑' j, dyadicMomentCoefficient j) +
      (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
  let J := (Finset.univ.sup (fun V : Finset (DeletionCandidate n) => dyadicIndex V))+1
  have hJ (V : Finset (DeletionCandidate n)) : dyadicIndex V < J := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun V : Finset (DeletionCandidate n) =>
      dyadicIndex V) (Finset.mem_univ V))
  let c : ℕ → Finset (DeletionCandidate n) → ℝ := fun j V =>
    if dyadicBin j V then 4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0
  let B : ℝ := (12/5 : ℝ)*ε^2*(M : ℝ)^(1/5 : ℝ)
  have ho := maskDelayMoment_occupation r 3 M P (dyadicCapBound M)
    (fun m hm V => dyadicCapBound_controls r hr (m+1) M (by omega) V) U
  have hc (V : Finset (DeletionCandidate n)) :
      (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) *
        dyadicCapBound M V ≤ (12/5 : ℝ)*(∑ j ∈ Finset.range J, c j V)+B :=
    obstruction_cost_bound P M J ε V (hJ V) (hP V)
  apply ho.trans
  calc
    _ ≤ ∑ t ∈ Finset.range M, (candidateBlock (r*t) 3 U).expect
        (fun V => (12/5 : ℝ)*(∑ j ∈ Finset.range J, c j V)+B) :=
      Finset.sum_le_sum (fun t _ => FiniteLaw.expect_mono _ hc)
    _ = (12/5 : ℝ)*(∑ j ∈ Finset.range J,
        ∑ t ∈ Finset.range M, (candidateBlock (r*t) 3 U).expect (c j)) + (M : ℝ)*B := by
      simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul_left, FiniteLaw.expect_sum,
        FiniteLaw.expect_const, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (12/5 : ℝ)*(∑ j ∈ Finset.range J, 4*dyadicMomentCoefficient j) + (M : ℝ)*B := by
      gcongr with j hj
      exact dyadic_bin_cost_occupation r hr j M U
    _ ≤ (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) + (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
      have hs := dyadicMomentCoefficient_summable.sum_le_tsum (Finset.range J)
        (fun j _ => dyadicMomentCoefficient_nonneg j)
      rw [← Finset.mul_sum]
      have hp : (M : ℝ)*(M : ℝ)^(1/5 : ℝ) = (M : ℝ)^(6/5 : ℝ) := by
        by_cases hM : M = 0
        · subst M
          norm_num
        · have h := (Real.rpow_add (by positivity : (0 : ℝ) < M) 1 (1/5 : ℝ)).symm
          norm_num at h
          exact h
      dsimp only [B]
      nlinarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem finiteMap_expect {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (P : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (finiteMap P f).expect g = P.expect (fun x => g (f x)) := by
  simp only [FiniteLaw.expect, finiteMap, Finset.sum_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem unionMaskLaw_killing {n : ℕ}
    (P Q : FiniteLaw (Finset (DeletionCandidate n))) (U : Finset (DeletionCandidate n)) :
    (unionMaskLaw P Q).expect (fun I => if U ∩ I = ∅ then 1 else 0) =
      P.expect (fun I => if U ∩ I = ∅ then 1 else 0) *
      Q.expect (fun I => if U ∩ I = ∅ then 1 else 0) := by
  rw [unionMaskLaw, finiteMap_expect, FiniteLaw.expect_bind]
  have he (I J : Finset (DeletionCandidate n)) :
      (if U ∩ (I ∪ J) = ∅ then (1 : ℝ) else 0) =
      (if U ∩ I = ∅ then 1 else 0) * (if U ∩ J = ∅ then 1 else 0) := by
    simp only [Finset.inter_union_distrib_left, Finset.union_eq_empty]
    split_ifs <;> simp_all
  simp only [he, FiniteLaw.expect_mul_left, FiniteLaw.expect_mul_right]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskDeletionTimes
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem maskLifetime_union {n m : ℕ} (U V : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (U ∪ V) xs = max (maskLifetime m U xs) (maskLifetime m V xs) := by
  induction m generalizing U V with
  | zero => simp [maskLifetime]
  | succ m ih =>
    by_cases hU : U.Nonempty
    · by_cases hV : V.Nonempty
      · have hUV : (U ∪ V).Nonempty := hU.mono Finset.subset_union_left
        simp only [maskLifetime, candidateAlive, ite_eq_left hU, ite_eq_left hV,
          ite_eq_left hUV, Finset.union_inter_distrib_right, ih, max_add_add_left]
      · have hVe : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
        subst V
        simp only [Finset.union_empty, maskLifetime_empty, max_eq_left (maskLifetime_nonneg U xs)]
    · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      simp only [Finset.empty_union, maskLifetime_empty, max_eq_right (maskLifetime_nonneg V xs)]

theorem maskLifetime_frontload {n m : ℕ} (U : Finset (DeletionCandidate n))
    (base incident : Fin m → Finset (DeletionCandidate n)) (I : Finset (DeletionCandidate n))
    (hI : ∀ j, I ⊆ incident j) :
    maskLifetime m (U ∩ I) base ≤ maskLifetime m U (fun j => base j ∩ incident j) := by
  induction m generalizing U with
  | zero => exact le_rfl
  | succ m ih =>
    simp only [maskLifetime]
    apply add_le_add (candidateAlive_mono Finset.inter_subset_left)
    have hsub : (U ∩ I) ∩ base 0 ⊆ (U ∩ (base 0 ∩ incident 0)) ∩ I := by
      intro x hx
      obtain ⟨hxUI,hxb⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxU,hxI⟩ := Finset.mem_inter.mp hxUI
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨hxU,Finset.mem_inter.mpr ⟨hxb,hI 0 hxI⟩⟩,hxI⟩
    exact (maskLifetime_mono hsub (Fin.tail base)).trans
      (ih (U ∩ (base 0 ∩ incident 0)) (Fin.tail base) (Fin.tail incident) (fun j => hI j.succ))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RestoredCandidates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

theorem deletedVariables_tail_image {n : ℕ} (x : DeletionCandidate (n+1)) :
    (deletedVariables (Fin.tail x)).image Fin.succ = (deletedVariables x).erase 0 := by
  ext i
  rw [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨Fin.succ_ne_zero _,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  · rintro ⟨hi0,hi⟩
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩

theorem deletedVariables_restore_card {n : ℕ} (b : Bool) (x : DeletionCandidate n) :
    (deletedVariables (restoreCandidate (some b) x)).card = (deletedVariables x).card := by
  have h0 : (0 : Fin (n+1)) ∉ deletedVariables (restoreCandidate (some b) x) := by
    intro h
    have hx := (Finset.mem_filter.mp h).2
    simp [restoreCandidate] at hx
  have he := deletedVariables_tail_image (restoreCandidate (some b) x)
  rw [Finset.erase_eq_of_notMem h0] at he
  rw [← he, Finset.card_image_of_injective _ (Fin.succ_injective n)]
  rfl

theorem mem_freeDeletionBudgetMask {n r : ℕ} (x : DeletionCandidate (n+1)) :
    x ∈ freeDeletionBudgetMask (n+1) r 0 ↔
      (deletedVariables (Fin.tail x)).card ≤ r := by
  simp only [freeDeletionBudgetMask, Finset.mem_biUnion, allowedDeletions, deletionMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hc : ((deletedVariables (Fin.tail x)).image Fin.succ).card =
      (deletedVariables (Fin.tail x)).card := Finset.card_image_of_injective _ (Fin.succ_injective n)
  constructor
  · rintro ⟨D,hD,hx⟩
    have hsub : (deletedVariables (Fin.tail x)).image Fin.succ ⊆ D := by
      rw [deletedVariables_tail_image]
      intro i hi
      obtain ⟨hi0,hi⟩ := Finset.mem_erase.mp hi
      exact (Finset.mem_insert.mp (hx hi)).resolve_left hi0
    rw [← hc]
    exact (Finset.card_le_card hsub).trans hD
  · intro hx
    refine ⟨(deletedVariables (Fin.tail x)).image Fin.succ, by simpa only [hc] using hx, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · exact Finset.mem_insert.mpr (Or.inl hi0)
    · exact Finset.mem_insert.mpr (Or.inr (by
        rw [deletedVariables_tail_image]
        exact Finset.mem_erase.mpr ⟨hi0,hi⟩))

theorem maskLifetime_map_le {n N m : ℕ} (f : DeletionCandidate n → DeletionCandidate N)
    (U : Finset (DeletionCandidate n)) (V : Finset (DeletionCandidate N))
    (xs : Fin m → Finset (DeletionCandidate n)) (ys : Fin m → Finset (DeletionCandidate N))
    (hUV : ∀ x ∈ U, f x ∈ V)
    (hxy : ∀ j x, x ∈ xs j → f x ∈ ys j) :
    maskLifetime m U xs ≤ maskLifetime m V ys := by
  induction m generalizing U V with
  | zero => exact le_rfl
  | succ m ih =>
    apply add_le_add
    · unfold candidateAlive
      split_ifs with hU hV hV
      · exact le_rfl
      · obtain ⟨x,hx⟩ := hU
        exact False.elim (hV ⟨f x,hUV x hx⟩)
      · norm_num
      · exact le_rfl
    · exact ih (U ∩ xs 0) (V ∩ ys 0) (Fin.tail xs) (Fin.tail ys)
        (fun x hx => Finset.mem_inter.mpr
          ⟨hUV x (Finset.mem_inter.mp hx).1,hxy 0 x (Finset.mem_inter.mp hx).2⟩)
        (fun j x hx => hxy j.succ x hx)

theorem restoredMask_tail {n : ℕ} (B F T : Finset (DeletionCandidate n))
    {x : DeletionCandidate (n+1)} (hx : x ∈ restoredMask B F T) : Fin.tail x ∈ B :=
  (Finset.mem_filter.mp hx).2.1

theorem restore_none_mem {n : ℕ} (B F T : Finset (DeletionCandidate n))
    {x : DeletionCandidate n} (hx : x ∈ B) :
    restoreCandidate none x ∈ restoredMask B F T := by
  simpa [restoredMask, restoreCandidate] using hx

theorem restore_some_mem {n : ℕ} (B F T : Finset (DeletionCandidate n))
    (b : Bool) {x : DeletionCandidate n} (hx : x ∈ B)
    (hi : x ∈ if b then T else F) :
    restoreCandidate (some b) x ∈ restoredMask B F T := by
  cases b <;> simpa [restoredMask, restoreCandidate, hx] using hi

theorem free_restored_lifetime {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (freeDeletionBudgetMask (n+1) r 0)
      (fun j => restoredMask (base j) (f j) (t j)) =
      maskLifetime m (deletionBudgetMask n r) base := by
  apply le_antisymm
  · apply maskLifetime_map_le (fun x => Fin.tail x)
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_freeDeletionBudgetMask] using hx
    · intro j x hx
      exact restoredMask_tail _ _ _ hx
  · apply maskLifetime_map_le (restoreCandidate none)
    · intro x hx
      rw [mem_freeDeletionBudgetMask]
      simpa only [restoreCandidate, Fin.tail_cons, deletionBudgetMask,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · intro j x hx
      exact restore_none_mem _ _ _ hx

theorem restored_frontload_lifetime {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n))
    (F T : Finset (DeletionCandidate n))
    (hF : ∀ j, F ⊆ f j) (hT : ∀ j, T ⊆ t j) :
    maskLifetime m (deletionBudgetMask n r ∩ (F ∪ T)) base ≤
      maskLifetime m (deletionBudgetMask (n+1) r)
        (fun j => restoredMask (base j) (f j) (t j)) := by
  rw [Finset.inter_union_distrib_left, maskLifetime_union]
  apply max_le
  · apply le_trans (maskLifetime_frontload _ base f F hF)
    apply maskLifetime_map_le (restoreCandidate (some false))
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        deletedVariables_restore_card] using hx
    · intro j x hx
      exact restore_some_mem _ _ _ false (Finset.mem_inter.mp hx).1
        (Finset.mem_inter.mp hx).2
  · apply le_trans (maskLifetime_frontload _ base t T hT)
    apply maskLifetime_map_le (restoreCandidate (some true))
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        deletedVariables_restore_card] using hx
    · intro j x hx
      exact restore_some_mem _ _ _ true (Finset.mem_inter.mp hx).1
        (Finset.mem_inter.mp hx).2

theorem deletionBudgetMask_subset_free (n r : ℕ) (v : Fin n) :
    deletionBudgetMask n r ⊆ freeDeletionBudgetMask n r v := by
  intro x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨deletedVariables x, ?_, ?_⟩
  · simpa only [allowedDeletions, deletionBudgetMask, Finset.mem_filter,
      Finset.mem_univ, true_and] using hx
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert _ _⟩

theorem restored_gap_nonneg {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n)) :
    0 ≤ maskLifetime m (deletionBudgetMask n r) base -
      maskLifetime m (deletionBudgetMask (n+1) r)
        (fun j => restoredMask (base j) (f j) (t j)) := by
  rw [← free_restored_lifetime base f t]
  exact sub_nonneg.mpr (maskLifetime_mono (deletionBudgetMask_subset_free (n+1) r 0) _)

theorem restored_gap_bound {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n))
    (F T : Finset (DeletionCandidate n))
    (hF : ∀ j, F ⊆ f j) (hT : ∀ j, T ⊆ t j) :
    (maskLifetime m (deletionBudgetMask n r) base -
      maskLifetime m (deletionBudgetMask (n+1) r)
        (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ) ≤
      (maskLifetime m (deletionBudgetMask n r) base -
        maskLifetime m (deletionBudgetMask n r ∩ (F ∪ T)) base)^(6/5 : ℝ) := by
  apply Real.rpow_le_rpow (restored_gap_nonneg base f t)
    (sub_le_sub_left (restored_frontload_lifetime base f t F T hF hT) _) (by norm_num)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RestoredProcessMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical NNReal

theorem mem_maskRun {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) (x : DeletionCandidate n) :
    x ∈ maskRun m U xs ↔ x ∈ U ∧ ∀ j, x ∈ xs j := by
  induction m generalizing U with
  | zero => simp [maskRun]
  | succ m ih =>
    simp only [maskRun, ih, Finset.mem_inter, Fin.forall_fin_succ, Fin.tail_def, and_assoc]

theorem frontloadMask_subset {n m : ℕ} (xs : Fin m → Finset (DeletionCandidate n))
    (j : Fin m) : frontloadMask xs ⊆ xs j := by
  intro x hx
  exact (mem_maskRun _ xs x).mp hx |>.2 j

theorem restored_process_moment_sat_oai {n : ℕ} [NeZero n] (M r : ℕ)
    (rate : ℝ≥0) (hrate : (1 : ℝ)/8 ≤ rate)
    (P : FiniteLaw (Fin M → Finset (DeletionCandidate n))) (ε : ℝ)
    (hP : ∀ U, (finiteMap P frontloadMask).expect
      (fun I => if U ∩ I = ∅ then 1 else 0) ≤ poissonKillProbability U 2 60 + ε) :
    P.expect (fun f => P.expect (fun t =>
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock rate 3 Finset.univ)).expect (fun base =>
        (maskLifetime M (deletionBudgetMask n r) base -
          maskLifetime M (deletionBudgetMask (n+1) r)
            (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)))) ≤
      (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) +
        (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
  let Q := finiteMap P frontloadMask
  have hQ (U : Finset (DeletionCandidate n)) :
      (unionMaskLaw Q Q).expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
        (poissonKillProbability U 2 60 + ε)^2 := by
    by_cases hU : U.Nonempty
    · simp only [hU, true_and, unionMaskLaw_killing]
      rw [← pow_two]
      exact pow_le_pow_left₀ (FiniteLaw.expect_nonneg _ (fun I => by split_ifs <;> norm_num))
        (hP U) 2
    · simp only [hU, false_and, ite_false, FiniteLaw.expect_const]
      exact sq_nonneg _
  have h := maskDelayMoment_of_obstruction rate hrate M (unionMaskLaw Q Q) ε hQ
    (deletionBudgetMask n r)
  apply le_trans ?_ h
  rw [unionMaskLaw, finiteMap_expect, FiniteLaw.expect_bind]
  simp only [Q, finiteMap_expect]
  apply P.expect_mono
  intro f
  apply P.expect_mono
  intro t
  exact FiniteLaw.expect_mono _ (fun base =>
    restored_gap_bound base f t (frontloadMask f) (frontloadMask t)
      (frontloadMask_subset f) (frontloadMask_subset t))

end FixedClauseThreshold.Computability

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.restored_process_moment_sat_oai := @OAI.FixedClauseThreshold.Computability.restored_process_moment_sat_oai
