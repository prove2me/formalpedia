-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2Y_le_of_bracket_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:08:03.774246+00:00
-- url     : https://prove2.me/submissions/6c2e51f1-a3a6-44b6-9f00-7c01b5eecbb5

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAICatalanIrrationality

section
-- module Solutions.OAICatalan.Catalan.Polynomial.CentralCoefficients
namespace OAI

namespace InternalCatalan

section

open scoped BigOperators



@[simp] theorem centralCoeff_zero : centralCoeff 0 = 1 := by
  norm_num [centralCoeff]

@[simp] theorem centralCoeffKernel_zero : centralCoeffKernel 0 = 1 := by
  norm_num [centralCoeffKernel]





@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]





@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl








@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]






@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]



@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]




end













end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealColumnDeterminant
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial




@[simp] theorem reversedRow_zero (C : ℕ) : reversedRow C 0 = 0 := by
  simp [reversedRow]



































end

section

open scoped BigOperators









end

section

open Polynomial







variable {K : Type*} [Field K]




end

open Polynomial



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierChebyshevUSeries
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem barrierChebyshevU_abs_le (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤ (k : ℝ) + 1 := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have h := Chebyshev.abs_iterate_derivative_T_real_le ((k : ℤ) + 1) 1 hx
  simp only [Function.iterate_one] at h
  rw [Chebyshev.derivative_T_eval_one, Chebyshev.T_derivative_eq_U] at h
  have hm : ((k : ℝ) + 1) * |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
    simpa only [add_sub_cancel_right, eval_mul, eval_intCast, eval_add, eval_natCast, eval_one,
      Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul, abs_of_pos hk,
      pow_two] using h
  exact le_of_mul_le_mul_left hm hk

theorem barrierChebyshevU_summable {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k) := by
  have hnorm : ‖(‖z‖ : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hz
  have hmajor : Summable (fun k : ℕ => ((k : ℝ) + 1) * ‖z‖ ^ k) := by
    simpa only [add_mul, one_mul] using
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.add
        (summable_geometric_of_norm_lt_one hnorm)
  refine hmajor.of_norm_bounded ?_
  intro k
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (barrierChebyshevU_abs_le k hx)
      (pow_nonneg (norm_nonneg z) k)

private theorem barrierChebyshevU_recurrence_complex (k : ℕ) (x : ℝ) :
    (((Chebyshev.U ℝ ((k + 2 : ℕ) : ℤ)).eval x : ℝ) : ℂ) =
      2 * (x : ℂ) * (((Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval x : ℝ) : ℂ) -
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) := by
  have h := congrArg (fun p : ℝ[X] => ((p.eval x : ℝ) : ℂ))
    (Chebyshev.U_add_two ℝ (k : ℤ))
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, eval_sub, eval_mul, eval_ofNat, eval_X,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

theorem barrierChebyshevU_hasSum {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k)
      (1 / (1 - 2 * (x : ℂ) * z + z ^ 2)) := by
  let f : ℕ → ℂ := fun k => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k
  let S : ℂ := ∑' k, f k
  have hs : HasSum f S := (barrierChebyshevU_summable hx hz).hasSum
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = 2 * (x : ℂ) * z := by simp [f, Chebyshev.U_one]
  have h1 : HasSum (fun k : ℕ => f (k + 1)) (S - 1) := by
    simpa only [Finset.sum_range_one, hf0] using (hasSum_nat_add_iff' 1).2 hs
  have h2 : HasSum (fun k : ℕ => f (k + 2)) (S - (1 + 2 * (x : ℂ) * z)) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hf0, hf1] using
      (hasSum_nat_add_iff' 2).2 hs
  have hrec : ∀ k : ℕ, f (k + 2) =
      (2 * (x : ℂ) * z) * f (k + 1) - z ^ 2 * f k := by
    intro k
    dsimp only [f]
    rw [barrierChebyshevU_recurrence_complex k x]
    simp only [pow_add, pow_one]
    ring
  have hrecSum : HasSum (fun k : ℕ => f (k + 2))
      ((2 * (x : ℂ) * z) * (S - 1) - z ^ 2 * S) :=
    ((h1.mul_left (2 * (x : ℂ) * z)).sub (hs.mul_left (z ^ 2))).congr_fun hrec
  have heq := h2.unique hrecSum
  have hmul : (1 - 2 * (x : ℂ) * z + z ^ 2) * S = 1 := by
    linear_combination heq
  have hden : 1 - 2 * (x : ℂ) * z + z ^ 2 ≠ 0 := by
    intro hzero
    simp only [hzero, zero_mul, zero_ne_one] at hmul
  have hS : S = 1 / (1 - 2 * (x : ℂ) * z + z ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using hmul
  rw [hS] at hs
  exact hs

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierDescartesCoefficientDegree
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierDescartesTransform {R : Type*} [CommRing R] (p : R[X])
    (d : ℕ) (a b : R) : R[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (p.coeff k) * (C a + C b * X) ^ k * (1 + X) ^ (d - k)

theorem barrierDescartesTransform_eval {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t =
      (1 + t) ^ d * p.eval ((a + b * t) / (1 + t)) := by
  unfold barrierDescartesTransform
  rw [eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : (1 + t) ^ (d - k) = (1 + t) ^ d / (1 + t) ^ k := by
    apply (eq_div_iff (pow_ne_zero k ht)).2
    rw [← pow_add, Nat.sub_add_cancel hkd]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rw [hp, div_pow]
  ring

theorem barrierDescartesTransform_eval_eq_zero_iff {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t = 0 ↔
      p.eval ((a + b * t) / (1 + t)) = 0 := by
  rw [barrierDescartesTransform_eval p d a b t hd ht]
  simp [pow_ne_zero d ht]

theorem barrierMobius_inverse {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    0 < (x - a) / (b - x) ∧
      (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) = x := by
  have hp : 0 < (x - a) / (b - x) :=
    div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hb : b - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have h1 : 1 + (x - a) / (b - x) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨hp, ?_⟩
  apply (div_eq_iff h1).2
  field_simp [hb]
  ring

theorem barrierDescartesTransform_root_of_interval (p : ℝ[X]) (d : ℕ)
    {a b x : ℝ} (hd : p.natDegree ≤ d) (hx : x ∈ Set.Ioo a b)
    (hp : p.eval x = 0) :
    0 < (x - a) / (b - x) ∧
      (barrierDescartesTransform p d a b).eval ((x - a) / (b - x)) = 0 := by
  obtain ⟨ht, heq⟩ := barrierMobius_inverse hx
  refine ⟨ht, ?_⟩
  apply (barrierDescartesTransform_eval_eq_zero_iff p d a b _ hd
    (ne_of_gt (by linarith))).2
  rw [heq]
  exact hp

theorem barrier_coeff_affine_pow {R : Type*} [CommRing R]
    (a b : R) (j k : ℕ) :
    ((C a + C b * X) ^ j).coeff k =
      (j.choose k : R) * a ^ (j - k) * b ^ k := by
  calc
    ((C a + C b * X) ^ j).coeff k =
        (((X + C a) ^ j).comp (C b * X)).coeff k := by
      rw [pow_comp, add_comp, X_comp, C_comp,
        add_comm (C b * X) (C a)]
    _ = ((X + C a) ^ j).coeff k * b ^ k := comp_C_mul_X_coeff
    _ = _ := by
      rw [coeff_X_add_C_pow]
      ac_rfl

theorem barrierDescartesTransform_coeff {R : Type*} [CommRing R]
    (p : R[X]) (d : ℕ) (a b : R) (h : ℕ) :
    (barrierDescartesTransform p d a b).coeff h =
      ∑ j ∈ Finset.range (d + 1), p.coeff j *
        ∑ k ∈ Finset.range (h + 1),
          (j.choose k : R) * a ^ (j - k) * b ^ k *
            ((d - j).choose (h - k) : R) := by
  unfold barrierDescartesTransform
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, coeff_C_mul, coeff_mul]
  have hanti :
      (∑ x ∈ Finset.HasAntidiagonal.antidiagonal h,
        Polynomial.coeff ((C a + C b * X : R[X]) ^ j) x.1 *
          Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) x.2) =
      ∑ k ∈ Finset.range (h + 1),
        Polynomial.coeff ((C a + C b * X : R[X]) ^ j) k *
          Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) (h - k) :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun (k l : ℕ) => Polynomial.coeff ((C a + C b * X : R[X]) ^ j) k *
        Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) l) h
  rw [hanti]
  simp only [barrier_coeff_affine_pow, coeff_one_add_X_pow]

def barrierDescartesCoeffRat (c : ℕ → ℚ) (d : ℕ) (a b : ℚ) (h : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (d + 1), c j *
    ∑ k ∈ Finset.range (h + 1),
      (j.choose k : ℚ) * a ^ (j - k) * b ^ k *
        ((d - j).choose (h - k) : ℚ)

theorem barrierDescartesTransform_coeff_rat (p : ℚ[X]) (c : ℕ → ℚ)
    (d : ℕ) (a b : ℚ) (h : ℕ)
    (hc : ∀ j, j < d + 1 → p.coeff j = c j) :
    (barrierDescartesTransform (p.map (Rat.castHom ℝ)) d (a : ℝ) (b : ℝ)).coeff h =
      (barrierDescartesCoeffRat c d a b h : ℝ) := by
  change (barrierDescartesTransform (p.map (Rat.castHom ℝ)) d
      ((Rat.castHom ℝ) a) ((Rat.castHom ℝ) b)).coeff h =
    (Rat.castHom ℝ) (barrierDescartesCoeffRat c d a b h)
  rw [barrierDescartesTransform_coeff]
  simp only [barrierDescartesCoeffRat, map_sum, map_mul, map_pow, map_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.coeff_map, hc j (Finset.mem_range.mp hj)]

end

section

open Polynomial

theorem barrierDescartes_interval_roots_card_le (p : ℝ[X]) (d : ℕ) (a b : ℝ)
    (hd : p.natDegree ≤ d)
    (hne : barrierDescartesTransform p d a b ≠ 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Set.Ioo a b ∧ p.eval x = 0) :
    s.card ≤ (barrierDescartesTransform p d a b).signVariations := by
  classical
  let Q := barrierDescartesTransform p d a b
  let t := (Q.roots.filter (fun x => 0 < x)).toFinset
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℝ => (x - a) / (b - x))
    · intro x hx
      obtain ⟨hpos, hroot⟩ := barrierDescartesTransform_root_of_interval p d hd
        (hs x hx).1 (hs x hx).2
      apply Multiset.mem_toFinset.mpr
      exact Multiset.mem_filter.mpr
        ⟨(Polynomial.mem_roots hne).mpr hroot, hpos⟩
    · intro x hx y hy hxy
      change (x - a) / (b - x) = (y - a) / (b - y) at hxy
      have hix := (barrierMobius_inverse (hs x hx).1).2
      have hiy := (barrierMobius_inverse (hs y hy).1).2
      calc
        x = (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) := hix.symm
        _ = (a + b * ((y - a) / (b - y))) / (1 + (y - a) / (b - y)) := by rw [hxy]
        _ = y := hiy
  have htcard : t.card ≤ Q.roots.countP (fun x => 0 < x) := by
    simpa only [t, Multiset.countP_eq_card_filter] using
      Multiset.toFinset_card_le (Q.roots.filter (fun x => 0 < x))
  exact hcard.trans (htcard.trans (Polynomial.roots_countP_pos_le_signVariations Q))

end

section

open Filter Polynomial
open scoped Topology





end

open Polynomial
open scoped BigOperators

theorem barrierDescartesTransform_coeff_zero_above {R : Type*} [CommRing R]
    (p : R[X]) (d : ℕ) (a b : R) {h : ℕ} (hh : d < h) :
    (barrierDescartesTransform p d a b).coeff h = 0 := by
  rw [barrierDescartesTransform_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  suffices hsum :
      (∑ k ∈ Finset.range (h + 1),
        (j.choose k : R) * a ^ (j - k) * b ^ k *
          ((d - j).choose (h - k) : R)) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : k ≤ j
  · have hchoose : d - j < h - k := by omega
    rw [Nat.choose_eq_zero_of_lt hchoose, Nat.cast_zero, mul_zero]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkj), Nat.cast_zero]
    simp only [zero_mul]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTailPairRational
namespace OAI

noncomputable section

namespace InternalCatalan













theorem barrier_finite_lengths :
    barrierP2Finite.length = 10 ∧ barrierV2Finite.length = 10 ∧
    barrierP1Finite.length = 8 ∧ barrierV1Finite.length = 8 := by decide

theorem barrier_tail_lengths : barrierP2Tail.length = 10 ∧ barrierV2Tail.length = 13 := by
  norm_num [barrierP2Tail, barrierV2Tail, barrierConjugatePair]


theorem barrierP2_finite_abs_lt_one :
    ∀ a ∈ barrierP2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP2Finite]

theorem barrierV2_finite_abs_lt_one :
    ∀ a ∈ barrierV2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV2Finite]

theorem barrierP1_finite_abs_lt_one :
    ∀ a ∈ barrierP1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP1Finite]

theorem barrierV1_finite_abs_lt_one :
    ∀ a ∈ barrierV1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV1Finite]

theorem barrierP2_tail_norm_bounds :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (94 / 100 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierP2Tail,
      Complex.normSq zr.1 ≤ (94 / 100 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierV2_tail_norm_bounds :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (984 / 1000 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierV2Tail,
      Complex.normSq zr.1 ≤ (984 / 1000 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierFiniteCoeff_abs_le (cs : List ℤ) (hlen : cs.length ≤ 10)
    (hcoeff : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1) (k : ℕ) :
    |barrierFiniteCoeff cs k| ≤ 2 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    norm_num [barrierFiniteCoeff]
  rw [barrierFiniteCoeff, if_neg hk]
  by_cases hi : k - 1 < cs.length
  · have hmem : cs.getD (k - 1) 0 ∈ cs := by
      rw [List.getD_eq_getElem cs 0 hi]
      exact List.getElem_mem hi
    have hk10 : k ≤ 10 := by omega
    have hpow : (99 / 100 : ℝ) ^ 10 ≤ (99 / 100 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk10
    calc
      |(cs.getD (k - 1) 0 : ℝ) / 100000000| ≤ 1 :=
        le_of_lt (hcoeff _ hmem)
      _ ≤ 2 * (99 / 100 : ℝ) ^ 10 := by norm_num
      _ ≤ 2 * (99 / 100 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  · rw [List.getD_eq_default cs 0 (Nat.le_of_not_gt hi)]
    simp only [Int.cast_zero, zero_div, abs_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)

def barrierTailLinearDen (z : ℂ) (x : ℝ) : ℂ := 1 - (x : ℂ) * z

def barrierTailQuadraticDen (z : ℂ) (x : ℝ) : ℂ :=
  1 - 2 * (x : ℂ) * z + z ^ 2


theorem barrierTailQuadraticDen_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) : barrierTailQuadraticDen z x ≠ 0 := by
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
  have hn : Complex.normSq z < 1 :=
    lt_of_not_ge (fun h => (not_le_of_gt hz) (Complex.one_le_normSq_iff.mp h))
  have hnorm : z.re ^ 2 + z.im ^ 2 < 1 := by
    simpa only [Complex.normSq_apply, pow_two] using hn
  intro hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  norm_num [barrierTailQuadraticDen, pow_two] at hre him
  have hprod : z.im * (z.re - x) = 0 := by nlinarith [him]
  have hax : z.re = x := by
    rcases mul_eq_zero.mp hprod with hb | ha
    · have hre0 := hre
      rw [hb] at hre0
      have hs : (z.re - x) ^ 2 = 0 := by
        nlinarith [sq_nonneg (z.re - x)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · exact sub_eq_zero.mp ha
  rw [hax] at hre hnorm
  nlinarith


theorem barrierTailQuadraticDen_prod_ne_zero (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    (tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨zr, hzr, hz⟩ := List.mem_map.mp hzero
  exact barrierTailQuadraticDen_ne_zero hx (htail zr hzr) hz


def barrierCase2QYValue (x : ℝ) : ℂ :=
  (x : ℂ) * (1 - (x : ℂ)) *
    (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod


private theorem barrierV2_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)


theorem barrierCase2QYValue_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : barrierCase2QYValue x ≠ 0 := by
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1' : 1 - (x : ℂ) ≠ 0 := by
    have h : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
    exact_mod_cast h
  exact mul_ne_zero (mul_ne_zero hx0' hx1')
    (barrierTailQuadraticDen_prod_ne_zero barrierV2Tail barrierV2_tail_base_lt_one hx)






















open Polynomial

private theorem barrier_conjugate_quotient_re (n d : ℂ) :
    (n / d + star n / star d).re =
      2 * (n.re * d.re + n.im * d.im) / (d.re ^ 2 + d.im ^ 2) := by
  have hc : star n / star d = star (n / d) := by
    simp only [Complex.star_def, map_div₀]
  rw [hc]
  simp only [Complex.star_def, Complex.add_re, Complex.conj_re, Complex.div_re,
    Complex.normSq_apply, pow_two]
  ring


private theorem barrierTailQuadraticDen_star (z : ℂ) (x : ℝ) :
    barrierTailQuadraticDen (star z) x = star (barrierTailQuadraticDen z x) := by
  simp [barrierTailQuadraticDen]


theorem barrierConjugatePair_quadratic_re (z r : ℂ) (x : ℝ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      2 * ((r * z).re * (1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2) +
        (r * z).im * (2 * z.im * (z.re - x))) /
        ((1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2) ^ 2 +
          (2 * z.im * (z.re - x)) ^ 2) := by
  simp only [barrierConjugatePair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hn : star r * star z = star (r * z) := by simp
  rw [barrierTailQuadraticDen_star, hn, barrier_conjugate_quotient_re]
  have hre : (barrierTailQuadraticDen z x).re =
      1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2 := by
    simp [barrierTailQuadraticDen, pow_two]
    ring
  have him : (barrierTailQuadraticDen z x).im = 2 * z.im * (z.re - x) := by
    simp [barrierTailQuadraticDen, pow_two]
    ring
  rw [hre, him]

def barrierPairLinearQ (a b : ℚ) : ℚ[X] :=
  (1 - C a * X) ^ 2 + (C b * X) ^ 2

def barrierPairLinearA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - C a * X) - C (c * b + d * a) * C b * X)

def barrierPairQuadraticQ (a b : ℚ) : ℚ[X] :=
  (1 - 2 * C a * X + C (a ^ 2 - b ^ 2)) ^ 2 +
    (2 * C b * (C a - X)) ^ 2

def barrierPairQuadraticA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - 2 * C a * X + C (a ^ 2 - b ^ 2)) +
    C (c * b + d * a) * (2 * C b * (C a - X)))


theorem barrierConjugatePair_quadratic_eq_ratPolynomial
    (a b c d : ℚ) (x : ℝ) :
    ((barrierConjugatePair (barrierComplex a b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      (barrierPairQuadraticA a b c d).eval₂ (Rat.castHom ℝ) x /
        (barrierPairQuadraticQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierConjugatePair_quadratic_re]
  simp only [barrierPairQuadraticA, barrierPairQuadraticQ, eval₂_mul, eval₂_add,
    eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one, eval₂_ofNat,
    map_mul, map_sub, map_add, map_pow, Rat.coe_castHom, barrierComplex, Complex.mul_re, Complex.mul_im]
  congr 1 <;> ring





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFinitePotentialRat
namespace OAI

noncomputable section

namespace InternalCatalan

section

private theorem barrierTail_norm_le (tail : List (ℂ × ℂ)) (k : ℕ) :
    (∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) →
      ‖(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum‖ ≤
        (tail.length : ℝ) * (99 / 100 : ℝ) ^ k := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    intro hb
    have hz := hb zr (List.mem_cons_self)
    have ht := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hone : ‖zr.2 * zr.1 ^ k‖ ≤ (99 / 100 : ℝ) ^ k := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * (99 / 100 : ℝ) ^ k := by
          gcongr
          · exact hz.2
          · exact hz.1
        _ = _ := one_mul _
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖zr.2 * zr.1 ^ k‖ + ‖(tail.map (fun w : ℂ × ℂ => w.2 * w.1 ^ k)).sum‖ :=
        norm_add_le _ _
      _ ≤ (99 / 100 : ℝ) ^ k + (tail.length : ℝ) * (99 / 100 : ℝ) ^ k :=
        add_le_add hone ht
      _ = _ := by ring

private theorem barrierTrial_abs_le (cs : List ℤ) (tail : List (ℂ × ℂ))
    (hc : cs.length ≤ 10)
    (ha : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1)
    (ht : tail.length ≤ 13)
    (hb : ∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) (k : ℕ) :
    |barrierTrial cs tail k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · simp [barrierTrial, hk]
  have htail : |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      13 * (99 / 100 : ℝ) ^ k := by
    exact (Complex.abs_re_le_norm _).trans ((barrierTail_norm_le tail k hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (by positivity)))
  simp only [barrierTrial, if_neg hk]
  calc
    _ ≤ |barrierFiniteCoeff cs k| +
        |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (barrierFiniteCoeff cs k)
        ((tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re)
    _ ≤ 2 * (99 / 100 : ℝ) ^ k + 13 * (99 / 100 : ℝ) ^ k :=
      add_le_add (barrierFiniteCoeff_abs_le cs hc ha k) htail
    _ = _ := by ring

theorem barrier_trials_abs_le (k : ℕ) :
    |barrierP2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierP1 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV1 k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  have hp : ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierP2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  have hv : ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierV2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact barrierTrial_abs_le barrierP2Finite barrierP2Tail
      barrier_finite_lengths.1.le barrierP2_finite_abs_lt_one
      (barrier_tail_lengths.1.le.trans (by norm_num)) hp k
  · exact barrierTrial_abs_le barrierV2Finite barrierV2Tail
      barrier_finite_lengths.2.1.le barrierV2_finite_abs_lt_one
      barrier_tail_lengths.2.le hv k
  · exact barrierTrial_abs_le barrierP1Finite []
      (barrier_finite_lengths.2.2.1.le.trans (by norm_num)) barrierP1_finite_abs_lt_one
      (by simp) (by simp) k
  · exact barrierTrial_abs_le barrierV1Finite []
      (barrier_finite_lengths.2.2.2.le.trans (by norm_num)) barrierV1_finite_abs_lt_one
      (by simp) (by simp) k

theorem barrier_trials_abs_summable :
    Summable (fun k => |barrierP2 k|) ∧ Summable (fun k => |barrierV2 k|) ∧
    Summable (fun k => |barrierP1 k|) ∧ Summable (fun k => |barrierV1 k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * (99 / 100 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left 15
  refine ⟨hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.2)⟩





open Polynomial Filter
open scoped BigOperators



private theorem barrierTrialT_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk


theorem barrierTrialT_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialT_term_norm_le u k hx)


theorem barrierTrialT_tendstoUniformlyOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (barrierTrialT u) atTop (Set.Icc (-1) 1) := by
  unfold barrierTrialT
  apply tendstoUniformlyOn_tsum_nat ((summable_nat_add_iff 1).mpr hu)
  intro k x hx
  exact barrierTrialT_term_norm_le u k (abs_le.mpr hx)



end

section

open scoped BigOperators





end
section

open Polynomial
open scoped BigOperators



end

section

open Polynomial Set Filter
open scoped BigOperators

theorem barrierTrialT_continuousOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    ContinuousOn (barrierTrialT u) (Icc (-1 : ℝ) 1) := by
  refine (barrierTrialT_tendstoUniformlyOn u hu).continuousOn (Frequently.of_forall ?_)
  intro m
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  have hterm : Continuous (fun x : ℝ =>
      u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x *
        (((k + 1 : ℕ) : ℝ)⁻¹)) :=
    (continuous_const.mul (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).continuous).mul
      continuous_const
  simpa only [div_eq_mul_inv] using hterm.continuousOn


end

open Polynomial

private theorem barrier_Tseries_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y /
        ((k + 1 : ℕ) : ℝ))
      (a * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hindex : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by simp
  have ht : HasDerivAt
      (fun y : ℝ => (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y)
      (((k + 1 : ℕ) : ℝ) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
    simpa only [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast,
      hindex, Int.cast_natCast, eval_natCast] using
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).hasDerivAt x
  apply ((ht.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]


theorem barrierTrialT_hasDerivAt_series (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|))
    (huw : Summable (fun k : ℕ => (k : ℝ) * |u k|))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT u)
      (∑' k : ℕ, u (k + 1) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  unfold barrierTrialT
  apply hasDerivAt_tsum_of_isPreconnected ((summable_nat_add_iff 1).mpr huw)
    isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => barrier_Tseries_term_hasDerivAt (u (k + 1)) k y)
    _ (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
    (barrierTrialT_summable u hu (x := 0) (by norm_num)) hx
  intro k y hy
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  rw [norm_mul]
  simp only [Real.norm_eq_abs]
  calc
    |u (k + 1)| * |(Chebyshev.U ℝ (k : ℤ)).eval y| ≤
        |u (k + 1)| * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (barrierChebyshevU_abs_le k hyabs) (abs_nonneg _)
    _ = ((k + 1 : ℕ) : ℝ) * |u (k + 1)| := by push_cast; ring


private theorem barrier_weighted_abs_summable_of_decay (u : ℕ → ℝ)
    (hu : ∀ k, |u k| ≤ 15 * (99 / 100 : ℝ) ^ k) :
    Summable (fun k : ℕ => (k : ℝ) * |u k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * ((k : ℝ) * (99 / 100 : ℝ) ^ k)) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left (15 : ℝ)
  apply hg.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * |u k|)]
  calc
    (k : ℝ) * |u k| ≤ (k : ℝ) * (15 * (99 / 100 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (hu k) (Nat.cast_nonneg k)
    _ = 15 * ((k : ℝ) * (99 / 100 : ℝ) ^ k) := by ring

theorem barrier_trials_weighted_abs_summable :
    Summable (fun k : ℕ => (k : ℝ) * |barrierP2 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierV2 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierP1 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierV1 k|) := by
  exact ⟨barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.2.1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.2.2)⟩

open Polynomial
open scoped BigOperators





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierGlobalMaxReduction
namespace OAI

noncomputable section

namespace InternalCatalan.GlobalMaxReduction

open Set Filter
open scoped Topology

theorem le_on_Icc_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (ha : f a ≤ M) (hb : f b ≤ M)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Icc a b, f x ≤ M := by
  intro x hx
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hcont
  have hcM : f c ≤ M := by
    by_cases hca : c = a
    · simpa only [hca] using ha
    by_cases hcb : c = b
    · simpa only [hcb] using hb
    have hcint : c ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hc.1 (Ne.symm hca), lt_of_le_of_ne hc.2 hcb⟩
    have hlocal : IsLocalMax f c :=
      hmax.isLocalMax (Icc_mem_nhds hcint.1 hcint.2)
    exact hcritical c hcint hlocal.deriv_eq_zero
  exact (hmax hx).trans hcM

theorem exists_left_cutoff {f : ℝ → ℝ} {a x M : ℝ}
    (hlim : Tendsto f (𝓝[>] a) atBot) (hax : a < x) :
    ∃ l ∈ Ioo a x, f l ≤ M := by
  have hinterval : ∀ᶠ l in 𝓝[>] a, l ∈ Ioo a x := Ioo_mem_nhdsGT hax
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem exists_right_cutoff {f : ℝ → ℝ} {x b M : ℝ}
    (hlim : Tendsto f (𝓝[<] b) atBot) (hxb : x < b) :
    ∃ r ∈ Ioo x b, f r ≤ M := by
  have hinterval : ∀ᶠ r in 𝓝[<] b, r ∈ Ioo x b := Ioo_mem_nhdsLT hxb
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem le_on_Ioo_of_limits_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  intro x hx
  obtain ⟨l, hl, hlM⟩ := exists_left_cutoff (M := M) hleft hx.1
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hl.1 hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) hlM hrM
    (fun c hc hd => hcritical c (hsub ⟨hc.1.le, hc.2.le⟩) hd)
    x ⟨hl.2.le, hr.1.le⟩


theorem le_on_Ioo_of_stationary_cover {f : ℝ → ℝ} {a b M : ℝ} {S : Set ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcover : ∀ c ∈ Ioo a b, deriv f c = 0 → c ∈ S)
    (hvalues : ∀ c ∈ S, f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  exact le_on_Ioo_of_limits_of_critical_le hcont hleft hright
    (fun c hc hd => hvalues c (hcover c hc hd))


end InternalCatalan.GlobalMaxReduction

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierRationalSumNumerator
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

def barrierFractionProduct (fs : List (ℚ[X] × ℚ[X])) : ℚ[X] :=
  (fs.map Prod.snd).prod

def barrierFractionNumerator : List (ℚ[X] × ℚ[X]) → ℚ[X]
  | [] => 0
  | aq :: fs => aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs

def barrierFractionSum (fs : List (ℚ[X] × ℚ[X])) (x : ℝ) : ℝ :=
  (fs.map (fun aq : ℚ[X] × ℚ[X] =>
    aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x)).sum

theorem barrierFractionNumerator_eval (fs : List (ℚ[X] × ℚ[X])) (x : ℝ)
    (hprod : (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0) :
    (barrierFractionNumerator fs).eval₂ (Rat.castHom ℝ) x =
      (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x * barrierFractionSum fs x := by
  revert hprod
  induction fs with
  | nil =>
      intro _
      simp [barrierFractionNumerator, barrierFractionProduct, barrierFractionSum]
  | cons aq fs ih =>
      intro hprod
      have hh : aq.2.eval₂ (Rat.castHom ℝ) x *
          (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
        simpa only [barrierFractionProduct, List.map_cons, List.prod_cons, eval₂_mul]
          using hprod
      have hq : aq.2.eval₂ (Rat.castHom ℝ) x ≠ 0 := (mul_ne_zero_iff.mp hh).1
      have ht : (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0 :=
        (mul_ne_zero_iff.mp hh).2
      have hrec := ih ht
      change
        (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs).eval₂
          (Rat.castHom ℝ) x =
        (aq.2 * barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x *
          (aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x +
            barrierFractionSum fs x)
      rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, hrec]
      field_simp [hq]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneRootExistence
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

theorem rationalPolynomial_root_mem_Ioo_of_eval_mul_neg (p : ℚ[X])
    {a b : ℚ} (hab : a < b) (hs : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, x ∈ Set.Ioo (a : ℝ) (b : ℝ) ∧
      (p.map (Rat.castHom ℝ)).eval x = 0 := by
  have heval (q : ℚ) :
      (p.map (Rat.castHom ℝ)).eval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
    change (p.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (p.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hs' : (p.map (Rat.castHom ℝ)).eval (a : ℝ) *
      (p.map (Rat.castHom ℝ)).eval (b : ℝ) < 0 := by
    simp only [heval]
    exact_mod_cast hs
  have hc : ContinuousOn (fun x : ℝ => (p.map (Rat.castHom ℝ)).eval x)
      (Set.Icc (a : ℝ) (b : ℝ)) := (p.map (Rat.castHom ℝ)).continuousOn
  rcases mul_neg_iff.mp hs' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ)) := ⟨hb, ha⟩
    rcases (intermediate_value_Ioo' hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ)) := ⟨ha, hb⟩
    rcases (intermediate_value_Ioo hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneDescartesX0
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierFiniteUDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * Chebyshev.U ℚ (k : ℤ)

def barrierFinitePowerDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * X ^ k











end

section

open Polynomial
























end

section



open Polynomial
open scoped BigOperators




end




open Polynomial



open Polynomial




















end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTrialUHasSum
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_U_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) *
      (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  have hvalue : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hvalue]
  simpa [barrierFiniteCoeff] using hs

private theorem barrierTailRow_U_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * (Chebyshev.U ℝ (k : ℤ)).eval x)
      (r * z / barrierTailQuadraticDen z x).re := by
  have hc : HasSum
      (fun k : ℕ => (r * z ^ (k + 1)) *
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ))
      (r * z / barrierTailQuadraticDen z x) := by
    convert (barrierChebyshevU_hasSum hx hz).mul_left (r * z) using 1
    · rfl
    · funext k
      rw [pow_succ]
      ring
    · simp only [barrierTailQuadraticDen, div_eq_mul_inv, one_mul]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

private theorem barrierTail_U_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_U_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

theorem barrierTrial_U_hasSum (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) *
      (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x +
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) := by
  simpa [barrierTrial, add_mul] using
    (barrierFiniteCoeff_U_hasSum cs x).add (barrierTail_U_hasSum tail htail hx)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXExplicitGroup7
namespace OAI

noncomputable section

namespace InternalCatalan

structure BarrierRationalPairRow where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

def barrierP2RealRows : List (ℚ × ℚ) :=
  [(85 / 100, -9338452 / 100000000), (94 / 100, -2141509 / 100000000)]

def barrierP2PairRows : List BarrierRationalPairRow :=
  [⟨0, 7 / 10, -66277922 / 200000000, 31907569 / 200000000⟩,
   ⟨0, 85 / 100, -1231651 / 200000000, -6002645 / 200000000⟩,
   ⟨92 / 1000, 92 / 100, -3225918 / 200000000, -8928234 / 200000000⟩,
   ⟨-92 / 1000, 92 / 100, -2105536 / 200000000, 9091287 / 200000000⟩]

def barrierV2RealRows : List (ℚ × ℚ) :=
  [(-8 / 10, 15199211 / 100000000), (-96 / 100, 4451662 / 100000000),
   (88 / 100, 2545398 / 100000000), (95 / 100, -4932634 / 100000000),
   (984 / 1000, 11618157 / 100000000)]

def barrierV2PairRows : List BarrierRationalPairRow :=
  [⟨0, 78 / 100, 27238714 / 200000000, 38447936 / 200000000⟩,
   ⟨0, 9 / 10, -31341084 / 200000000, 30188786 / 200000000⟩,
   ⟨0, 955 / 1000, -6693542 / 200000000, -11912254 / 200000000⟩,
   ⟨0, 984 / 1000, 2055213 / 200000000, 21715849 / 200000000⟩]

def barrierExpandRealRows (rs : List (ℚ × ℚ)) : List (ℂ × ℂ) :=
  rs.map (fun ac : ℚ × ℚ => (barrierComplex ac.1 0, barrierComplex ac.2 0))

def barrierExpandPairRow (row : BarrierRationalPairRow) : List (ℂ × ℂ) :=
  barrierConjugatePair (barrierComplex row.a row.b) (barrierComplex row.c row.d)

def barrierExpandPairRows (rs : List BarrierRationalPairRow) : List (ℂ × ℂ) :=
  rs.flatMap barrierExpandPairRow


theorem barrierV2Tail_eq_grouped :
    barrierV2Tail = barrierExpandRealRows barrierV2RealRows ++
      barrierExpandPairRows barrierV2PairRows := by rfl

open Polynomial

def barrierRealLinearQ (a : ℚ) : ℚ[X] := 1 - C a * X

def barrierRealQuadraticQ (a : ℚ) : ℚ[X] := 1 - 2 * C a * X + C (a ^ 2)


def barrierGroupedQuadraticQ (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : ℚ[X] :=
  (rs.map (fun ac : ℚ × ℚ => barrierRealQuadraticQ ac.1)).prod *
    (ps.map (fun row : BarrierRationalPairRow => barrierPairQuadraticQ row.a row.b)).prod


private theorem barrierRealQuadraticQ_eval_complex (a : ℚ) (x : ℝ) :
    (barrierRealQuadraticQ a).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      barrierTailQuadraticDen (barrierComplex a 0) x := by
  apply Complex.ext <;>
    simp [barrierRealQuadraticQ, barrierTailQuadraticDen, barrierComplex, pow_two]
  ring


private theorem barrierPairQuadraticQ_eval_complex (row : BarrierRationalPairRow) (x : ℝ) :
    (barrierPairQuadraticQ row.a row.b).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandPairRow row).map
        (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  apply Complex.ext <;>
    simp [barrierPairQuadraticQ, barrierExpandPairRow, barrierConjugatePair,
      barrierTailQuadraticDen, barrierComplex, pow_two]
  <;> ring

private theorem barrier_prod_map_flatMap {α β : Type*} (rs : List α)
    (g : α → List β) (f : β → ℂ) :
    ((rs.flatMap g).map f).prod = (rs.map (fun r => ((g r).map f).prod)).prod := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]


private theorem barrierGroupedQuadraticQ_eval_complex (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    (barrierGroupedQuadraticQ rs ps).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map
        (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  simp only [barrierGroupedQuadraticQ, eval₂_mul, eval₂_list_prod,
    barrierExpandRealRows, barrierExpandPairRows, List.map_append, List.prod_append,
    barrier_prod_map_flatMap, List.map_map, Function.comp_def,
    barrierRealQuadraticQ_eval_complex, barrierPairQuadraticQ_eval_complex]



def barrierV2QuadraticQ : ℚ[X] :=
  barrierGroupedQuadraticQ barrierV2RealRows barrierV2PairRows



theorem barrierV2QuadraticQ_eval_complex (x : ℝ) :
    barrierV2QuadraticQ.eval₂ (Rat.castHom ℂ) (x : ℂ) =
      (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  rw [barrierV2Tail_eq_grouped]
  exact barrierGroupedQuadraticQ_eval_complex _ _ x


def barrierCase2QY : ℚ[X] := X * (1 - X) * barrierV2QuadraticQ


theorem barrierCase2QY_eval_complex (x : ℝ) :
    barrierCase2QY.eval₂ (Rat.castHom ℂ) (x : ℂ) = barrierCase2QYValue x := by
  simp only [barrierCase2QY, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one,
    barrierV2QuadraticQ_eval_complex, barrierCase2QYValue]

private theorem barrier_ratPolynomial_eval_complex (p : ℚ[X]) (x : ℝ) :
    ((p.eval₂ (Rat.castHom ℝ) x : ℝ) : ℂ) = p.eval₂ (Rat.castHom ℂ) (x : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp


theorem barrierCase2QY_eval_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2QY.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  intro hzero
  apply barrierCase2QYValue_ne_zero hx hx0 hx1
  rw [← barrierCase2QY_eval_complex, ← barrier_ratPolynomial_eval_complex]
  simp only [hzero, Complex.ofReal_zero]

open Polynomial

def barrierGroupedLinearTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) / (1 - (ac.1 : ℝ) * x))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairLinearA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairLinearQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum

def barrierGroupedQuadraticTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) /
      (1 - 2 * (ac.1 : ℝ) * x + (ac.1 : ℝ) ^ 2))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairQuadraticA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairQuadraticQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum

private theorem barrierComplex_real (a : ℚ) :
    barrierComplex a 0 = ((a : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [barrierComplex]


private theorem barrier_realTailQuadratic_re (a c : ℚ) (x : ℝ) :
    (barrierComplex c 0 * barrierComplex a 0 /
      barrierTailQuadraticDen (barrierComplex a 0) x).re =
      (c : ℝ) * (a : ℝ) / (1 - 2 * (a : ℝ) * x + (a : ℝ) ^ 2) := by
  have hd : barrierTailQuadraticDen (barrierComplex a 0) x =
      ((1 - 2 * (a : ℝ) * x + (a : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp only [barrierTailQuadraticDen, barrierComplex_real, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_pow]
    ring
  rw [hd]
  simp only [barrierComplex_real, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]

private theorem barrier_list_map_sum_re {α : Type*} (rs : List α)
    (f : α → ℂ) (g : α → ℝ) (h : ∀ a, (f a).re = g a) :
    (rs.map f).sum.re = (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re, h a, ih]

private theorem barrier_list_flatMap_sum_re {α : Type*} (rs : List α)
    (expand : α → List (ℂ × ℂ)) (f : ℂ × ℂ → ℂ) (g : α → ℝ)
    (h : ∀ a, ((expand a).map f).sum.re = g a) :
    ((rs.flatMap expand).map f).sum.re = (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, Complex.add_re,
      List.map_cons, List.sum_cons, h a, ih]

private theorem barrier_grouped_tail_sum_re (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (f : ℂ × ℂ → ℂ)
    (g : ℚ × ℚ → ℝ) (h : BarrierRationalPairRow → ℝ)
    (hreal : ∀ ac : ℚ × ℚ,
      (f (barrierComplex ac.1 0, barrierComplex ac.2 0)).re = g ac)
    (hpair : ∀ row : BarrierRationalPairRow,
      ((barrierExpandPairRow row).map f).sum.re = h row) :
    ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map f).sum.re =
      (rs.map g).sum + (ps.map h).sum := by
  have hr : ((barrierExpandRealRows rs).map f).sum.re = (rs.map g).sum := by
    simpa only [barrierExpandRealRows, List.map_map, Function.comp_def] using
      barrier_list_map_sum_re rs
        (fun ac : ℚ × ℚ => f (barrierComplex ac.1 0, barrierComplex ac.2 0)) g hreal
  have hp : ((barrierExpandPairRows ps).map f).sum.re = (ps.map h).sum := by
    simpa only [barrierExpandPairRows] using
      barrier_list_flatMap_sum_re ps barrierExpandPairRow f h hpair
  rw [List.map_append, List.sum_append, Complex.add_re, hr, hp]



theorem barrierV2Tail_quadratic_sum_re_eq_grouped (x : ℝ) :
    (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      barrierGroupedQuadraticTailValue barrierV2RealRows barrierV2PairRows x := by
  rw [barrierV2Tail_eq_grouped]
  unfold barrierGroupedQuadraticTailValue
  apply barrier_grouped_tail_sum_re
  · intro ac
    exact barrier_realTailQuadratic_re ac.1 ac.2 x
  · intro row
    exact barrierConjugatePair_quadratic_eq_ratPolynomial row.a row.b row.c row.d x

def barrierLinearFractions (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : List (ℚ[X] × ℚ[X]) :=
  rs.map (fun ac : ℚ × ℚ => (C (ac.2 * ac.1), barrierRealLinearQ ac.1)) ++
    ps.map (fun row : BarrierRationalPairRow =>
      (barrierPairLinearA row.a row.b row.c row.d, barrierPairLinearQ row.a row.b))

def barrierQuadraticFractions (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : List (ℚ[X] × ℚ[X]) :=
  rs.map (fun ac : ℚ × ℚ => (C (ac.2 * ac.1), barrierRealQuadraticQ ac.1)) ++
    ps.map (fun row : BarrierRationalPairRow =>
      (barrierPairQuadraticA row.a row.b row.c row.d, barrierPairQuadraticQ row.a row.b))

def barrierScaleFractions (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) : List (ℚ[X] × ℚ[X]) :=
  fs.map (fun aq : ℚ[X] × ℚ[X] => (C c * aq.1, aq.2))


private theorem barrierQuadraticFractions_product (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) :
    barrierFractionProduct (barrierQuadraticFractions rs ps) = barrierGroupedQuadraticQ rs ps := by
  simp [barrierFractionProduct, barrierQuadraticFractions, barrierGroupedQuadraticQ,
    List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem barrierFractionProduct_append (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (fs ++ gs) = barrierFractionProduct fs * barrierFractionProduct gs := by
  simp [barrierFractionProduct, List.map_append, List.prod_append]

private theorem barrierScaleFractions_product (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (barrierScaleFractions c fs) = barrierFractionProduct fs := by
  simp [barrierFractionProduct, barrierScaleFractions, List.map_map, Function.comp_def]


private theorem barrierQuadraticFractions_sum (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    barrierFractionSum (barrierQuadraticFractions rs ps) x =
      barrierGroupedQuadraticTailValue rs ps x := by
  simp [barrierFractionSum, barrierQuadraticFractions, barrierGroupedQuadraticTailValue,
    barrierRealQuadraticQ, eval₂_pow, List.map_append, List.sum_append, List.map_map, Function.comp_def]

private theorem barrierFractionSum_append (fs gs : List (ℚ[X] × ℚ[X])) (x : ℝ) :
    barrierFractionSum (fs ++ gs) x = barrierFractionSum fs x + barrierFractionSum gs x := by
  simp [barrierFractionSum, List.map_append, List.sum_append]

private theorem barrierScaleFractions_sum (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) (x : ℝ) :
    barrierFractionSum (barrierScaleFractions c fs) x = (c : ℝ) * barrierFractionSum fs x := by
  simpa only [barrierFractionSum, barrierScaleFractions, List.map_map, Function.comp_def,
    eval₂_mul, eval₂_C, Rat.coe_castHom, mul_div_assoc] using
    List.sum_map_mul_left fs
      (fun aq : ℚ[X] × ℚ[X] =>
        aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x) (c : ℝ)


def barrierCase2YFractions : List (ℚ[X] × ℚ[X]) :=
  [(C (7 / 48), X), (-C (1 / 12), 1 - X),
   (C 2 * barrierFiniteUDerivative barrierV2Finite, 1)] ++
  barrierScaleFractions 2 (barrierQuadraticFractions barrierV2RealRows barrierV2PairRows)

def barrierCase2XDerivativeFormula (x : ℝ) : ℝ :=
  (19 / 48) / x - (1 / 12) / (1 - x) - (65 / 24) * x / (1 + x ^ 2) -
    4 * ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) -
    ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re)

def barrierCase2YDerivativeFormula (x : ℝ) : ℝ :=
  (7 / 48) / x - (1 / 12) / (1 - x) +
    2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)


theorem barrierCase2YFractions_product :
    barrierFractionProduct barrierCase2YFractions = barrierCase2QY := by
  simp only [barrierCase2YFractions, barrierFractionProduct_append,
    barrierScaleFractions_product, barrierQuadraticFractions_product]
  simp only [barrierFractionProduct, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, barrierCase2QY, barrierV2QuadraticQ]


theorem barrierCase2YFractions_sum (x : ℝ) :
    barrierFractionSum barrierCase2YFractions x = barrierCase2YDerivativeFormula x := by
  simp only [barrierCase2YFractions, barrierFractionSum_append, barrierScaleFractions_sum,
    barrierQuadraticFractions_sum]
  unfold barrierCase2YDerivativeFormula
  rw [barrierV2Tail_quadratic_sum_re_eq_grouped]
  norm_num [barrierFractionSum]
  ring

def barrierCase2AY : ℚ[X] := barrierFractionNumerator barrierCase2YFractions


theorem barrierCase2AY_clears_denominator {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2AY.eval₂ (Rat.castHom ℝ) x =
      barrierCase2QY.eval₂ (Rat.castHom ℝ) x * barrierCase2YDerivativeFormula x := by
  have hprod : (barrierFractionProduct barrierCase2YFractions).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
    rw [barrierCase2YFractions_product]
    exact barrierCase2QY_eval_ne_zero hx hx0 hx1
  simpa only [barrierCase2AY, barrierCase2YFractions_product, barrierCase2YFractions_sum] using
    barrierFractionNumerator_eval barrierCase2YFractions x hprod

def barrierCase2AYExplicit : ℚ[X] :=
  C (6139400617553994264158059821657057/46566128730773925781250000000000000000000) +
  C (-33561002014090297827119379306520481903587029/2328306436538696289062500000000000000000000000000) * X ^ 1 +
  C (33074408368087250152306475891437531860945477517/55879354476928710937500000000000000000000000000000) * X ^ 2 +
  C (-66077599258590392372719123938575511970776167147/3725290298461914062500000000000000000000000000000) * X ^ 3 +
  C (14122789091810067197857825223683987234653915605963/27939677238464355468750000000000000000000000000000) * X ^ 4 +
  C (-86750624167723639733042199688839383716982023693179/9313225746154785156250000000000000000000000000000) * X ^ 5 +
  C (1316740050792652908780607827887161749864672742734289/13969838619232177734375000000000000000000000000000) * X ^ 6 +
  C (-1212115504788431760218102810891669598130270751340433/2328306436538696289062500000000000000000000000000) * X ^ 7 +
  C (1852388549149144304739559910201030352481292410036837/1164153218269348144531250000000000000000000000000) * X ^ 8 +
  C (-1747032160720335963573846025320381769579591080592813/582076609134674072265625000000000000000000000000) * X ^ 9 +
  C (1739901547181074548477858628301501635372218788391207/291038304567337036132812500000000000000000000000) * X ^ 10 +
  C (-58398556052369231733549806414095197880896863913593/4547473508864641189575195312500000000000000000) * X ^ 11 +
  C (-224485494639452816006183298746436192812684184457/227373675443232059478759765625000000000000000) * X ^ 12 +
  C (2269599238587048364445509906643305862019685574511/29103830456733703613281250000000000000000000) * X ^ 13 +
  C (-8312207244243935884298339203836978265449226071511/72759576141834259033203125000000000000000000) * X ^ 14 +
  C (-378061677768450552949892491615489728857434329461/3637978807091712951660156250000000000000000) * X ^ 15 +
  C (6336754667545200773744815681065942607080067871/18189894035458564758300781250000000000000) * X ^ 16 +
  C (-23670761651501264423340946642925921358111/355271367880050092935562133789062500) * X ^ 17 +
  C (-1591316942855983330678136272429722751753611/3637978807091712951660156250000000000) * X ^ 18 +
  C (2196441555444677056714374493311795175923/7275957614183425903320312500000000) * X ^ 19 +
  C (19920658548966767554832955780992945163/90949470177292823791503906250000) * X ^ 20 +
  C (-252630662688341342631694749106212633/909494701772928237915039062500) * X ^ 21 +
  C (8040903690975846553048561271748/1818989403545856475830078125) * X ^ 22 +
  C (1234121953779801858851339053248/14551915228366851806640625) * X ^ 23 +
  C (-3121113626614610031471086592/116415321826934814453125) * X ^ 24

private theorem barrier_case2_U_3 :
    Chebyshev.U ℚ 3 = 2 * X * Chebyshev.U ℚ 2 - Chebyshev.U ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 1

private theorem barrier_case2_U_4 :
    Chebyshev.U ℚ 4 = 2 * X * Chebyshev.U ℚ 3 - Chebyshev.U ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 2

private theorem barrier_case2_U_5 :
    Chebyshev.U ℚ 5 = 2 * X * Chebyshev.U ℚ 4 - Chebyshev.U ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 3

private theorem barrier_case2_U_6 :
    Chebyshev.U ℚ 6 = 2 * X * Chebyshev.U ℚ 5 - Chebyshev.U ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 4

private theorem barrier_case2_U_7 :
    Chebyshev.U ℚ 7 = 2 * X * Chebyshev.U ℚ 6 - Chebyshev.U ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 5

private theorem barrier_case2_U_8 :
    Chebyshev.U ℚ 8 = 2 * X * Chebyshev.U ℚ 7 - Chebyshev.U ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 6

private theorem barrier_case2_U_9 :
    Chebyshev.U ℚ 9 = 2 * X * Chebyshev.U ℚ 8 - Chebyshev.U ℚ 7 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 7

theorem barrierCase2AY_eq_explicit : barrierCase2AY = barrierCase2AYExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2AY, barrierCase2AYExplicit, barrierFractionNumerator,
    barrierFractionProduct, barrierCase2YFractions, barrierScaleFractions,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    barrierFiniteUDerivative, barrierFinitePowerDerivative, barrierP2Finite, barrierV2Finite,
    Finset.sum_range_succ, eval_finsetSum, eval_list_prod,
    Chebyshev.U_two, barrier_case2_U_3, barrier_case2_U_4,
    barrier_case2_U_5, barrier_case2_U_6, barrier_case2_U_7,
    barrier_case2_U_8, barrier_case2_U_9]
  ring

theorem barrierCase2AY_natDegree : barrierCase2AY.natDegree = 24 := by
  rw [barrierCase2AY_eq_explicit]
  unfold barrierCase2AYExplicit
  compute_degree!







def barrierCase2AYCoefficient (k : ℕ) : ℚ :=
  ([6139400617553994264158059821657057/46566128730773925781250000000000000000000, -33561002014090297827119379306520481903587029/2328306436538696289062500000000000000000000000000, 33074408368087250152306475891437531860945477517/55879354476928710937500000000000000000000000000000, -66077599258590392372719123938575511970776167147/3725290298461914062500000000000000000000000000000, 14122789091810067197857825223683987234653915605963/27939677238464355468750000000000000000000000000000, -86750624167723639733042199688839383716982023693179/9313225746154785156250000000000000000000000000000, 1316740050792652908780607827887161749864672742734289/13969838619232177734375000000000000000000000000000, -1212115504788431760218102810891669598130270751340433/2328306436538696289062500000000000000000000000000, 1852388549149144304739559910201030352481292410036837/1164153218269348144531250000000000000000000000000, -1747032160720335963573846025320381769579591080592813/582076609134674072265625000000000000000000000000, 1739901547181074548477858628301501635372218788391207/291038304567337036132812500000000000000000000000, -58398556052369231733549806414095197880896863913593/4547473508864641189575195312500000000000000000, -224485494639452816006183298746436192812684184457/227373675443232059478759765625000000000000000, 2269599238587048364445509906643305862019685574511/29103830456733703613281250000000000000000000, -8312207244243935884298339203836978265449226071511/72759576141834259033203125000000000000000000, -378061677768450552949892491615489728857434329461/3637978807091712951660156250000000000000000, 6336754667545200773744815681065942607080067871/18189894035458564758300781250000000000000, -23670761651501264423340946642925921358111/355271367880050092935562133789062500, -1591316942855983330678136272429722751753611/3637978807091712951660156250000000000, 2196441555444677056714374493311795175923/7275957614183425903320312500000000, 19920658548966767554832955780992945163/90949470177292823791503906250000, -252630662688341342631694749106212633/909494701772928237915039062500, 8040903690975846553048561271748/1818989403545856475830078125, 1234121953779801858851339053248/14551915228366851806640625, -3121113626614610031471086592/116415321826934814453125] : List ℚ).getD k 0

private theorem barrierCase2AY_eval_quarter_ne_zero :
    barrierCase2AY.eval (1 / 4) ≠ 0 := by
  rw [barrierCase2AY_eq_explicit]
  norm_num [barrierCase2AYExplicit, eval_pow]

private theorem barrierCase2AY_eval_half_ne_zero :
    barrierCase2AY.eval (1 / 2) ≠ 0 := by
  rw [barrierCase2AY_eq_explicit]
  norm_num [barrierCase2AYExplicit, eval_pow]

private theorem barrierCase2AY_eval_three_quarters_ne_zero :
    barrierCase2AY.eval (3 / 4) ≠ 0 := by
  rw [barrierCase2AY_eq_explicit]
  norm_num [barrierCase2AYExplicit, eval_pow]

theorem barrierCase2AY_quarter_nonzero :
    barrierCase2AY.eval (1 / 4) ≠ 0 ∧
      barrierCase2AY.eval (1 / 2) ≠ 0 ∧
      barrierCase2AY.eval (3 / 4) ≠ 0 := by
  exact ⟨barrierCase2AY_eval_quarter_ne_zero, barrierCase2AY_eval_half_ne_zero,
    barrierCase2AY_eval_three_quarters_ne_zero⟩



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesY0Group0
namespace OAI

namespace InternalCatalan

section
open Polynomial

theorem barrierCase2AY_coeff_0 :
    barrierCase2AY.coeff 0 = barrierCase2AYCoefficient 0 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero]

theorem barrierCase2AY_coeff_1 :
    barrierCase2AY.coeff 1 = barrierCase2AYCoefficient 1 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_2 :
    barrierCase2AY.coeff 2 = barrierCase2AYCoefficient 2 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_3 :
    barrierCase2AY.coeff 3 = barrierCase2AYCoefficient 3 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_4 :
    barrierCase2AY.coeff 4 = barrierCase2AYCoefficient 4 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_5 :
    barrierCase2AY.coeff 5 = barrierCase2AYCoefficient 5 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_6 :
    barrierCase2AY.coeff 6 = barrierCase2AYCoefficient 6 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_7 :
    barrierCase2AY.coeff 7 = barrierCase2AYCoefficient 7 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_8 :
    barrierCase2AY.coeff 8 = barrierCase2AYCoefficient 8 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_9 :
    barrierCase2AY.coeff 9 = barrierCase2AYCoefficient 9 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_10 :
    barrierCase2AY.coeff 10 = barrierCase2AYCoefficient 10 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_11 :
    barrierCase2AY.coeff 11 = barrierCase2AYCoefficient 11 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_12 :
    barrierCase2AY.coeff 12 = barrierCase2AYCoefficient 12 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_13 :
    barrierCase2AY.coeff 13 = barrierCase2AYCoefficient 13 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_14 :
    barrierCase2AY.coeff 14 = barrierCase2AYCoefficient 14 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_15 :
    barrierCase2AY.coeff 15 = barrierCase2AYCoefficient 15 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_16 :
    barrierCase2AY.coeff 16 = barrierCase2AYCoefficient 16 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_17 :
    barrierCase2AY.coeff 17 = barrierCase2AYCoefficient 17 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_18 :
    barrierCase2AY.coeff 18 = barrierCase2AYCoefficient 18 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_19 :
    barrierCase2AY.coeff 19 = barrierCase2AYCoefficient 19 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_20 :
    barrierCase2AY.coeff 20 = barrierCase2AYCoefficient 20 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_21 :
    barrierCase2AY.coeff 21 = barrierCase2AYCoefficient 21 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_22 :
    barrierCase2AY.coeff 22 = barrierCase2AYCoefficient 22 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_23 :
    barrierCase2AY.coeff 23 = barrierCase2AYCoefficient 23 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AY_coeff_24 :
    barrierCase2AY.coeff 24 = barrierCase2AYCoefficient 24 := by
  rw [barrierCase2AY_eq_explicit]
  simp only [barrierCase2AYExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYCoefficient, List.getD_cons_zero, List.getD_cons_succ]

end

theorem barrierCase2AY_coeff_small (k : ℕ) (hk : k < 25) :
    barrierCase2AY.coeff k = barrierCase2AYCoefficient k := by
  interval_cases k
  · exact barrierCase2AY_coeff_0
  · exact barrierCase2AY_coeff_1
  · exact barrierCase2AY_coeff_2
  · exact barrierCase2AY_coeff_3
  · exact barrierCase2AY_coeff_4
  · exact barrierCase2AY_coeff_5
  · exact barrierCase2AY_coeff_6
  · exact barrierCase2AY_coeff_7
  · exact barrierCase2AY_coeff_8
  · exact barrierCase2AY_coeff_9
  · exact barrierCase2AY_coeff_10
  · exact barrierCase2AY_coeff_11
  · exact barrierCase2AY_coeff_12
  · exact barrierCase2AY_coeff_13
  · exact barrierCase2AY_coeff_14
  · exact barrierCase2AY_coeff_15
  · exact barrierCase2AY_coeff_16
  · exact barrierCase2AY_coeff_17
  · exact barrierCase2AY_coeff_18
  · exact barrierCase2AY_coeff_19
  · exact barrierCase2AY_coeff_20
  · exact barrierCase2AY_coeff_21
  · exact barrierCase2AY_coeff_22
  · exact barrierCase2AY_coeff_23
  · exact barrierCase2AY_coeff_24

open Polynomial

def barrierCase2AYTransform0Coefficient (h : ℕ) : ℚ :=
  ([6139400617553994264158059821657057/46566128730773925781250000000000000000000,
    -4091879049831125359160692162566608303587029/9313225746154785156250000000000000000000000000000,
    -1698874465296400209069344602086923145554936503/178813934326171875000000000000000000000000000000000,
    -386806442085509445485744794549405491033327527117/3576278686523437500000000000000000000000000000000000,
    -2011405504514275385872154240728192890514645824943/7152557373046875000000000000000000000000000000000000,
    27234848024203894401518312556228157540414575245541/9536743164062500000000000000000000000000000000000000,
    454325143116180952690743446349797334112840913231913/19073486328125000000000000000000000000000000000000000,
    2867790670020576185577035574269328787164574541852919/38146972656250000000000000000000000000000000000000000,
    6934629715726934547911911020541033275992684880416759/76293945312500000000000000000000000000000000000000000,
    -20859728197749686648655654802486853752664364619088237/152587890625000000000000000000000000000000000000000000,
    -234739528391705334384896032983954594556790281689774527/305175781250000000000000000000000000000000000000000000,
    -173923803242614290722764126061317264577033446481819069/114440917968750000000000000000000000000000000000000000,
    -1516022266593914700842861545847933209612401314256279163/915527343750000000000000000000000000000000000000000000,
    -2754181145944614170739508758005549905389383018143489963/3662109375000000000000000000000000000000000000000000000,
    326355594747103789521331197391310787982895037000152779/488281250000000000000000000000000000000000000000000000,
    781048772305121556718639362683885716134665809859172019/488281250000000000000000000000000000000000000000000000,
    48411970989804846089166316900334863566841772792206559/30517578125000000000000000000000000000000000000000000,
    152631389037685245024546110862272979980545229515991301/152587890625000000000000000000000000000000000000000000,
    1041145826984330846397205909068261651288924927975544199/2441406250000000000000000000000000000000000000000000000,
    58102709081083581172227941177245292920859419681179131/488281250000000000000000000000000000000000000000000000,
    66592701504517610958614702541909691926109828765843273/3662109375000000000000000000000000000000000000000000000,
    -13330691392117722812153850815135102023718385734269/457763671875000000000000000000000000000000000000000000,
    -215983146690043837621114874020848362803740139904321/366210937500000000000000000000000000000000000000000000,
    -62787068206991434684987150068285048297869866983281/610351562500000000000000000000000000000000000000000000,
    -1837264500726327467065173687765768006566633848311/305175781250000000000000000000000000000000000000000000] : List ℚ).getD h 0

noncomputable def barrierCase2AYTransform0Explicit : ℝ[X] :=
  C (6139400617553994264158059821657057/46566128730773925781250000000000000000000) +
    C (-4091879049831125359160692162566608303587029/9313225746154785156250000000000000000000000000000) * X ^ 1 +
    C (-1698874465296400209069344602086923145554936503/178813934326171875000000000000000000000000000000000) * X ^ 2 +
    C (-386806442085509445485744794549405491033327527117/3576278686523437500000000000000000000000000000000000) * X ^ 3 +
    C (-2011405504514275385872154240728192890514645824943/7152557373046875000000000000000000000000000000000000) * X ^ 4 +
    C (27234848024203894401518312556228157540414575245541/9536743164062500000000000000000000000000000000000000) * X ^ 5 +
    C (454325143116180952690743446349797334112840913231913/19073486328125000000000000000000000000000000000000000) * X ^ 6 +
    C (2867790670020576185577035574269328787164574541852919/38146972656250000000000000000000000000000000000000000) * X ^ 7 +
    C (6934629715726934547911911020541033275992684880416759/76293945312500000000000000000000000000000000000000000) * X ^ 8 +
    C (-20859728197749686648655654802486853752664364619088237/152587890625000000000000000000000000000000000000000000) * X ^ 9 +
    C (-234739528391705334384896032983954594556790281689774527/305175781250000000000000000000000000000000000000000000) * X ^ 10 +
    C (-173923803242614290722764126061317264577033446481819069/114440917968750000000000000000000000000000000000000000) * X ^ 11 +
    C (-1516022266593914700842861545847933209612401314256279163/915527343750000000000000000000000000000000000000000000) * X ^ 12 +
    C (-2754181145944614170739508758005549905389383018143489963/3662109375000000000000000000000000000000000000000000000) * X ^ 13 +
    C (326355594747103789521331197391310787982895037000152779/488281250000000000000000000000000000000000000000000000) * X ^ 14 +
    C (781048772305121556718639362683885716134665809859172019/488281250000000000000000000000000000000000000000000000) * X ^ 15 +
    C (48411970989804846089166316900334863566841772792206559/30517578125000000000000000000000000000000000000000000) * X ^ 16 +
    C (152631389037685245024546110862272979980545229515991301/152587890625000000000000000000000000000000000000000000) * X ^ 17 +
    C (1041145826984330846397205909068261651288924927975544199/2441406250000000000000000000000000000000000000000000000) * X ^ 18 +
    C (58102709081083581172227941177245292920859419681179131/488281250000000000000000000000000000000000000000000000) * X ^ 19 +
    C (66592701504517610958614702541909691926109828765843273/3662109375000000000000000000000000000000000000000000000) * X ^ 20 +
    C (-13330691392117722812153850815135102023718385734269/457763671875000000000000000000000000000000000000000000) * X ^ 21 +
    C (-215983146690043837621114874020848362803740139904321/366210937500000000000000000000000000000000000000000000) * X ^ 22 +
    C (-62787068206991434684987150068285048297869866983281/610351562500000000000000000000000000000000000000000000) * X ^ 23 +
    C (-1837264500726327467065173687765768006566633848311/305175781250000000000000000000000000000000000000000000) * X ^ 24

theorem barrierCase2AYTransform0Explicit_natDegree :
    barrierCase2AYTransform0Explicit.natDegree = 24 := by
  unfold barrierCase2AYTransform0Explicit
  compute_degree!

open Polynomial

def barrierCase2AYTransform1Coefficient (h : ℕ) : ℚ :=
  ([-1837264500726327467065173687765768006566633848311/305175781250000000000000000000000000000000000000000000,
    -4543612954509440086130780958289147213301079298183/24414062500000000000000000000000000000000000000000000,
    -4585340373696594343417058168441352424410041667040891/1831054687500000000000000000000000000000000000000000000,
    -353353512043793437620914233878325861503566527058827/18310546875000000000000000000000000000000000000000000,
    -335581703729655501780846222922286161248351878081932847/3662109375000000000000000000000000000000000000000000000,
    -603034288475528815033313480078500440970522939954790199/2441406250000000000000000000000000000000000000000000000,
    -209308792287293916049862640946140879464891526552269491/2441406250000000000000000000000000000000000000000000000,
    758554565596682285463003089578898507186573455834392583/305175781250000000000000000000000000000000000000000000,
    7914562431913865407893525949086976963775369402833984301/610351562500000000000000000000000000000000000000000000,
    96692848064543941140912945929378634843565684112381544769/2441406250000000000000000000000000000000000000000000000,
    211905183677909517706693221034273505846772559645342813013/2441406250000000000000000000000000000000000000000000000,
    531250671878855642828234172991628338318967749683190977959/3662109375000000000000000000000000000000000000000000000,
    34672403362031486993312613102579602698386779981561628097/183105468750000000000000000000000000000000000000000000,
    44477862569171801502699886618029990414622599937583285717/228881835937500000000000000000000000000000000000000000,
    47545667157899139476391785838163013908719392497596899311/305175781250000000000000000000000000000000000000000000,
    14549306343350769488460149121479276194807016180723328621/152587890625000000000000000000000000000000000000000000,
    640860209435411201888841882930832098143048810102286237/15258789062500000000000000000000000000000000000000000,
    419130757722101818558111439369352373484985041994928369/38146972656250000000000000000000000000000000000000000,
    -699047864106370576100329295623101592966401829106419/2384185791015625000000000000000000000000000000000000,
    -8593956182909203692568227523046688720178213449193409/4768371582031250000000000000000000000000000000000000,
    -12994424380851388913259988574397330186144455052082697/14305114746093750000000000000000000000000000000000000,
    -1840251482187528259359203971793492932968853189914619/7152557373046875000000000000000000000000000000000000,
    -160484979401671022917453651513411511977179688283687/3576278686523437500000000000000000000000000000000000,
    -107221208095505324801116820723830487432299614401/23841857910156250000000000000000000000000000000000,
    -29468567785849371012404257102782431370391111831/149011611938476562500000000000000000000000000000000] : List ℚ).getD h 0

noncomputable def barrierCase2AYTransform1Explicit : ℝ[X] :=
  C (-1837264500726327467065173687765768006566633848311/305175781250000000000000000000000000000000000000000000) +
    C (-4543612954509440086130780958289147213301079298183/24414062500000000000000000000000000000000000000000000) * X ^ 1 +
    C (-4585340373696594343417058168441352424410041667040891/1831054687500000000000000000000000000000000000000000000) * X ^ 2 +
    C (-353353512043793437620914233878325861503566527058827/18310546875000000000000000000000000000000000000000000) * X ^ 3 +
    C (-335581703729655501780846222922286161248351878081932847/3662109375000000000000000000000000000000000000000000000) * X ^ 4 +
    C (-603034288475528815033313480078500440970522939954790199/2441406250000000000000000000000000000000000000000000000) * X ^ 5 +
    C (-209308792287293916049862640946140879464891526552269491/2441406250000000000000000000000000000000000000000000000) * X ^ 6 +
    C (758554565596682285463003089578898507186573455834392583/305175781250000000000000000000000000000000000000000000) * X ^ 7 +
    C (7914562431913865407893525949086976963775369402833984301/610351562500000000000000000000000000000000000000000000) * X ^ 8 +
    C (96692848064543941140912945929378634843565684112381544769/2441406250000000000000000000000000000000000000000000000) * X ^ 9 +
    C (211905183677909517706693221034273505846772559645342813013/2441406250000000000000000000000000000000000000000000000) * X ^ 10 +
    C (531250671878855642828234172991628338318967749683190977959/3662109375000000000000000000000000000000000000000000000) * X ^ 11 +
    C (34672403362031486993312613102579602698386779981561628097/183105468750000000000000000000000000000000000000000000) * X ^ 12 +
    C (44477862569171801502699886618029990414622599937583285717/228881835937500000000000000000000000000000000000000000) * X ^ 13 +
    C (47545667157899139476391785838163013908719392497596899311/305175781250000000000000000000000000000000000000000000) * X ^ 14 +
    C (14549306343350769488460149121479276194807016180723328621/152587890625000000000000000000000000000000000000000000) * X ^ 15 +
    C (640860209435411201888841882930832098143048810102286237/15258789062500000000000000000000000000000000000000000) * X ^ 16 +
    C (419130757722101818558111439369352373484985041994928369/38146972656250000000000000000000000000000000000000000) * X ^ 17 +
    C (-699047864106370576100329295623101592966401829106419/2384185791015625000000000000000000000000000000000000) * X ^ 18 +
    C (-8593956182909203692568227523046688720178213449193409/4768371582031250000000000000000000000000000000000000) * X ^ 19 +
    C (-12994424380851388913259988574397330186144455052082697/14305114746093750000000000000000000000000000000000000) * X ^ 20 +
    C (-1840251482187528259359203971793492932968853189914619/7152557373046875000000000000000000000000000000000000) * X ^ 21 +
    C (-160484979401671022917453651513411511977179688283687/3576278686523437500000000000000000000000000000000000) * X ^ 22 +
    C (-107221208095505324801116820723830487432299614401/23841857910156250000000000000000000000000000000000) * X ^ 23 +
    C (-29468567785849371012404257102782431370391111831/149011611938476562500000000000000000000000000000000) * X ^ 24

theorem barrierCase2AYTransform1Explicit_natDegree :
    barrierCase2AYTransform1Explicit.natDegree = 24 := by
  unfold barrierCase2AYTransform1Explicit
  compute_degree!

theorem barrierCase2AY_transform0_ratCoeff_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 0 =
      barrierCase2AYTransform0Coefficient 0 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 1 =
      barrierCase2AYTransform0Coefficient 1 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 2 =
      barrierCase2AYTransform0Coefficient 2 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 3 =
      barrierCase2AYTransform0Coefficient 3 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 4 =
      barrierCase2AYTransform0Coefficient 4 := by decide +kernel

theorem barrierCase2AYTransform0Explicit_coeff_0 :
    barrierCase2AYTransform0Explicit.coeff 0 = (barrierCase2AYTransform0Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_1 :
    barrierCase2AYTransform0Explicit.coeff 1 = (barrierCase2AYTransform0Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_2 :
    barrierCase2AYTransform0Explicit.coeff 2 = (barrierCase2AYTransform0Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_3 :
    barrierCase2AYTransform0Explicit.coeff 3 = (barrierCase2AYTransform0Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_4 :
    barrierCase2AYTransform0Explicit.coeff 4 = (barrierCase2AYTransform0Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0
namespace OAI

namespace InternalCatalan

section




open Polynomial





end
section


end

noncomputable section

open Polynomial
open scoped BigOperators


def barrierCase2AYFiniteEval (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 25, barrierCase2AYCoefficient k * x ^ k


theorem barrierCase2AY_eval_finite (x : ℚ) :
    barrierCase2AY.eval x = barrierCase2AYFiniteEval x := by
  have hd : barrierCase2AY.natDegree < 25 := by
    rw [barrierCase2AY_natDegree]
    decide
  calc
    barrierCase2AY.eval x =
        ∑ k ∈ Finset.range 25, barrierCase2AY.coeff k * x ^ k :=
      Polynomial.eval_eq_sum_range' hd x
    _ = barrierCase2AYFiniteEval x := by
      unfold barrierCase2AYFiniteEval
      apply Finset.sum_congr rfl
      intro k hk
      rw [barrierCase2AY_coeff_small k (Finset.mem_range.mp hk)]

end

section
open Polynomial







end




















theorem barrierCase2AY_bracket_sign_00 :
    barrierCase2AY.eval (barrierBracketLeft (176402802)) *
      barrierCase2AY.eval (barrierBracketRight (176402802)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (176402802)),
    barrierCase2AY_eval_finite (barrierBracketRight (176402802))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_01 :
    barrierCase2AY.eval (barrierBracketLeft (330649406)) *
      barrierCase2AY.eval (barrierBracketRight (330649406)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (330649406)),
    barrierCase2AY_eval_finite (barrierBracketRight (330649406))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_02 :
    barrierCase2AY.eval (barrierBracketLeft (764952882)) *
      barrierCase2AY.eval (barrierBracketRight (764952882)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (764952882)),
    barrierCase2AY_eval_finite (barrierBracketRight (764952882))]
  decide +kernel

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesY0
namespace OAI

namespace InternalCatalan

section

open Polynomial

theorem barrierCase2AY_transform0_ratCoeff_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 5 =
      barrierCase2AYTransform0Coefficient 5 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 6 =
      barrierCase2AYTransform0Coefficient 6 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 7 =
      barrierCase2AYTransform0Coefficient 7 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 8 =
      barrierCase2AYTransform0Coefficient 8 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 9 =
      barrierCase2AYTransform0Coefficient 9 := by decide +kernel

theorem barrierCase2AYTransform0Explicit_coeff_5 :
    barrierCase2AYTransform0Explicit.coeff 5 = (barrierCase2AYTransform0Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_6 :
    barrierCase2AYTransform0Explicit.coeff 6 = (barrierCase2AYTransform0Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_7 :
    barrierCase2AYTransform0Explicit.coeff 7 = (barrierCase2AYTransform0Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_8 :
    barrierCase2AYTransform0Explicit.coeff 8 = (barrierCase2AYTransform0Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_9 :
    barrierCase2AYTransform0Explicit.coeff 9 = (barrierCase2AYTransform0Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform0_ratCoeff_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 10 =
      barrierCase2AYTransform0Coefficient 10 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 11 =
      barrierCase2AYTransform0Coefficient 11 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 12 =
      barrierCase2AYTransform0Coefficient 12 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 13 =
      barrierCase2AYTransform0Coefficient 13 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 14 =
      barrierCase2AYTransform0Coefficient 14 := by decide +kernel

theorem barrierCase2AYTransform0Explicit_coeff_10 :
    barrierCase2AYTransform0Explicit.coeff 10 = (barrierCase2AYTransform0Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_11 :
    barrierCase2AYTransform0Explicit.coeff 11 = (barrierCase2AYTransform0Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_12 :
    barrierCase2AYTransform0Explicit.coeff 12 = (barrierCase2AYTransform0Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_13 :
    barrierCase2AYTransform0Explicit.coeff 13 = (barrierCase2AYTransform0Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_14 :
    barrierCase2AYTransform0Explicit.coeff 14 = (barrierCase2AYTransform0Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform0_ratCoeff_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 15 =
      barrierCase2AYTransform0Coefficient 15 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 16 =
      barrierCase2AYTransform0Coefficient 16 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 17 =
      barrierCase2AYTransform0Coefficient 17 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 18 =
      barrierCase2AYTransform0Coefficient 18 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 19 =
      barrierCase2AYTransform0Coefficient 19 := by decide +kernel

theorem barrierCase2AYTransform0Explicit_coeff_15 :
    barrierCase2AYTransform0Explicit.coeff 15 = (barrierCase2AYTransform0Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_16 :
    barrierCase2AYTransform0Explicit.coeff 16 = (barrierCase2AYTransform0Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_17 :
    barrierCase2AYTransform0Explicit.coeff 17 = (barrierCase2AYTransform0Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_18 :
    barrierCase2AYTransform0Explicit.coeff 18 = (barrierCase2AYTransform0Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_19 :
    barrierCase2AYTransform0Explicit.coeff 19 = (barrierCase2AYTransform0Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform0_ratCoeff_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 20 =
      barrierCase2AYTransform0Coefficient 20 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 21 =
      barrierCase2AYTransform0Coefficient 21 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 22 =
      barrierCase2AYTransform0Coefficient 22 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 23 =
      barrierCase2AYTransform0Coefficient 23 := by decide +kernel

theorem barrierCase2AY_transform0_ratCoeff_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) 24 =
      barrierCase2AYTransform0Coefficient 24 := by decide +kernel

theorem barrierCase2AYTransform0Explicit_coeff_20 :
    barrierCase2AYTransform0Explicit.coeff 20 = (barrierCase2AYTransform0Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_21 :
    barrierCase2AYTransform0Explicit.coeff 21 = (barrierCase2AYTransform0Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_22 :
    barrierCase2AYTransform0Explicit.coeff 22 = (barrierCase2AYTransform0Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_23 :
    barrierCase2AYTransform0Explicit.coeff 23 = (barrierCase2AYTransform0Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform0Explicit_coeff_24 :
    barrierCase2AYTransform0Explicit.coeff 24 = (barrierCase2AYTransform0Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform0_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) h.val =
      barrierCase2AYTransform0Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) h =
    barrierCase2AYTransform0Coefficient h
  interval_cases h
  · exact barrierCase2AY_transform0_ratCoeff_0
  · exact barrierCase2AY_transform0_ratCoeff_1
  · exact barrierCase2AY_transform0_ratCoeff_2
  · exact barrierCase2AY_transform0_ratCoeff_3
  · exact barrierCase2AY_transform0_ratCoeff_4
  · exact barrierCase2AY_transform0_ratCoeff_5
  · exact barrierCase2AY_transform0_ratCoeff_6
  · exact barrierCase2AY_transform0_ratCoeff_7
  · exact barrierCase2AY_transform0_ratCoeff_8
  · exact barrierCase2AY_transform0_ratCoeff_9
  · exact barrierCase2AY_transform0_ratCoeff_10
  · exact barrierCase2AY_transform0_ratCoeff_11
  · exact barrierCase2AY_transform0_ratCoeff_12
  · exact barrierCase2AY_transform0_ratCoeff_13
  · exact barrierCase2AY_transform0_ratCoeff_14
  · exact barrierCase2AY_transform0_ratCoeff_15
  · exact barrierCase2AY_transform0_ratCoeff_16
  · exact barrierCase2AY_transform0_ratCoeff_17
  · exact barrierCase2AY_transform0_ratCoeff_18
  · exact barrierCase2AY_transform0_ratCoeff_19
  · exact barrierCase2AY_transform0_ratCoeff_20
  · exact barrierCase2AY_transform0_ratCoeff_21
  · exact barrierCase2AY_transform0_ratCoeff_22
  · exact barrierCase2AY_transform0_ratCoeff_23
  · exact barrierCase2AY_transform0_ratCoeff_24

theorem barrierCase2AYTransform0Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform0Explicit.coeff h = (barrierCase2AYTransform0Coefficient h : ℝ) := by
  interval_cases h
  · exact barrierCase2AYTransform0Explicit_coeff_0
  · exact barrierCase2AYTransform0Explicit_coeff_1
  · exact barrierCase2AYTransform0Explicit_coeff_2
  · exact barrierCase2AYTransform0Explicit_coeff_3
  · exact barrierCase2AYTransform0Explicit_coeff_4
  · exact barrierCase2AYTransform0Explicit_coeff_5
  · exact barrierCase2AYTransform0Explicit_coeff_6
  · exact barrierCase2AYTransform0Explicit_coeff_7
  · exact barrierCase2AYTransform0Explicit_coeff_8
  · exact barrierCase2AYTransform0Explicit_coeff_9
  · exact barrierCase2AYTransform0Explicit_coeff_10
  · exact barrierCase2AYTransform0Explicit_coeff_11
  · exact barrierCase2AYTransform0Explicit_coeff_12
  · exact barrierCase2AYTransform0Explicit_coeff_13
  · exact barrierCase2AYTransform0Explicit_coeff_14
  · exact barrierCase2AYTransform0Explicit_coeff_15
  · exact barrierCase2AYTransform0Explicit_coeff_16
  · exact barrierCase2AYTransform0Explicit_coeff_17
  · exact barrierCase2AYTransform0Explicit_coeff_18
  · exact barrierCase2AYTransform0Explicit_coeff_19
  · exact barrierCase2AYTransform0Explicit_coeff_20
  · exact barrierCase2AYTransform0Explicit_coeff_21
  · exact barrierCase2AYTransform0Explicit_coeff_22
  · exact barrierCase2AYTransform0Explicit_coeff_23
  · exact barrierCase2AYTransform0Explicit_coeff_24

theorem barrierCase2AY_transform0_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (0) (1/4) =
      barrierCase2AYTransform0Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (0) (1/4) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform0_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (0) (1/4) h =
      barrierCase2AYTransform0Coefficient h at hr
    rw [hr] at hc
    have ha : ((0 : ℚ) : ℝ) = (0 : ℝ) := by norm_num
    have hb : ((1/4 : ℚ) : ℝ) = (1/4 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform0Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform0Explicit_natDegree]
    omega

end

noncomputable section

open Polynomial

theorem barrierCase2AY_transform0_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ))
      24 (0) (1/4)).signVariations = 5 := by
  rw [barrierCase2AY_transform0_eq_explicit]
  have hd : barrierCase2AYTransform0Explicit.degree = 24 := by
    unfold barrierCase2AYTransform0Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform0Explicit_coeff, barrierCase2AYTransform0Coefficient,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesY1
namespace OAI

namespace InternalCatalan

section

open Polynomial

theorem barrierCase2AY_transform1_ratCoeff_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 0 =
      barrierCase2AYTransform1Coefficient 0 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 1 =
      barrierCase2AYTransform1Coefficient 1 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 2 =
      barrierCase2AYTransform1Coefficient 2 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 3 =
      barrierCase2AYTransform1Coefficient 3 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 4 =
      barrierCase2AYTransform1Coefficient 4 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_0 :
    barrierCase2AYTransform1Explicit.coeff 0 = (barrierCase2AYTransform1Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_1 :
    barrierCase2AYTransform1Explicit.coeff 1 = (barrierCase2AYTransform1Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_2 :
    barrierCase2AYTransform1Explicit.coeff 2 = (barrierCase2AYTransform1Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_3 :
    barrierCase2AYTransform1Explicit.coeff 3 = (barrierCase2AYTransform1Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_4 :
    barrierCase2AYTransform1Explicit.coeff 4 = (barrierCase2AYTransform1Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 5 =
      barrierCase2AYTransform1Coefficient 5 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 6 =
      barrierCase2AYTransform1Coefficient 6 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 7 =
      barrierCase2AYTransform1Coefficient 7 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 8 =
      barrierCase2AYTransform1Coefficient 8 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 9 =
      barrierCase2AYTransform1Coefficient 9 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_5 :
    barrierCase2AYTransform1Explicit.coeff 5 = (barrierCase2AYTransform1Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_6 :
    barrierCase2AYTransform1Explicit.coeff 6 = (barrierCase2AYTransform1Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_7 :
    barrierCase2AYTransform1Explicit.coeff 7 = (barrierCase2AYTransform1Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_8 :
    barrierCase2AYTransform1Explicit.coeff 8 = (barrierCase2AYTransform1Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_9 :
    barrierCase2AYTransform1Explicit.coeff 9 = (barrierCase2AYTransform1Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 10 =
      barrierCase2AYTransform1Coefficient 10 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 11 =
      barrierCase2AYTransform1Coefficient 11 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 12 =
      barrierCase2AYTransform1Coefficient 12 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 13 =
      barrierCase2AYTransform1Coefficient 13 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 14 =
      barrierCase2AYTransform1Coefficient 14 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_10 :
    barrierCase2AYTransform1Explicit.coeff 10 = (barrierCase2AYTransform1Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_11 :
    barrierCase2AYTransform1Explicit.coeff 11 = (barrierCase2AYTransform1Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_12 :
    barrierCase2AYTransform1Explicit.coeff 12 = (barrierCase2AYTransform1Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_13 :
    barrierCase2AYTransform1Explicit.coeff 13 = (barrierCase2AYTransform1Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_14 :
    barrierCase2AYTransform1Explicit.coeff 14 = (barrierCase2AYTransform1Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 15 =
      barrierCase2AYTransform1Coefficient 15 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 16 =
      barrierCase2AYTransform1Coefficient 16 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 17 =
      barrierCase2AYTransform1Coefficient 17 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 18 =
      barrierCase2AYTransform1Coefficient 18 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 19 =
      barrierCase2AYTransform1Coefficient 19 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_15 :
    barrierCase2AYTransform1Explicit.coeff 15 = (barrierCase2AYTransform1Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_16 :
    barrierCase2AYTransform1Explicit.coeff 16 = (barrierCase2AYTransform1Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_17 :
    barrierCase2AYTransform1Explicit.coeff 17 = (barrierCase2AYTransform1Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_18 :
    barrierCase2AYTransform1Explicit.coeff 18 = (barrierCase2AYTransform1Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_19 :
    barrierCase2AYTransform1Explicit.coeff 19 = (barrierCase2AYTransform1Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 20 =
      barrierCase2AYTransform1Coefficient 20 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 21 =
      barrierCase2AYTransform1Coefficient 21 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 22 =
      barrierCase2AYTransform1Coefficient 22 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 23 =
      barrierCase2AYTransform1Coefficient 23 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 24 =
      barrierCase2AYTransform1Coefficient 24 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_20 :
    barrierCase2AYTransform1Explicit.coeff 20 = (barrierCase2AYTransform1Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_21 :
    barrierCase2AYTransform1Explicit.coeff 21 = (barrierCase2AYTransform1Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_22 :
    barrierCase2AYTransform1Explicit.coeff 22 = (barrierCase2AYTransform1Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_23 :
    barrierCase2AYTransform1Explicit.coeff 23 = (barrierCase2AYTransform1Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_24 :
    barrierCase2AYTransform1Explicit.coeff 24 = (barrierCase2AYTransform1Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) h.val =
      barrierCase2AYTransform1Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) h =
    barrierCase2AYTransform1Coefficient h
  interval_cases h
  · exact barrierCase2AY_transform1_ratCoeff_0
  · exact barrierCase2AY_transform1_ratCoeff_1
  · exact barrierCase2AY_transform1_ratCoeff_2
  · exact barrierCase2AY_transform1_ratCoeff_3
  · exact barrierCase2AY_transform1_ratCoeff_4
  · exact barrierCase2AY_transform1_ratCoeff_5
  · exact barrierCase2AY_transform1_ratCoeff_6
  · exact barrierCase2AY_transform1_ratCoeff_7
  · exact barrierCase2AY_transform1_ratCoeff_8
  · exact barrierCase2AY_transform1_ratCoeff_9
  · exact barrierCase2AY_transform1_ratCoeff_10
  · exact barrierCase2AY_transform1_ratCoeff_11
  · exact barrierCase2AY_transform1_ratCoeff_12
  · exact barrierCase2AY_transform1_ratCoeff_13
  · exact barrierCase2AY_transform1_ratCoeff_14
  · exact barrierCase2AY_transform1_ratCoeff_15
  · exact barrierCase2AY_transform1_ratCoeff_16
  · exact barrierCase2AY_transform1_ratCoeff_17
  · exact barrierCase2AY_transform1_ratCoeff_18
  · exact barrierCase2AY_transform1_ratCoeff_19
  · exact barrierCase2AY_transform1_ratCoeff_20
  · exact barrierCase2AY_transform1_ratCoeff_21
  · exact barrierCase2AY_transform1_ratCoeff_22
  · exact barrierCase2AY_transform1_ratCoeff_23
  · exact barrierCase2AY_transform1_ratCoeff_24

theorem barrierCase2AYTransform1Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform1Explicit.coeff h = (barrierCase2AYTransform1Coefficient h : ℝ) := by
  interval_cases h
  · exact barrierCase2AYTransform1Explicit_coeff_0
  · exact barrierCase2AYTransform1Explicit_coeff_1
  · exact barrierCase2AYTransform1Explicit_coeff_2
  · exact barrierCase2AYTransform1Explicit_coeff_3
  · exact barrierCase2AYTransform1Explicit_coeff_4
  · exact barrierCase2AYTransform1Explicit_coeff_5
  · exact barrierCase2AYTransform1Explicit_coeff_6
  · exact barrierCase2AYTransform1Explicit_coeff_7
  · exact barrierCase2AYTransform1Explicit_coeff_8
  · exact barrierCase2AYTransform1Explicit_coeff_9
  · exact barrierCase2AYTransform1Explicit_coeff_10
  · exact barrierCase2AYTransform1Explicit_coeff_11
  · exact barrierCase2AYTransform1Explicit_coeff_12
  · exact barrierCase2AYTransform1Explicit_coeff_13
  · exact barrierCase2AYTransform1Explicit_coeff_14
  · exact barrierCase2AYTransform1Explicit_coeff_15
  · exact barrierCase2AYTransform1Explicit_coeff_16
  · exact barrierCase2AYTransform1Explicit_coeff_17
  · exact barrierCase2AYTransform1Explicit_coeff_18
  · exact barrierCase2AYTransform1Explicit_coeff_19
  · exact barrierCase2AYTransform1Explicit_coeff_20
  · exact barrierCase2AYTransform1Explicit_coeff_21
  · exact barrierCase2AYTransform1Explicit_coeff_22
  · exact barrierCase2AYTransform1Explicit_coeff_23
  · exact barrierCase2AYTransform1Explicit_coeff_24

theorem barrierCase2AY_transform1_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1/4) (1/2) =
      barrierCase2AYTransform1Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (1/4) (1/2) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform1_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) h =
      barrierCase2AYTransform1Coefficient h at hr
    rw [hr] at hc
    have ha : ((1/4 : ℚ) : ℝ) = (1/4 : ℝ) := by norm_num
    have hb : ((1/2 : ℚ) : ℝ) = (1/2 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform1Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform1Explicit_natDegree]
    omega

end

noncomputable section

open Polynomial

theorem barrierCase2AY_transform1_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ))
      24 (1/4) (1/2)).signVariations = 2 := by
  rw [barrierCase2AY_transform1_eq_explicit]
  have hd : barrierCase2AYTransform1Explicit.degree = 24 := by
    unfold barrierCase2AYTransform1Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform1Explicit_coeff, barrierCase2AYTransform1Coefficient,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesY2Group3
namespace OAI

namespace InternalCatalan

open Polynomial

def barrierCase2AYTransform2Coefficient (h : ℕ) : ℚ :=
  ([-29468567785849371012404257102782431370391111831 / 149011611938476562500000000000000000000000000000000,
    -2977434812495446114353696845638464637307603111527 / 596046447753906250000000000000000000000000000000000,
    -201457815596549216134410784714304450284195247990963 / 3576278686523437500000000000000000000000000000000000,
    -2633510307610809888534437678027934316546694819748733 / 7152557373046875000000000000000000000000000000000000,
    -21072027952584250316974210184493818299292218725433469 / 14305114746093750000000000000000000000000000000000000,
    -14730087874452741619503223044591826241000848978864807 / 4768371582031250000000000000000000000000000000000000,
    1242273293766808109592345866642046367789497834996327 / 596046447753906250000000000000000000000000000000000,
    1622021631381797822212329831968617169963601197771330479 / 38146972656250000000000000000000000000000000000000000,
    13661846168777521797301608174679836037120536570862578189 / 76293945312500000000000000000000000000000000000000000,
    73490645449005696123846325049423163426369696440394564947 / 152587890625000000000000000000000000000000000000000000,
    58152956781182625907456187025931197733855929862941855943 / 61035156250000000000000000000000000000000000000000000,
    41578447392389767044595405690791048242379904737600598033 / 28610229492187500000000000000000000000000000000000000,
    1592940760729225414840314323668190545170664189697713316777 / 915527343750000000000000000000000000000000000000000000,
    6001410973679336559069436793807181638938509189532577759417 / 3662109375000000000000000000000000000000000000000000000,
    2929896215941923617488651331571818408514241932966749238361 / 2441406250000000000000000000000000000000000000000000000,
    1612855803009347594625832102512813729373738622167808378891 / 2441406250000000000000000000000000000000000000000000000,
    304639085906673529980262914720767634069566273788274662699 / 1220703125000000000000000000000000000000000000000000000,
    13160155455391400545735885499903827112656312823070513823 / 305175781250000000000000000000000000000000000000000000,
    -39754224304628931854829845652755777923909753006029865859 / 2441406250000000000000000000000000000000000000000000000,
    -38786440062552273499794450526869737457149272370144558573 / 2441406250000000000000000000000000000000000000000000000,
    -5909563786909702763872399679689333829063402807129830169 / 915527343750000000000000000000000000000000000000000000,
    -1476482497134772048707163571996691407418282748781618819 / 915527343750000000000000000000000000000000000000000000,
    -465752604043612189183612003586479532135529925444062943 / 1831054687500000000000000000000000000000000000000000000,
    -568330377708050253339574534094868438462948592398721 / 24414062500000000000000000000000000000000000000000000,
    -143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000] : List ℚ).getD h 0

noncomputable def barrierCase2AYTransform2Explicit : ℝ[X] :=
  C (-29468567785849371012404257102782431370391111831 / 149011611938476562500000000000000000000000000000000) +
    C (-2977434812495446114353696845638464637307603111527 / 596046447753906250000000000000000000000000000000000) * X ^ 1 +
    C (-201457815596549216134410784714304450284195247990963 / 3576278686523437500000000000000000000000000000000000) * X ^ 2 +
    C (-2633510307610809888534437678027934316546694819748733 / 7152557373046875000000000000000000000000000000000000) * X ^ 3 +
    C (-21072027952584250316974210184493818299292218725433469 / 14305114746093750000000000000000000000000000000000000) * X ^ 4 +
    C (-14730087874452741619503223044591826241000848978864807 / 4768371582031250000000000000000000000000000000000000) * X ^ 5 +
    C (1242273293766808109592345866642046367789497834996327 / 596046447753906250000000000000000000000000000000000) * X ^ 6 +
    C (1622021631381797822212329831968617169963601197771330479 / 38146972656250000000000000000000000000000000000000000) * X ^ 7 +
    C (13661846168777521797301608174679836037120536570862578189 / 76293945312500000000000000000000000000000000000000000) * X ^ 8 +
    C (73490645449005696123846325049423163426369696440394564947 / 152587890625000000000000000000000000000000000000000000) * X ^ 9 +
    C (58152956781182625907456187025931197733855929862941855943 / 61035156250000000000000000000000000000000000000000000) * X ^ 10 +
    C (41578447392389767044595405690791048242379904737600598033 / 28610229492187500000000000000000000000000000000000000) * X ^ 11 +
    C (1592940760729225414840314323668190545170664189697713316777 / 915527343750000000000000000000000000000000000000000000) * X ^ 12 +
    C (6001410973679336559069436793807181638938509189532577759417 / 3662109375000000000000000000000000000000000000000000000) * X ^ 13 +
    C (2929896215941923617488651331571818408514241932966749238361 / 2441406250000000000000000000000000000000000000000000000) * X ^ 14 +
    C (1612855803009347594625832102512813729373738622167808378891 / 2441406250000000000000000000000000000000000000000000000) * X ^ 15 +
    C (304639085906673529980262914720767634069566273788274662699 / 1220703125000000000000000000000000000000000000000000000) * X ^ 16 +
    C (13160155455391400545735885499903827112656312823070513823 / 305175781250000000000000000000000000000000000000000000) * X ^ 17 +
    C (-39754224304628931854829845652755777923909753006029865859 / 2441406250000000000000000000000000000000000000000000000) * X ^ 18 +
    C (-38786440062552273499794450526869737457149272370144558573 / 2441406250000000000000000000000000000000000000000000000) * X ^ 19 +
    C (-5909563786909702763872399679689333829063402807129830169 / 915527343750000000000000000000000000000000000000000000) * X ^ 20 +
    C (-1476482497134772048707163571996691407418282748781618819 / 915527343750000000000000000000000000000000000000000000) * X ^ 21 +
    C (-465752604043612189183612003586479532135529925444062943 / 1831054687500000000000000000000000000000000000000000000) * X ^ 22 +
    C (-568330377708050253339574534094868438462948592398721 / 24414062500000000000000000000000000000000000000000000) * X ^ 23 +
    C (-143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000) * X ^ 24

theorem barrierCase2AYTransform2Explicit_natDegree :
    barrierCase2AYTransform2Explicit.natDegree = 24 := by
  unfold barrierCase2AYTransform2Explicit
  compute_degree!

theorem barrier_case2_AY_transform2_coeff_rat_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 0 =
      barrierCase2AYTransform2Coefficient 0 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 1 =
      barrierCase2AYTransform2Coefficient 1 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 2 =
      barrierCase2AYTransform2Coefficient 2 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 3 =
      barrierCase2AYTransform2Coefficient 3 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 4 =
      barrierCase2AYTransform2Coefficient 4 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_0 :
    barrierCase2AYTransform2Explicit.coeff 0 =
      (barrierCase2AYTransform2Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_1 :
    barrierCase2AYTransform2Explicit.coeff 1 =
      (barrierCase2AYTransform2Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_2 :
    barrierCase2AYTransform2Explicit.coeff 2 =
      (barrierCase2AYTransform2Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_3 :
    barrierCase2AYTransform2Explicit.coeff 3 =
      (barrierCase2AYTransform2Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_4 :
    barrierCase2AYTransform2Explicit.coeff 4 =
      (barrierCase2AYTransform2Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_coeff_rat_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 5 =
      barrierCase2AYTransform2Coefficient 5 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 6 =
      barrierCase2AYTransform2Coefficient 6 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 7 =
      barrierCase2AYTransform2Coefficient 7 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 8 =
      barrierCase2AYTransform2Coefficient 8 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 9 =
      barrierCase2AYTransform2Coefficient 9 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_5 :
    barrierCase2AYTransform2Explicit.coeff 5 =
      (barrierCase2AYTransform2Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_6 :
    barrierCase2AYTransform2Explicit.coeff 6 =
      (barrierCase2AYTransform2Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_7 :
    barrierCase2AYTransform2Explicit.coeff 7 =
      (barrierCase2AYTransform2Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_8 :
    barrierCase2AYTransform2Explicit.coeff 8 =
      (barrierCase2AYTransform2Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_9 :
    barrierCase2AYTransform2Explicit.coeff 9 =
      (barrierCase2AYTransform2Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_coeff_rat_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 10 =
      barrierCase2AYTransform2Coefficient 10 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 11 =
      barrierCase2AYTransform2Coefficient 11 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 12 =
      barrierCase2AYTransform2Coefficient 12 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 13 =
      barrierCase2AYTransform2Coefficient 13 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 14 =
      barrierCase2AYTransform2Coefficient 14 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_10 :
    barrierCase2AYTransform2Explicit.coeff 10 =
      (barrierCase2AYTransform2Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_11 :
    barrierCase2AYTransform2Explicit.coeff 11 =
      (barrierCase2AYTransform2Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_12 :
    barrierCase2AYTransform2Explicit.coeff 12 =
      (barrierCase2AYTransform2Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_13 :
    barrierCase2AYTransform2Explicit.coeff 13 =
      (barrierCase2AYTransform2Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_14 :
    barrierCase2AYTransform2Explicit.coeff 14 =
      (barrierCase2AYTransform2Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_coeff_rat_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 15 =
      barrierCase2AYTransform2Coefficient 15 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 16 =
      barrierCase2AYTransform2Coefficient 16 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 17 =
      barrierCase2AYTransform2Coefficient 17 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 18 =
      barrierCase2AYTransform2Coefficient 18 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 19 =
      barrierCase2AYTransform2Coefficient 19 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_15 :
    barrierCase2AYTransform2Explicit.coeff 15 =
      (barrierCase2AYTransform2Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_16 :
    barrierCase2AYTransform2Explicit.coeff 16 =
      (barrierCase2AYTransform2Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_17 :
    barrierCase2AYTransform2Explicit.coeff 17 =
      (barrierCase2AYTransform2Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_18 :
    barrierCase2AYTransform2Explicit.coeff 18 =
      (barrierCase2AYTransform2Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_19 :
    barrierCase2AYTransform2Explicit.coeff 19 =
      (barrierCase2AYTransform2Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesY2
namespace OAI

namespace InternalCatalan

section

open Polynomial

theorem barrier_case2_AY_transform2_coeff_rat_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 20 =
      barrierCase2AYTransform2Coefficient 20 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 21 =
      barrierCase2AYTransform2Coefficient 21 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 22 =
      barrierCase2AYTransform2Coefficient 22 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 23 =
      barrierCase2AYTransform2Coefficient 23 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 24 =
      barrierCase2AYTransform2Coefficient 24 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_20 :
    barrierCase2AYTransform2Explicit.coeff 20 =
      (barrierCase2AYTransform2Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_21 :
    barrierCase2AYTransform2Explicit.coeff 21 =
      (barrierCase2AYTransform2Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_22 :
    barrierCase2AYTransform2Explicit.coeff 22 =
      (barrierCase2AYTransform2Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_23 :
    barrierCase2AYTransform2Explicit.coeff 23 =
      (barrierCase2AYTransform2Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_24 :
    barrierCase2AYTransform2Explicit.coeff 24 =
      (barrierCase2AYTransform2Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform2_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h.val =
      barrierCase2AYTransform2Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h =
    barrierCase2AYTransform2Coefficient h
  interval_cases h
  · exact barrier_case2_AY_transform2_coeff_rat_0
  · exact barrier_case2_AY_transform2_coeff_rat_1
  · exact barrier_case2_AY_transform2_coeff_rat_2
  · exact barrier_case2_AY_transform2_coeff_rat_3
  · exact barrier_case2_AY_transform2_coeff_rat_4
  · exact barrier_case2_AY_transform2_coeff_rat_5
  · exact barrier_case2_AY_transform2_coeff_rat_6
  · exact barrier_case2_AY_transform2_coeff_rat_7
  · exact barrier_case2_AY_transform2_coeff_rat_8
  · exact barrier_case2_AY_transform2_coeff_rat_9
  · exact barrier_case2_AY_transform2_coeff_rat_10
  · exact barrier_case2_AY_transform2_coeff_rat_11
  · exact barrier_case2_AY_transform2_coeff_rat_12
  · exact barrier_case2_AY_transform2_coeff_rat_13
  · exact barrier_case2_AY_transform2_coeff_rat_14
  · exact barrier_case2_AY_transform2_coeff_rat_15
  · exact barrier_case2_AY_transform2_coeff_rat_16
  · exact barrier_case2_AY_transform2_coeff_rat_17
  · exact barrier_case2_AY_transform2_coeff_rat_18
  · exact barrier_case2_AY_transform2_coeff_rat_19
  · exact barrier_case2_AY_transform2_coeff_rat_20
  · exact barrier_case2_AY_transform2_coeff_rat_21
  · exact barrier_case2_AY_transform2_coeff_rat_22
  · exact barrier_case2_AY_transform2_coeff_rat_23
  · exact barrier_case2_AY_transform2_coeff_rat_24

theorem barrierCase2AYTransform2Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform2Explicit.coeff h =
      (barrierCase2AYTransform2Coefficient h : ℝ) := by
  interval_cases h
  · exact barrier_case2_AY_transform2_explicit_coeff_0
  · exact barrier_case2_AY_transform2_explicit_coeff_1
  · exact barrier_case2_AY_transform2_explicit_coeff_2
  · exact barrier_case2_AY_transform2_explicit_coeff_3
  · exact barrier_case2_AY_transform2_explicit_coeff_4
  · exact barrier_case2_AY_transform2_explicit_coeff_5
  · exact barrier_case2_AY_transform2_explicit_coeff_6
  · exact barrier_case2_AY_transform2_explicit_coeff_7
  · exact barrier_case2_AY_transform2_explicit_coeff_8
  · exact barrier_case2_AY_transform2_explicit_coeff_9
  · exact barrier_case2_AY_transform2_explicit_coeff_10
  · exact barrier_case2_AY_transform2_explicit_coeff_11
  · exact barrier_case2_AY_transform2_explicit_coeff_12
  · exact barrier_case2_AY_transform2_explicit_coeff_13
  · exact barrier_case2_AY_transform2_explicit_coeff_14
  · exact barrier_case2_AY_transform2_explicit_coeff_15
  · exact barrier_case2_AY_transform2_explicit_coeff_16
  · exact barrier_case2_AY_transform2_explicit_coeff_17
  · exact barrier_case2_AY_transform2_explicit_coeff_18
  · exact barrier_case2_AY_transform2_explicit_coeff_19
  · exact barrier_case2_AY_transform2_explicit_coeff_20
  · exact barrier_case2_AY_transform2_explicit_coeff_21
  · exact barrier_case2_AY_transform2_explicit_coeff_22
  · exact barrier_case2_AY_transform2_explicit_coeff_23
  · exact barrier_case2_AY_transform2_explicit_coeff_24

theorem barrierCase2AY_transform2_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4) =
      barrierCase2AYTransform2Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform2_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h =
      barrierCase2AYTransform2Coefficient h at hr
    rw [hr] at hc
    have ha : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
    have hb : ((3 / 4 : ℚ) : ℝ) = (3 / 4 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform2Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform2Explicit_natDegree]
    omega

end

noncomputable section

open Polynomial

theorem barrierCase2AY_transform2_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4)).signVariations =
      2 := by
  rw [barrierCase2AY_transform2_eq_explicit]
  have hd : barrierCase2AYTransform2Explicit.degree = 24 := by
    unfold barrierCase2AYTransform2Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform2Explicit_coeff, barrierCase2AYTransform2Coefficient,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesY3Group3
namespace OAI

namespace InternalCatalan

open Polynomial

def barrierCase2AYTransform3Coefficient (h : ℕ) : ℚ :=
  ([-143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000,
    -13328852305020656769974420328867986569078499453047847 / 610351562500000000000000000000000000000000000000000000,
    -405073511543650819301080934964722549053360065816570661 / 1831054687500000000000000000000000000000000000000000000,
    -1135715502151477029448121480712888010404496946542335209 / 915527343750000000000000000000000000000000000000000000,
    -3425747014757532840387408046604750189100980151421780073 / 915527343750000000000000000000000000000000000000000000,
    -32564922254395114794043131666483789414566624556349199 / 19531250000000000000000000000000000000000000000000000,
    96507491766964192008323381540874751067786163701854775211 / 2441406250000000000000000000000000000000000000000000000,
    2552136099683715674198722117827879481369002003219286563 / 12207031250000000000000000000000000000000000000000000,
    757295683155663124924691968667443065370025938184710453169 / 1220703125000000000000000000000000000000000000000000000,
    3081347631187943503290080929183422725649931198655770031221 / 2441406250000000000000000000000000000000000000000000000,
    894974956378438662157180107167251898953560334080624379907 / 488281250000000000000000000000000000000000000000000000,
    6762715922934768192302940241411982273797805158671382025807 / 3662109375000000000000000000000000000000000000000000000,
    49897915571152220668070685145880004745954607525119213777 / 45776367187500000000000000000000000000000000000000000,
    -8478892304126901706129993081424673920933645530641695947 / 228881835937500000000000000000000000000000000000000000,
    -250883345684911847930727702269439739886830864462697542683 / 305175781250000000000000000000000000000000000000000000,
    -139548911805189759334085179198262041423478654187395622079 / 152587890625000000000000000000000000000000000000000000,
    -42842999955418773787975250759537820647632678736432955307 / 76293945312500000000000000000000000000000000000000000,
    -7677384199066108545301224087264333207407796782438804823 / 38146972656250000000000000000000000000000000000000000,
    -576371618304089744975361850231714547694133029671007137 / 19073486328125000000000000000000000000000000000000000,
    53105118518658103982573517692925793524071100845888027 / 9536743164062500000000000000000000000000000000000000,
    10310494448084278033147754923819461246573435357971077 / 3576278686523437500000000000000000000000000000000000,
    778043333408210218430483767526511181284896861087257 / 3576278686523437500000000000000000000000000000000000,
    -16157727069445508923697447903700348673024154406613 / 447034835815429687500000000000000000000000000000000,
    35186487237831991152495949797694230294009192933 / 74505805969238281250000000000000000000000000000000,
    -427438929851263500756115967545179267 / 372529029846191406250000000000000000000000] : List ℚ).getD h 0

noncomputable def barrierCase2AYTransform3Explicit : ℝ[X] :=
  C (-143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000) +
    C (-13328852305020656769974420328867986569078499453047847 / 610351562500000000000000000000000000000000000000000000) * X ^ 1 +
    C (-405073511543650819301080934964722549053360065816570661 / 1831054687500000000000000000000000000000000000000000000) * X ^ 2 +
    C (-1135715502151477029448121480712888010404496946542335209 / 915527343750000000000000000000000000000000000000000000) * X ^ 3 +
    C (-3425747014757532840387408046604750189100980151421780073 / 915527343750000000000000000000000000000000000000000000) * X ^ 4 +
    C (-32564922254395114794043131666483789414566624556349199 / 19531250000000000000000000000000000000000000000000000) * X ^ 5 +
    C (96507491766964192008323381540874751067786163701854775211 / 2441406250000000000000000000000000000000000000000000000) * X ^ 6 +
    C (2552136099683715674198722117827879481369002003219286563 / 12207031250000000000000000000000000000000000000000000) * X ^ 7 +
    C (757295683155663124924691968667443065370025938184710453169 / 1220703125000000000000000000000000000000000000000000000) * X ^ 8 +
    C (3081347631187943503290080929183422725649931198655770031221 / 2441406250000000000000000000000000000000000000000000000) * X ^ 9 +
    C (894974956378438662157180107167251898953560334080624379907 / 488281250000000000000000000000000000000000000000000000) * X ^ 10 +
    C (6762715922934768192302940241411982273797805158671382025807 / 3662109375000000000000000000000000000000000000000000000) * X ^ 11 +
    C (49897915571152220668070685145880004745954607525119213777 / 45776367187500000000000000000000000000000000000000000) * X ^ 12 +
    C (-8478892304126901706129993081424673920933645530641695947 / 228881835937500000000000000000000000000000000000000000) * X ^ 13 +
    C (-250883345684911847930727702269439739886830864462697542683 / 305175781250000000000000000000000000000000000000000000) * X ^ 14 +
    C (-139548911805189759334085179198262041423478654187395622079 / 152587890625000000000000000000000000000000000000000000) * X ^ 15 +
    C (-42842999955418773787975250759537820647632678736432955307 / 76293945312500000000000000000000000000000000000000000) * X ^ 16 +
    C (-7677384199066108545301224087264333207407796782438804823 / 38146972656250000000000000000000000000000000000000000) * X ^ 17 +
    C (-576371618304089744975361850231714547694133029671007137 / 19073486328125000000000000000000000000000000000000000) * X ^ 18 +
    C (53105118518658103982573517692925793524071100845888027 / 9536743164062500000000000000000000000000000000000000) * X ^ 19 +
    C (10310494448084278033147754923819461246573435357971077 / 3576278686523437500000000000000000000000000000000000) * X ^ 20 +
    C (778043333408210218430483767526511181284896861087257 / 3576278686523437500000000000000000000000000000000000) * X ^ 21 +
    C (-16157727069445508923697447903700348673024154406613 / 447034835815429687500000000000000000000000000000000) * X ^ 22 +
    C (35186487237831991152495949797694230294009192933 / 74505805969238281250000000000000000000000000000000) * X ^ 23 +
    C (-427438929851263500756115967545179267 / 372529029846191406250000000000000000000000) * X ^ 24

theorem barrierCase2AYTransform3Explicit_natDegree :
    barrierCase2AYTransform3Explicit.natDegree = 24 := by
  unfold barrierCase2AYTransform3Explicit
  compute_degree!

theorem barrier_case2_AY_transform3_coeff_rat_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 0 =
      barrierCase2AYTransform3Coefficient 0 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 1 =
      barrierCase2AYTransform3Coefficient 1 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 2 =
      barrierCase2AYTransform3Coefficient 2 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 3 =
      barrierCase2AYTransform3Coefficient 3 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 4 =
      barrierCase2AYTransform3Coefficient 4 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_0 :
    barrierCase2AYTransform3Explicit.coeff 0 =
      (barrierCase2AYTransform3Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_1 :
    barrierCase2AYTransform3Explicit.coeff 1 =
      (barrierCase2AYTransform3Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_2 :
    barrierCase2AYTransform3Explicit.coeff 2 =
      (barrierCase2AYTransform3Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_3 :
    barrierCase2AYTransform3Explicit.coeff 3 =
      (barrierCase2AYTransform3Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_4 :
    barrierCase2AYTransform3Explicit.coeff 4 =
      (barrierCase2AYTransform3Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_coeff_rat_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 5 =
      barrierCase2AYTransform3Coefficient 5 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 6 =
      barrierCase2AYTransform3Coefficient 6 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 7 =
      barrierCase2AYTransform3Coefficient 7 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 8 =
      barrierCase2AYTransform3Coefficient 8 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 9 =
      barrierCase2AYTransform3Coefficient 9 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_5 :
    barrierCase2AYTransform3Explicit.coeff 5 =
      (barrierCase2AYTransform3Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_6 :
    barrierCase2AYTransform3Explicit.coeff 6 =
      (barrierCase2AYTransform3Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_7 :
    barrierCase2AYTransform3Explicit.coeff 7 =
      (barrierCase2AYTransform3Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_8 :
    barrierCase2AYTransform3Explicit.coeff 8 =
      (barrierCase2AYTransform3Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_9 :
    barrierCase2AYTransform3Explicit.coeff 9 =
      (barrierCase2AYTransform3Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_coeff_rat_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 10 =
      barrierCase2AYTransform3Coefficient 10 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 11 =
      barrierCase2AYTransform3Coefficient 11 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 12 =
      barrierCase2AYTransform3Coefficient 12 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 13 =
      barrierCase2AYTransform3Coefficient 13 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 14 =
      barrierCase2AYTransform3Coefficient 14 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_10 :
    barrierCase2AYTransform3Explicit.coeff 10 =
      (barrierCase2AYTransform3Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_11 :
    barrierCase2AYTransform3Explicit.coeff 11 =
      (barrierCase2AYTransform3Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_12 :
    barrierCase2AYTransform3Explicit.coeff 12 =
      (barrierCase2AYTransform3Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_13 :
    barrierCase2AYTransform3Explicit.coeff 13 =
      (barrierCase2AYTransform3Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_14 :
    barrierCase2AYTransform3Explicit.coeff 14 =
      (barrierCase2AYTransform3Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_coeff_rat_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 15 =
      barrierCase2AYTransform3Coefficient 15 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 16 =
      barrierCase2AYTransform3Coefficient 16 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 17 =
      barrierCase2AYTransform3Coefficient 17 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 18 =
      barrierCase2AYTransform3Coefficient 18 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 19 =
      barrierCase2AYTransform3Coefficient 19 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_15 :
    barrierCase2AYTransform3Explicit.coeff 15 =
      (barrierCase2AYTransform3Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_16 :
    barrierCase2AYTransform3Explicit.coeff 16 =
      (barrierCase2AYTransform3Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_17 :
    barrierCase2AYTransform3Explicit.coeff 17 =
      (barrierCase2AYTransform3Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_18 :
    barrierCase2AYTransform3Explicit.coeff 18 =
      (barrierCase2AYTransform3Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_19 :
    barrierCase2AYTransform3Explicit.coeff 19 =
      (barrierCase2AYTransform3Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoYRootSimplicity
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial

theorem barrier_case2_AY_transform3_coeff_rat_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 20 =
      barrierCase2AYTransform3Coefficient 20 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 21 =
      barrierCase2AYTransform3Coefficient 21 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 22 =
      barrierCase2AYTransform3Coefficient 22 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 23 =
      barrierCase2AYTransform3Coefficient 23 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 24 =
      barrierCase2AYTransform3Coefficient 24 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_20 :
    barrierCase2AYTransform3Explicit.coeff 20 =
      (barrierCase2AYTransform3Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_21 :
    barrierCase2AYTransform3Explicit.coeff 21 =
      (barrierCase2AYTransform3Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_22 :
    barrierCase2AYTransform3Explicit.coeff 22 =
      (barrierCase2AYTransform3Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_23 :
    barrierCase2AYTransform3Explicit.coeff 23 =
      (barrierCase2AYTransform3Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_24 :
    barrierCase2AYTransform3Explicit.coeff 24 =
      (barrierCase2AYTransform3Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform3_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) h.val =
      barrierCase2AYTransform3Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) h =
    barrierCase2AYTransform3Coefficient h
  interval_cases h
  · exact barrier_case2_AY_transform3_coeff_rat_0
  · exact barrier_case2_AY_transform3_coeff_rat_1
  · exact barrier_case2_AY_transform3_coeff_rat_2
  · exact barrier_case2_AY_transform3_coeff_rat_3
  · exact barrier_case2_AY_transform3_coeff_rat_4
  · exact barrier_case2_AY_transform3_coeff_rat_5
  · exact barrier_case2_AY_transform3_coeff_rat_6
  · exact barrier_case2_AY_transform3_coeff_rat_7
  · exact barrier_case2_AY_transform3_coeff_rat_8
  · exact barrier_case2_AY_transform3_coeff_rat_9
  · exact barrier_case2_AY_transform3_coeff_rat_10
  · exact barrier_case2_AY_transform3_coeff_rat_11
  · exact barrier_case2_AY_transform3_coeff_rat_12
  · exact barrier_case2_AY_transform3_coeff_rat_13
  · exact barrier_case2_AY_transform3_coeff_rat_14
  · exact barrier_case2_AY_transform3_coeff_rat_15
  · exact barrier_case2_AY_transform3_coeff_rat_16
  · exact barrier_case2_AY_transform3_coeff_rat_17
  · exact barrier_case2_AY_transform3_coeff_rat_18
  · exact barrier_case2_AY_transform3_coeff_rat_19
  · exact barrier_case2_AY_transform3_coeff_rat_20
  · exact barrier_case2_AY_transform3_coeff_rat_21
  · exact barrier_case2_AY_transform3_coeff_rat_22
  · exact barrier_case2_AY_transform3_coeff_rat_23
  · exact barrier_case2_AY_transform3_coeff_rat_24

theorem barrierCase2AYTransform3Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform3Explicit.coeff h =
      (barrierCase2AYTransform3Coefficient h : ℝ) := by
  interval_cases h
  · exact barrier_case2_AY_transform3_explicit_coeff_0
  · exact barrier_case2_AY_transform3_explicit_coeff_1
  · exact barrier_case2_AY_transform3_explicit_coeff_2
  · exact barrier_case2_AY_transform3_explicit_coeff_3
  · exact barrier_case2_AY_transform3_explicit_coeff_4
  · exact barrier_case2_AY_transform3_explicit_coeff_5
  · exact barrier_case2_AY_transform3_explicit_coeff_6
  · exact barrier_case2_AY_transform3_explicit_coeff_7
  · exact barrier_case2_AY_transform3_explicit_coeff_8
  · exact barrier_case2_AY_transform3_explicit_coeff_9
  · exact barrier_case2_AY_transform3_explicit_coeff_10
  · exact barrier_case2_AY_transform3_explicit_coeff_11
  · exact barrier_case2_AY_transform3_explicit_coeff_12
  · exact barrier_case2_AY_transform3_explicit_coeff_13
  · exact barrier_case2_AY_transform3_explicit_coeff_14
  · exact barrier_case2_AY_transform3_explicit_coeff_15
  · exact barrier_case2_AY_transform3_explicit_coeff_16
  · exact barrier_case2_AY_transform3_explicit_coeff_17
  · exact barrier_case2_AY_transform3_explicit_coeff_18
  · exact barrier_case2_AY_transform3_explicit_coeff_19
  · exact barrier_case2_AY_transform3_explicit_coeff_20
  · exact barrier_case2_AY_transform3_explicit_coeff_21
  · exact barrier_case2_AY_transform3_explicit_coeff_22
  · exact barrier_case2_AY_transform3_explicit_coeff_23
  · exact barrier_case2_AY_transform3_explicit_coeff_24

theorem barrierCase2AY_transform3_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1) =
      barrierCase2AYTransform3Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (3 / 4) (1) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform3_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) h =
      barrierCase2AYTransform3Coefficient h at hr
    rw [hr] at hc
    have ha : ((3 / 4 : ℚ) : ℝ) = (3 / 4 : ℝ) := by norm_num
    have hb : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform3Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform3Explicit_natDegree]
    omega

theorem barrierCase2AY_transform3_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1)).signVariations =
      6 := by
  rw [barrierCase2AY_transform3_eq_explicit]
  have hd : barrierCase2AYTransform3Explicit.degree = 24 := by
    unfold barrierCase2AYTransform3Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform3Explicit_coeff, barrierCase2AYTransform3Coefficient,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end

section

theorem barrierCase2AY_bracket_sign_03 :
    barrierCase2AY.eval (barrierBracketLeft (1227250753)) *
      barrierCase2AY.eval (barrierBracketRight (1227250753)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (1227250753)),
    barrierCase2AY_eval_finite (barrierBracketRight (1227250753))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_04 :
    barrierCase2AY.eval (barrierBracketLeft (2149465998)) *
      barrierCase2AY.eval (barrierBracketRight (2149465998)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (2149465998)),
    barrierCase2AY_eval_finite (barrierBracketRight (2149465998))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_05 :
    barrierCase2AY.eval (barrierBracketLeft (3048189112)) *
      barrierCase2AY.eval (barrierBracketRight (3048189112)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (3048189112)),
    barrierCase2AY_eval_finite (barrierBracketRight (3048189112))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_06 :
    barrierCase2AY.eval (barrierBracketLeft (4322699096)) *
      barrierCase2AY.eval (barrierBracketRight (4322699096)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (4322699096)),
    barrierCase2AY_eval_finite (barrierBracketRight (4322699096))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_07 :
    barrierCase2AY.eval (barrierBracketLeft (5564757994)) *
      barrierCase2AY.eval (barrierBracketRight (5564757994)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (5564757994)),
    barrierCase2AY_eval_finite (barrierBracketRight (5564757994))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_08 :
    barrierCase2AY.eval (barrierBracketLeft (6801929373)) *
      barrierCase2AY.eval (barrierBracketRight (6801929373)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (6801929373)),
    barrierCase2AY_eval_finite (barrierBracketRight (6801929373))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_09 :
    barrierCase2AY.eval (barrierBracketLeft (8031988371)) *
      barrierCase2AY.eval (barrierBracketRight (8031988371)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (8031988371)),
    barrierCase2AY_eval_finite (barrierBracketRight (8031988371))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_10 :
    barrierCase2AY.eval (barrierBracketLeft (8877037851)) *
      barrierCase2AY.eval (barrierBracketRight (8877037851)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (8877037851)),
    barrierCase2AY_eval_finite (barrierBracketRight (8877037851))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_11 :
    barrierCase2AY.eval (barrierBracketLeft (9577761832)) *
      barrierCase2AY.eval (barrierBracketRight (9577761832)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9577761832)),
    barrierCase2AY_eval_finite (barrierBracketRight (9577761832))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_12 :
    barrierCase2AY.eval (barrierBracketLeft (9838463999)) *
      barrierCase2AY.eval (barrierBracketRight (9838463999)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9838463999)),
    barrierCase2AY_eval_finite (barrierBracketRight (9838463999))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_13 :
    barrierCase2AY.eval (barrierBracketLeft (9972727815)) *
      barrierCase2AY.eval (barrierBracketRight (9972727815)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9972727815)),
    barrierCase2AY_eval_finite (barrierBracketRight (9972727815))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_14 :
    barrierCase2AY.eval (barrierBracketLeft (9992037196)) *
      barrierCase2AY.eval (barrierBracketRight (9992037196)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9992037196)),
    barrierCase2AY_eval_finite (barrierBracketRight (9992037196))]
  decide +kernel

open Polynomial





theorem barrierCase2AY_bracket_signs (m : ℤ) (hm : m ∈ barrierCase2YBrackets) :
    barrierCase2AY.eval (barrierBracketLeft m) *
      barrierCase2AY.eval (barrierBracketRight m) < 0 := by
  simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact barrierCase2AY_bracket_sign_00
  · exact barrierCase2AY_bracket_sign_01
  · exact barrierCase2AY_bracket_sign_02
  · exact barrierCase2AY_bracket_sign_03
  · exact barrierCase2AY_bracket_sign_04
  · exact barrierCase2AY_bracket_sign_05
  · exact barrierCase2AY_bracket_sign_06
  · exact barrierCase2AY_bracket_sign_07
  · exact barrierCase2AY_bracket_sign_08
  · exact barrierCase2AY_bracket_sign_09
  · exact barrierCase2AY_bracket_sign_10
  · exact barrierCase2AY_bracket_sign_11
  · exact barrierCase2AY_bracket_sign_12
  · exact barrierCase2AY_bracket_sign_13
  · exact barrierCase2AY_bracket_sign_14

theorem barrierCase2Y_bracket_domain (m : ℤ) (hm : m ∈ barrierCase2YBrackets) :
    0 < barrierBracketLeft m ∧
      barrierBracketLeft m < barrierBracketRight m ∧
      barrierBracketRight m < 1 := by
  simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

end


theorem barrierCase2AY_bracket_root (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase2AY
    (barrierCase2Y_bracket_domain m hm).2.1 (barrierCase2AY_bracket_signs m hm)

open Polynomial

private theorem barrierCase2AY_mapped_natDegree_le :
    (barrierCase2AY.map (Rat.castHom ℝ)).natDegree ≤ 24 := by
  calc
    _ ≤ barrierCase2AY.natDegree := Polynomial.natDegree_map_le
    _ = 24 := barrierCase2AY_natDegree

theorem barrierCase2AY_interval0_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) (1 / 4) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 5 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (0) (1 / 4) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform0_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform0_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (0) (1 / 4)
      barrierCase2AY_mapped_natDegree_le hne s hs

theorem barrierCase2AY_interval1_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 2 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 4) (1 / 2) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform1_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 4) (1 / 2)
      barrierCase2AY_mapped_natDegree_le hne s hs

theorem barrierCase2AY_interval2_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 2 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform2_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform2_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4)
      barrierCase2AY_mapped_natDegree_le hne s hs

theorem barrierCase2AY_interval3_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (3 / 4 : ℝ) (1) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 6 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform3_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform3_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1)
      barrierCase2AY_mapped_natDegree_le hne s hs

private theorem barrierCase2AY_map_eval_rat_ne_zero (q : ℚ)
    (hq : barrierCase2AY.eval q ≠ 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).eval (q : ℝ) ≠ 0 := by
  have heval : (barrierCase2AY.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((barrierCase2AY.eval q : ℚ) : ℝ) := by
    change (barrierCase2AY.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (barrierCase2AY.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  rw [heval]
  exact_mod_cast hq

private theorem barrierCase2AY_root_subdivision {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ Set.Ioo (0 : ℝ) (1 / 4) ∨ x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) ∨ x ∈ Set.Ioo (3 / 4 : ℝ) 1 := by
  have hq1 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (1 / 4 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_map_eval_rat_ne_zero (1 / 4)
      barrierCase2AY_quarter_nonzero.1
  have hq2 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_map_eval_rat_ne_zero (1 / 2)
      barrierCase2AY_quarter_nonzero.2.1
  have hq3 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (3 / 4 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_map_eval_rat_ne_zero (3 / 4)
      barrierCase2AY_quarter_nonzero.2.2
  have hn1 : x ≠ (1 / 4 : ℝ) := by
    intro heq
    exact hq1 (by simpa only [heq] using hr)
  have hn2 : x ≠ (1 / 2 : ℝ) := by
    intro heq
    exact hq2 (by simpa only [heq] using hr)
  have hn3 : x ≠ (3 / 4 : ℝ) := by
    intro heq
    exact hq3 (by simpa only [heq] using hr)
  rcases lt_or_gt_of_ne hn1 with hlt1 | hgt1
  · exact Or.inl ⟨hx.1, hlt1⟩
  · rcases lt_or_gt_of_ne hn2 with hlt2 | hgt2
    · exact Or.inr (Or.inl ⟨hgt1, hlt2⟩)
    · rcases lt_or_gt_of_ne hn3 with hlt3 | hgt3
      · exact Or.inr (Or.inr (Or.inl ⟨hgt2, hlt3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hgt3, hx.2⟩))

theorem barrierCase2AY_interval_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 15 := by
  classical
  let s0 := s.filter (fun x => x ∈ Set.Ioo (0 : ℝ) (1 / 4))
  let s1 := s.filter (fun x => x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2))
  let s2 := s.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4))
  let s3 := s.filter (fun x => x ∈ Set.Ioo (3 / 4 : ℝ) 1)
  have h0 : s0.card ≤ 5 := by
    apply barrierCase2AY_interval0_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h1 : s1.card ≤ 2 := by
    apply barrierCase2AY_interval1_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h2 : s2.card ≤ 2 := by
    apply barrierCase2AY_interval2_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h3 : s3.card ≤ 6 := by
    apply barrierCase2AY_interval3_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have hcover : s ⊆ s0 ∪ (s1 ∪ (s2 ∪ s3)) := by
    intro x hx
    have hparts := barrierCase2AY_root_subdivision (hs x hx).1 (hs x hx).2
    simp only [Finset.mem_union]
    rcases hparts with hx0 | hx1 | hx2 | hx3
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hx0⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx1⟩))
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx, hx3⟩)))
  calc
    s.card ≤ (s0 ∪ (s1 ∪ (s2 ∪ s3))).card := Finset.card_le_card hcover
    _ ≤ s0.card + (s1 ∪ (s2 ∪ s3)).card := Finset.card_union_le _ _
    _ ≤ s0.card + (s1.card + (s2 ∪ s3).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ s0.card + (s1.card + (s2.card + s3.card)) :=
      Nat.add_le_add_left (Nat.add_le_add_left (Finset.card_union_le _ _) _) _
    _ ≤ 5 + (2 + (2 + 6)) := Nat.add_le_add h0 (Nat.add_le_add h1 (Nat.add_le_add h2 h3))
    _ = 15 := rfl

private theorem barrierCase2Y_bracket_subset_interval {m : ℤ}
    (hm : m ∈ barrierCase2YBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, _, hb⟩ := barrierCase2Y_bracket_domain m hm
  have ha' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  exact ⟨ha'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase2Y_bracket_separation :
    ∀ m ∈ barrierCase2YBrackets, ∀ n ∈ barrierCase2YBrackets,
      m ≠ n → m + 2 ≤ n ∨ n + 2 ≤ m := by decide +kernel

private theorem barrierBracketRight_le_left_of_separated {m n : ℤ}
    (h : m + 2 ≤ n) :
    (barrierBracketRight m : ℝ) ≤ (barrierBracketLeft n : ℝ) := by
  have hq : barrierBracketRight m ≤ barrierBracketLeft n := by
    unfold barrierBracketRight barrierBracketLeft
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℚ) ≤ 10000000000)
    exact_mod_cast h
  exact_mod_cast hq

private theorem barrierCase2Y_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase2YBrackets) (hn : n ∈ barrierCase2YBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  rcases barrierCase2Y_bracket_separation m hm n hn hmn with hmn' | hnm'
  · have hs := barrierBracketRight_le_left_of_separated hmn'
    exact (not_lt_of_ge hs) (hy.1.trans hx.2)
  · have hs := barrierBracketRight_le_left_of_separated hnm'
    exact (not_lt_of_ge hs) (hx.1.trans hy.2)

private def barrierCase2YChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase2YBrackets then
    Classical.choose (barrierCase2AY_bracket_root m hm)
  else 0

private theorem barrierCase2YChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    barrierCase2YChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval (barrierCase2YChosenRoot m) = 0 := by
  simpa only [barrierCase2YChosenRoot, dif_pos hm] using
    Classical.choose_spec (barrierCase2AY_bracket_root m hm)

private def barrierCase2YChosenRoots : Finset ℝ := by
  classical
  exact barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot

private theorem barrierCase2YChosenRoots_card : barrierCase2YChosenRoots.card = 15 := by
  classical
  have hinj : Set.InjOn barrierCase2YChosenRoot
      (↑barrierCase2YBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase2YBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase2YBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase2Y_brackets_disjoint hm' hn' hmn
      (barrierCase2YChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase2YChosenRoot_spec n hn').1)
  unfold barrierCase2YChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase2YBrackets]

private theorem barrierCase2YChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase2YChosenRoots) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧ (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase2YBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase2YChosenRoot_spec m hm'
  exact ⟨barrierCase2Y_bracket_subset_interval hm' hr.1, hr.2⟩

private theorem barrierCase2AY_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase2YChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase2YChosenRoots).card ≤ 15 := by
    apply barrierCase2AY_interval_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase2YChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase2YChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase2AY_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase2YBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase2AY_root_mem_chosen hx hr
  change x ∈ barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase2YBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase2YChosenRoot_spec m hm').1⟩


open Polynomial














end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
namespace OAI

noncomputable section

namespace InternalCatalan

section





private theorem barrier_case2_v_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)


private theorem barrier_case2_vT_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT barrierV2)
      ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierV2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialT_hasDerivAt_series barrierV2 barrier_trials_abs_summable.2.1
    barrier_trials_weighted_abs_summable.2.1 hx
  have hs := barrierTrial_U_hasSum barrierV2Finite barrierV2Tail
    barrier_case2_v_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq



private theorem barrier_case2_column_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt realEnergyColumnField
      ((7 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr h1.symm
  have hl0 : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hh := (hl0.const_mul (7 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))
  unfold realEnergyColumnField
  apply hh.congr_deriv
  field_simp [h0, ho]
  ring


theorem barrierCase2Y_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt barrierCase2Y (barrierCase2YDerivativeFormula x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans (by norm_num) hx.1, hx.2⟩
  have hh := (barrier_case2_column_hasDerivAt (ne_of_gt hx.1) (ne_of_lt hx.2)).add
    ((barrier_case2_vT_hasDerivAt hx').const_mul (2 : ℝ))
  unfold barrierCase2Y
  apply hh.congr_deriv
  unfold barrierCase2YDerivativeFormula
  rfl

end

section

open Set Filter
open scoped Topology

private theorem barrier2_atBot_add_finite {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  have hb : ∀ᶠ x in l, g x ≤ c + 1 :=
    ((tendsto_order.mp hg).2 (c + 1) (by linarith)).mono (fun _ hx => hx.le)
  exact tendsto_atBot_add_right_of_ge' l (c + 1) hf hb

private theorem barrier2_log_one_sub_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 - x)) (𝓝[<] 1) atBot := by
  have hc : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have ht : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x < 1 at hx
      change 0 < 1 - x
      exact sub_pos.mpr hx
  exact Real.tendsto_log_nhdsGT_zero.comp ht

private theorem barrier2_continuousOn_tendsto_one_left {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := by
  have ht : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝[Icc (-1) 1] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, ?_⟩
    have ha : ∀ᶠ x : ℝ in 𝓝[<] 1, -1 < x :=
      (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [ha, self_mem_nhdsWithin] with x hx hx1
    exact ⟨hx.le, le_of_lt hx1⟩
  exact (hf 1 (by norm_num)).tendsto.comp ht

private theorem barrier2_continuousOn_continuousAt_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) : ContinuousAt f 0 :=
  (hf 0 (by norm_num)).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))



private theorem barrierCase2V2T_continuousOn :
    ContinuousOn (barrierTrialT barrierV2) (Icc (-1 : ℝ) 1) :=
  barrierTrialT_continuousOn barrierV2 barrier_trials_abs_summable.2.1






theorem barrierCase2Y_tendsto_zero_right :
    Tendsto barrierCase2Y (𝓝[>] 0) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 7 / 48)
    Real.tendsto_log_nhdsGT_zero
  have hr : ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      2 * barrierTrialT barrierV2 x) 0 := by
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    exact (hlog.const_mul (1 / 12 : ℝ)).add
      ((barrier2_continuousOn_continuousAt_zero barrierCase2V2T_continuousOn).const_mul 2)
  have hh := barrier2_atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  unfold barrierCase2Y realEnergyColumnField
  ring

theorem barrierCase2Y_tendsto_one_left :
    Tendsto barrierCase2Y (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier2_log_one_sub_tendsto
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  have hr := (hlog.const_mul (7 / 48 : ℝ)).add
    ((barrier2_continuousOn_tendsto_one_left barrierCase2V2T_continuousOn).const_mul 2)
  have hh := barrier2_atBot_add_finite hl hr
  convert hh using 1
  funext x
  unfold barrierCase2Y realEnergyColumnField
  ring




theorem barrierCase2Y_continuousOn :
    ContinuousOn barrierCase2Y (Ioo (0 : ℝ) 1) := by
  intro x hx
  have hlog : ContinuousWithinAt Real.log (Ioo (0 : ℝ) 1) x :=
    (Real.continuousAt_log (ne_of_gt hx.1)).continuousWithinAt
  have hlog1 : ContinuousWithinAt (fun y : ℝ => Real.log (1 - y)) (Ioo 0 1) x :=
    ((continuousAt_const.sub continuousAt_id).log
      (sub_ne_zero.mpr (Ne.symm (ne_of_lt hx.2)))).continuousWithinAt
  have ht : ContinuousWithinAt (barrierTrialT barrierV2) (Ioo (0 : ℝ) 1) x := by
    apply (barrierCase2V2T_continuousOn x ⟨by linarith [hx.1], hx.2.le⟩).mono
    intro y hy
    exact ⟨by linarith [hy.1], hy.2.le⟩
  exact ((hlog.const_mul (7 / 48 : ℝ)).add (hlog1.const_mul (1 / 12 : ℝ))).add
    (ht.const_mul 2)

end

section
open scoped BigOperators











end
section


theorem barrierCase2Y_deriv_eq_zero_iff {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv barrierCase2Y x = 0 ↔ (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  have ha : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩
  have h0 : x ≠ 0 := ne_of_gt hx.1
  have h1 : x ≠ 1 := ne_of_lt hx.2
  rw [(barrierCase2Y_hasDerivAt hx).deriv, Polynomial.eval_map,
    barrierCase2AY_clears_denominator ha h0 h1]
  simp [barrierCase2QY_eval_ne_zero ha h0 h1]

end

section

open scoped ComplexConjugate




end

open Set


theorem barrierCase2Y_le_of_bracket_bounds (M : ℝ)
    (hbr : ∀ m ∈ barrierCase2YBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2Y x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, barrierCase2Y x ≤ M := by
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase2YBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · exact barrierCase2Y_continuousOn
  · exact barrierCase2Y_tendsto_zero_right
  · exact barrierCase2Y_tendsto_one_left
  · intro x hx hd
    exact barrierCase2AY_roots_exhausted hx ((barrierCase2Y_deriv_eq_zero_iff hx).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Set

theorem solution (M : ℝ)
    (hbr : ∀ m ∈ barrierCase2YBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2Y x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, barrierCase2Y x ≤ M := by
  first
  | exact @OAI.InternalCatalan.barrierCase2Y_le_of_bracket_bounds
  | (apply OAI.InternalCatalan.barrierCase2Y_le_of_bracket_bounds <;> assumption)

end
