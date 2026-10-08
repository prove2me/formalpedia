-- Prove2me | solution 1 for OAI.InternalCatalan.determinantRat_prime_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:08:04.227881+00:00
-- url     : https://prove2.me/submissions/6346f8c9-84f9-4406-ad83-bae57152dcdf

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_OAICatalanIrrationality
import Theorems.Thm_OAI_InternalCatalan_fixedMatrix_det_ne_zero_sigma_neg_one
import Theorems.Thm_OAI_InternalCatalan_fixedMatrix_det_ne_zero_sigma_one
import Theorems.Thm_OAI_InternalCatalan_fixedMatrix_det_ne_zero_sigma_zero

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeBlockGathering
namespace OAI


open scoped BigOperators

namespace InternalCatalan

theorem oddPrime_block_residue_sum_gather {R : Type*} [Semiring R]
    {p ell B : ℕ} (hp : 0 < p) (hell : ell < p) (a g : ℕ → R) :
    (∑ i ∈ Finset.range (B * p), if i % p = ell then a i * g (i / p) else 0) =
      ∑ u ∈ Finset.range B, a (u * p + ell) * g u := by
  classical
  have hmod (u : ℕ) : (u * p + ell) % p = ell := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hell]
  have hquot (u : ℕ) : (u * p + ell) / p = u := by
    rw [Nat.mul_comm u p, Nat.mul_add_div hp, Nat.div_eq_of_lt hell, add_zero]
  refine Finset.sum_bij_ne_zero (fun i _ _ => i / p) ?_ ?_ ?_ ?_
  · intro i hi hfi
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr (Finset.mem_range.mp hi))
  · intro i hi hfi j hj hfj heq
    have hir : i % p = ell := by
      by_contra h
      exact hfi (if_neg h)
    have hjr : j % p = ell := by
      by_contra h
      exact hfj (if_neg h)
    have hdi := Nat.mod_add_div i p
    have hdj := Nat.mod_add_div j p
    rw [hir, heq] at hdi
    rw [hjr] at hdj
    omega
  · intro u hu hgu
    have hu' : u < B := Finset.mem_range.mp hu
    have hstep : (u + 1) * p ≤ B * p := Nat.mul_le_mul_right p (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    have hlt : u * p + ell < B * p := by omega
    refine ⟨u * p + ell, Finset.mem_range.mpr hlt, ?_, hquot u⟩
    simpa only [if_pos (hmod u), hquot u] using hgu
  · intro i hi hfi
    have hir : i % p = ell := by
      by_contra h
      exact hfi (if_neg h)
    have heq : i / p * p + ell = i := by
      have h := Nat.mod_add_div i p
      rw [hir] at h
      simpa only [Nat.add_comm, Nat.mul_comm] using h
    rw [if_pos hir, heq]

end InternalCatalan

end OAI

end

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

theorem momentScalar_even (l : ℕ) :
    momentScalar (2 * l) = 2 / (((2 * l + 1 : ℕ) : ℚ) * centralCoeff l) := by
  simp [momentScalar]

theorem momentScalar_odd (l : ℕ) : momentScalar (2 * l + 1) = 0 := by
  simp [momentScalar]



@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl






theorem momentRat_of_le {i j : ℕ} (hji : j ≤ i) :
    momentRat i j = boundaryMinus (i - j) -
      ∑ k ∈ Finset.range j, momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ) := by
  simp [momentRat, hji]

theorem momentRat_of_lt {i j : ℕ} (hij : i < j) :
    momentRat i j = boundaryPlus (j - i) -
      ∑ k ∈ Finset.range i, momentScalar k / ((j - i + k + 1 : ℕ) : ℚ) := by
  simp [momentRat, not_le.mpr hij]

@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]


theorem momentRat_step (i j : ℕ) :
    momentRat i j - momentRat (i + 1) (j + 1) =
      momentScalar i / ((j + 1 : ℕ) : ℚ) := by
  by_cases hji : j ≤ i
  · have hs : j + 1 ≤ i + 1 := by omega
    have hi : i - j + j = i := Nat.sub_add_cancel hji
    rw [momentRat_of_le hji, momentRat_of_le hs]
    simp only [Nat.add_sub_add_right, Finset.sum_range_succ, hi]
    ring
  · have hij : i < j := Nat.lt_of_not_ge hji
    have hs : i + 1 < j + 1 := by omega
    have hj : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt hij)
    rw [momentRat_of_lt hij, momentRat_of_lt hs]
    simp only [Nat.add_sub_add_right, Finset.sum_range_succ, hj]
    ring

def momentRatNegOne (j : ℕ) : ℚ := boundaryPlus (j + 1)

@[simp] theorem momentRatNegOne_eq (j : ℕ) :
    momentRatNegOne j = boundaryPlus (j + 1) := rfl


@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]

theorem harmonicRat_succ (d n : ℕ) :
    harmonicRat d (n + 1) = harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d) := by
  simp [harmonicRat, Finset.sum_range_succ]


@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]

theorem zetaRat_of_ne {i j : ℕ} (hij : i ≠ j) :
    zetaRat i j = (harmonicRat 1 i - harmonicRat 1 j) / ((i : ℚ) - (j : ℚ)) := by
  simp [zetaRat, hij]

theorem zetaRat_symm (i j : ℕ) : zetaRat i j = zetaRat j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · rw [zetaRat_of_ne hij, zetaRat_of_ne (Ne.symm hij)]
    have hcast : (i : ℚ) ≠ (j : ℚ) := fun h => hij (Nat.cast_injective h)
    apply (div_eq_div_iff (sub_ne_zero.mpr hcast) (sub_ne_zero.mpr (Ne.symm hcast))).2
    ring


end

theorem centralCoeff_pos (l : ℕ) : 0 < centralCoeff l := by
  unfold centralCoeff
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos l
  · positivity

theorem centralCoeff_ne_zero (l : ℕ) : centralCoeff l ≠ 0 :=
  ne_of_gt (centralCoeff_pos l)

theorem centralCoeff_step (l : ℕ) :
    ((2 * l + 2 : ℕ) : ℚ) * centralCoeff (l + 1) =
      ((2 * l + 1 : ℕ) : ℚ) * centralCoeff l := by
  have hc : ((l + 1 : ℕ) : ℚ) * (((2 * (l + 1)).choose (l + 1) : ℕ) : ℚ) =
      2 * ((2 * l + 1 : ℕ) : ℚ) * (((2 * l).choose l : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ l
  have hp : (4 : ℚ) ^ l ≠ 0 := pow_ne_zero l (by norm_num)
  unfold centralCoeff
  rw [pow_succ]
  push_cast at hc ⊢
  field_simp
  nlinarith only [hc]

def boundaryFactor (z : ℕ) : ℚ :=
  if z % 2 = 0 then centralCoeff (z / 2)
  else 1 / ((z : ℚ) * centralCoeff ((z - 1) / 2))

theorem boundaryFactor_even (l : ℕ) : boundaryFactor (2 * l) = centralCoeff l := by
  simp [boundaryFactor]

theorem boundaryFactor_odd (l : ℕ) :
    boundaryFactor (2 * l + 1) = 1 / (((2 * l + 1 : ℕ) : ℚ) * centralCoeff l) := by
  simp [boundaryFactor]

@[simp] theorem boundaryFactor_zero : boundaryFactor 0 = 1 := by
  norm_num [boundaryFactor]

@[simp] theorem boundaryFactor_one : boundaryFactor 1 = 1 := by
  norm_num [boundaryFactor]

theorem boundaryFactor_pos (z : ℕ) : 0 < boundaryFactor z := by
  unfold boundaryFactor
  split_ifs with hz
  · exact centralCoeff_pos _
  · have hpos : 0 < z := by omega
    apply div_pos (by norm_num)
    exact mul_pos (by exact_mod_cast hpos) (centralCoeff_pos _)

theorem boundaryFactor_ne_zero (z : ℕ) : boundaryFactor z ≠ 0 :=
  ne_of_gt (boundaryFactor_pos z)

theorem boundaryFactor_step (z : ℕ) :
    ((z + 2 : ℕ) : ℚ) * boundaryFactor (z + 2) =
      ((z + 1 : ℕ) : ℚ) * boundaryFactor z := by
  by_cases hz : z % 2 = 0
  · have heq : z = 2 * (z / 2) := by omega
    generalize z / 2 = l at heq
    subst z
    rw [show 2 * l + 2 = 2 * (l + 1) by omega, boundaryFactor_even,
      boundaryFactor_even]
    convert centralCoeff_step l using 1 <;> push_cast <;> ring
  · have heq : z = 2 * (z / 2) + 1 := by omega
    generalize z / 2 = l at heq
    subst z
    rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      boundaryFactor_odd, boundaryFactor_odd]
    have hl : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hl' : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hc := centralCoeff_step l
    have hc0 := centralCoeff_ne_zero l
    have hc1 := centralCoeff_ne_zero (l + 1)
    push_cast at hc ⊢
    field_simp
    nlinarith only [hc]


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.BoundaryFormulas
namespace OAI


namespace InternalCatalan

open scoped BigOperators

def parityBoundarySum (f : ℕ → ℚ) (u : ℕ) : ℚ :=
  ∑ z ∈ Finset.range (u + 1), if 0 < z ∧ z % 2 = u % 2 then f z else 0

@[simp] theorem parityBoundarySum_zero (f : ℕ → ℚ) : parityBoundarySum f 0 = 0 := by
  simp [parityBoundarySum]

@[simp] theorem parityBoundarySum_one (f : ℕ → ℚ) : parityBoundarySum f 1 = f 1 := by
  simp [parityBoundarySum, Finset.sum_range_succ]

theorem parityBoundarySum_step (f : ℕ → ℚ) (u : ℕ) :
    parityBoundarySum f (u + 2) = parityBoundarySum f u + f (u + 2) := by
  have hp : (u + 2) % 2 = u % 2 := by omega
  have hn : ¬(0 < u + 1 ∧ (u + 1) % 2 = u % 2) := by omega
  have hn' : (u + 1) % 2 ≠ u % 2 := by omega
  have ht : 0 < u + 2 ∧ (u + 2) % 2 = u % 2 := by omega
  unfold parityBoundarySum
  simp_rw [hp]
  rw [show u + 2 + 1 = (u + 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp [hn', ht]

def boundaryPlusWeight (z : ℕ) : ℚ := 2 / ((z : ℚ) ^ 2 * boundaryFactor z)

theorem boundaryPlus_explicit (u : ℕ) :
    boundaryPlus (u + 1) = boundaryFactor u * parityBoundarySum boundaryPlusWeight u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero => norm_num [boundaryPlus, boundaryPlusWeight]
      | succ u =>
        change boundaryPlus (u + 2 + 1) =
          boundaryFactor (u + 2) * parityBoundarySum boundaryPlusWeight (u + 2)
        have hs := boundaryFactor_step u
        have hu : ((u + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        have hf := boundaryFactor_ne_zero (u + 2)
        have hu1 : ((u + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hf0 := boundaryFactor_ne_zero u
        have hr : boundaryFactor (u + 2) =
            ((u + 1 : ℕ) : ℚ) * boundaryFactor u / ((u + 2 : ℕ) : ℚ) := by
          apply (eq_div_iff hu).2
          simpa [mul_comm] using hs
        rw [show u + 2 + 1 = (u + 1) + 2 by omega, boundaryPlus,
          ih u (by omega), parityBoundarySum_step]
        unfold boundaryPlusWeight
        rw [hr]
        field_simp

def boundaryMinusWeight (z : ℕ) : ℚ :=
  if z % 2 = 0 then 2 / ((z : ℚ) ^ 2 * boundaryFactor z ^ 2)
  else 2 / (z : ℚ)

theorem boundaryMinus_increment (d : ℕ) :
    (momentScalar d + momentScalar (d + 1)) /
        (((d + 2 : ℕ) : ℚ) * boundaryFactor (d + 2)) =
      boundaryMinusWeight (d + 2) := by
  by_cases hd : d % 2 = 0
  · have heq : d = 2 * (d / 2) := by omega
    generalize d / 2 = l at heq
    subst d
    rw [momentScalar_even, momentScalar_odd]
    rw [show 2 * l + 2 = 2 * (l + 1) by omega]
    have hp : (2 * (l + 1)) % 2 = 0 := by omega
    rw [boundaryMinusWeight, if_pos hp]
    simp only [boundaryFactor_even, add_zero]
    have hc : ((2 * l + 1 : ℕ) : ℚ) * centralCoeff l =
        ((2 * (l + 1) : ℕ) : ℚ) * centralCoeff (l + 1) := by
      exact (centralCoeff_step l).symm
    rw [hc]
    have hden : ((2 * (l + 1) : ℕ) : ℚ) ≠ 0 := by positivity
    have hfactor := centralCoeff_ne_zero (l + 1)
    field_simp
  · have heq : d = 2 * (d / 2) + 1 := by omega
    generalize d / 2 = l at heq
    subst d
    rw [momentScalar_odd,
      show 2 * l + 1 + 1 = 2 * (l + 1) by omega, momentScalar_even,
      show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega]
    have hp : (2 * (l + 1) + 1) % 2 ≠ 0 := by omega
    simp only [boundaryMinusWeight, if_neg hp, boundaryFactor_odd, zero_add]
    have hden : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hfactor := centralCoeff_ne_zero (l + 1)
    field_simp

theorem boundaryMinus_explicit (u : ℕ) :
    boundaryMinus u = boundaryFactor u * parityBoundarySum boundaryMinusWeight u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero => norm_num [boundaryMinusWeight]
      | succ u =>
        change boundaryMinus (u + 2) =
          boundaryFactor (u + 2) * parityBoundarySum boundaryMinusWeight (u + 2)
        have hu : ((u + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        have hf := boundaryFactor_ne_zero (u + 2)
        have hs := boundaryFactor_step u
        have hw := boundaryMinus_increment u
        have hr : ((u + 1 : ℕ) : ℚ) * boundaryFactor u =
            ((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2) := hs.symm
        have hw' : momentScalar u + momentScalar (u + 1) =
            boundaryMinusWeight (u + 2) *
              (((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2)) :=
          (div_eq_iff (mul_ne_zero hu hf)).mp hw
        rw [boundaryMinus, ih u (by omega), parityBoundarySum_step]
        rw [show ((u + 1 : ℕ) : ℚ) *
              (boundaryFactor u * parityBoundarySum boundaryMinusWeight u) =
            (((u + 1 : ℕ) : ℚ) * boundaryFactor u) *
              parityBoundarySum boundaryMinusWeight u by ring, hr]
        rw [show ((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2) *
                parityBoundarySum boundaryMinusWeight u + momentScalar u + momentScalar (u + 1) =
              ((u + 2 : ℕ) : ℚ) * boundaryFactor (u + 2) *
                parityBoundarySum boundaryMinusWeight u +
                  (momentScalar u + momentScalar (u + 1)) by ring, hw']
        field_simp

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeOddBoundaryValuation
namespace OAI


namespace InternalCatalan



theorem centralBinom_valuation_single_carry {p l : ℕ} (hp : p.Prime)
    (hl : 2 * l < p ^ 2) :
    padicValNat p ((2 * l).choose l) = if p ≤ 2 * (l % p) then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_choose (by omega : l ≤ 2 * l)
    (Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hl)]
  have hI : Finset.Ico 1 2 = {1} := by decide
  simp [hI, Finset.filter_singleton, two_mul]
  split_ifs <;> simp


theorem centralCoeff_odd_prime_valuation (p l : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValRat p (centralCoeff l) = (padicValNat p ((2 * l).choose l) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat_primes hp2]
    norm_num
  have hfour : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow, htwo]
    norm_num
  have hnum : (((2 * l).choose l : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.centralBinom_pos l))
  unfold centralCoeff
  rw [padicValRat.div hnum (pow_ne_zero _ (by norm_num)),
    padicValRat.of_nat, padicValRat.pow, hfour]
  simp

theorem centralCoeff_odd_prime_single_carry {p l : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hl : 2 * l < p ^ 2) :
    padicValRat p (centralCoeff l) = if p ≤ 2 * (l % p) then 1 else 0 := by
  rw [centralCoeff_odd_prime_valuation p l hp hp2,
    centralBinom_valuation_single_carry hp hl]
  split_ifs <;> norm_num


theorem nat_valuation_below_prime_sq {p z : ℕ} (hp : p.Prime)
    (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    padicValNat p z = if z % p = 0 then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hd : z % p = 0
  · rw [if_pos hd]
    have hle := padicValNat_le_nat_log (p := p) z
    have hlog := Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hz
    have hge := one_le_padicValNat_of_dvd hz0 (Nat.dvd_of_mod_eq_zero hd)
    omega
  · rw [if_neg hd]
    exact padicValNat.eq_zero_of_not_dvd (fun h ↦ hd (Nat.mod_eq_zero_of_dvd h))

theorem double_carry_iff_remainder_odd (p l : ℕ) (hp : p % 2 = 1) :
    p ≤ 2 * (l % p) ↔ ((2 * l) % p) % 2 = 1 := by
  have hp0 : 0 < p := by omega
  have hr : l % p < p := Nat.mod_lt l hp0
  rw [← Nat.mul_mod_mod 2 l p]
  by_cases h : p ≤ 2 * (l % p)
  · rw [Nat.mod_eq_sub_mod h,
      Nat.mod_eq_of_lt (show 2 * (l % p) - p < p by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show 2 * (l % p) < p by omega)]
    omega

theorem boundaryFactor_even_odd_prime_valuation {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2) :
    padicValRat p (boundaryFactor z) = if (z % p) % 2 = 1 then 1 else 0 := by
  have hz2 : 2 * (z / 2) = z := by omega
  have hval := centralCoeff_odd_prime_single_carry hp hp2
    (show 2 * (z / 2) < p ^ 2 by omega)
  have hpar := double_carry_iff_remainder_odd p (z / 2)
    (hp.mod_two_eq_one_iff_ne_two.mpr hp2)
  rw [hz2] at hpar
  rw [boundaryFactor, if_pos hzEven, hval]
  simp only [hpar]

theorem boundaryFactor_even_odd_prime_eq_zero {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hrEven : (z % p) % 2 = 0) : padicValRat p (boundaryFactor z) = 0 := by
  rw [boundaryFactor_even_odd_prime_valuation hp hp2 hzEven hz]
  simp [hrEven]

theorem boundaryFactor_even_odd_prime_eq_one {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hrOdd : (z % p) % 2 = 1) : padicValRat p (boundaryFactor z) = 1 := by
  rw [boundaryFactor_even_odd_prime_valuation hp hp2 hzEven hz, if_pos hrOdd]


theorem boundaryFactor_even_mul_odd_prime_valuation {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0)
    (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    padicValRat p ((z : ℚ) * boundaryFactor z) =
      if z % p = 0 ∨ (z % p) % 2 = 1 then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz0
  rw [padicValRat.mul hzq (boundaryFactor_ne_zero z), padicValRat.of_nat,
    nat_valuation_below_prime_sq hp hz0 hz,
    boundaryFactor_even_odd_prime_valuation hp hp2 hzEven hz]
  by_cases hr : z % p = 0 <;> simp [hr]





open scoped BigOperators

theorem harmonicRat_strictMono (d : ℕ) : StrictMono (harmonicRat d) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [harmonicRat_succ]
  exact lt_add_of_pos_right _ (by positivity)

theorem harmonicRat_sub_ne_zero (d : ℕ) {i j : ℕ} (hij : i ≠ j) :
    harmonicRat d i - harmonicRat d j ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact hij ((harmonicRat_strictMono d).injective h)

theorem zetaRat_ne_zero_of_ne {i j : ℕ} (hij : i ≠ j) :
    zetaRat i j ≠ 0 := by
  rw [zetaRat_of_ne hij]
  apply div_ne_zero (harmonicRat_sub_ne_zero 1 hij)
  apply sub_ne_zero.mpr
  intro h
  exact hij (Nat.cast_injective h)

private theorem harmonic_sum_prime_valuation_lower {p : ℕ} [Fact p.Prime]
    {α : Type*} (s : Finset α) (f : α → ℚ)
    (B : ℤ) (hB : B ≤ 0) (hf : ∀ x ∈ s, B ≤ padicValRat p (f x)) :
    B ≤ padicValRat p (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases hz : f a + ∑ x ∈ s, f x = 0
    · simpa [hz] using hB
    · apply le_trans _ (padicValRat.min_le_padicValRat_add hz)
      apply le_min
      · exact hf a (Finset.mem_insert_self a s)
      · exact ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem harmonicRat_prime_sq_lower {p n : ℕ} (hp : p.Prime)
    (hn : n < p ^ 2) (d : ℕ) : -(d : ℤ) ≤ padicValRat p (harmonicRat d n) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold harmonicRat
  apply harmonic_sum_prime_valuation_lower
  · omega
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hval : padicValNat p (k + 1) ≤ 1 := by
      rw [nat_valuation_below_prime_sq hp (by omega) (by omega)]
      split_ifs <;> omega
    have hval' : (padicValNat p (k + 1) : ℤ) ≤ 1 := by exact_mod_cast hval
    simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    have hmul := mul_le_mul_of_nonneg_left hval' (by positivity : 0 ≤ (d : ℤ))
    simpa only [mul_one] using neg_le_neg hmul

private theorem nat_sub_not_dvd_of_mod_ne {p i j : ℕ} (hji : j ≤ i)
    (hres : i % p ≠ j % p) : ¬p ∣ i - j := by
  intro hdiv
  have hzero : (i - j) % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have heq : i = (i - j) + j := by omega
  apply hres
  rw [heq, Nat.add_mod, hzero, zero_add, Nat.mod_mod]

theorem sub_natCast_valuation_of_mod_ne {p i j : ℕ}
    (hres : i % p ≠ j % p) : padicValRat p ((i : ℚ) - (j : ℚ)) = 0 := by
  rcases le_total j i with hji | hij
  · rw [← Nat.cast_sub hji, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (nat_sub_not_dvd_of_mod_ne hji hres)]
    norm_num
  · have heq : (i : ℚ) - (j : ℚ) = -((j - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub hij]
      ring
    rw [heq, padicValRat.neg, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (nat_sub_not_dvd_of_mod_ne hij (Ne.symm hres))]
    norm_num

theorem zetaRat_distinct_residue_valuation_lower {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p ≠ j % p) :
    -1 ≤ padicValRat p (zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  have hij : i ≠ j := fun h => hres (congrArg (fun n => n % p) h)
  have hnum := harmonicRat_sub_ne_zero 1 hij
  have hden : (i : ℚ) - (j : ℚ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hij (Nat.cast_injective h)
  have hival : -1 ≤ padicValRat p (harmonicRat 1 i) := by
    simpa using harmonicRat_prime_sq_lower hp hi 1
  have hjval : -1 ≤ padicValRat p (harmonicRat 1 j) := by
    simpa using harmonicRat_prime_sq_lower hp hj 1
  have hsum := padicValRat.min_le_padicValRat_add (p := p)
    (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
    (by simpa only [sub_eq_add_neg] using hnum)
  rw [← sub_eq_add_neg, padicValRat.neg] at hsum
  rw [zetaRat_of_ne hij, padicValRat.div hnum hden,
    sub_natCast_valuation_of_mod_ne hres, sub_zero]
  exact (le_min hival hjval).trans hsum

theorem zetaRat_distinct_residue_scaled_valuation {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p ≠ j % p) :
    1 ≤ padicValRat p ((p : ℚ) ^ 2 * zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  have hij : i ≠ j := fun h => hres (congrArg (fun n => n % p) h)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul (pow_ne_zero _ hpq) (zetaRat_ne_zero_of_ne hij),
    padicValRat.pow, padicValRat.self hp.one_lt]
  have hz := zetaRat_distinct_residue_valuation_lower hp hi hj hres
  omega

/-- Port note (prove2.me): stands in for `Rat.num_or_den_zero_padicVal` of newer Mathlib. -/
theorem portRat_num_or_den_zero_padicVal {p : ℕ} (q : ℚ) (hp : p.Prime) :
    padicValInt p q.num = 0 ∨ padicValNat p q.den = 0 := by
  by_contra h
  push_neg at h
  have h1 : p ∣ q.num.natAbs :=
    dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr (by simpa [padicValInt] using h.1))
  have h2 : p ∣ q.den := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr h.2)
  have h3 := Nat.dvd_gcd h1 h2
  rw [q.reduced] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem rational_residue_zero_of_positive_valuation {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hv : 0 < padicValRat p q) :
    (q.den : ZMod p) ≠ 0 ∧ (q.num : ZMod p) / (q.den : ZMod p) = 0 := by
  have hnumval : padicValInt p q.num ≠ 0 := by
    rw [padicValRat_def] at hv
    omega
  have hdenval : padicValNat p q.den = 0 :=
    (portRat_num_or_den_zero_padicVal q hp.out).resolve_left hnumval
  have hdnot : ¬p ∣ q.den := by
    intro hdiv
    have hge := one_le_padicValNat_of_dvd q.den_ne_zero hdiv
    omega
  have hnDiv : (p : ℤ) ∣ q.num := by
    by_contra hn
    exact hnumval (padicValInt.eq_zero_of_not_dvd hn)
  have hnzero : (q.num : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod p) p q.num).mpr hnDiv
  refine ⟨?_, ?_⟩
  · exact fun hh => hdnot ((ZMod.natCast_eq_zero_iff q.den p).mp hh)
  · rw [hnzero, zero_div]

theorem zetaRat_distinct_residue_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p ≠ j % p) :
    (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * zetaRat i j).num : ZMod p) /
        (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have h := zetaRat_distinct_residue_scaled_valuation hp.out hi hj hres
  omega

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators







end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem harmonicRat_prime_digit_error (p d n : ℕ) (hp : 0 < p) :
    (p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p) =
      ∑ k ∈ Finset.range n,
        if p ∣ k + 1 then 0 else (p : ℚ) ^ d / (((k + 1 : ℕ) : ℚ) ^ d) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hdiv : p ∣ n + 1
    · have hfactor : n + 1 = p * (n / p + 1) := by
        rw [← Nat.succ_div_of_dvd hdiv]
        exact (Nat.mul_div_cancel' hdiv).symm
      have hfactorq : ((n + 1 : ℕ) : ℚ) = (p : ℚ) * ((n / p + 1 : ℕ) : ℚ) := by
        exact_mod_cast hfactor
      have hq : ((n / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hterm : (p : ℚ) ^ d * (1 / (((n + 1 : ℕ) : ℚ) ^ d)) =
          1 / (((n / p + 1 : ℕ) : ℚ) ^ d) := by
        rw [hfactorq, mul_pow]
        field_simp [hpq, hq]
      rw [harmonicRat_succ, Nat.succ_div_of_dvd hdiv,
        harmonicRat_succ, Finset.sum_range_succ, if_pos hdiv]
      calc
        (p : ℚ) ^ d * (harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d)) -
            (harmonicRat d (n / p) + 1 / (((n / p + 1 : ℕ) : ℚ) ^ d)) =
          ((p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p)) +
            ((p : ℚ) ^ d * (1 / (((n + 1 : ℕ) : ℚ) ^ d)) -
              1 / (((n / p + 1 : ℕ) : ℚ) ^ d)) := by ring
        _ = _ := by rw [ih, hterm]; ring
    · rw [harmonicRat_succ, Nat.succ_div_of_not_dvd hdiv,
        Finset.sum_range_succ, if_neg hdiv]
      calc
        (p : ℚ) ^ d * (harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d)) -
            harmonicRat d (n / p) =
          ((p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p)) +
            (p : ℚ) ^ d / (((n + 1 : ℕ) : ℚ) ^ d) := by ring
        _ = _ := by rw [ih]

private theorem finite_sum_valuation_zero_or_one_le {p : ℕ} [Fact p.Prime]
    (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ k ∈ s, f k = 0 ∨ 1 ≤ padicValRat p (f k)) :
    (∑ k ∈ s, f k) = 0 ∨ 1 ≤ padicValRat p (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have has := hf a (Finset.mem_insert_self a s)
    have hss := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    rcases has with haz | hav
    · simpa only [haz, zero_add] using hss
    · rcases hss with hsz | hsv
      · right
        simpa only [hsz, add_zero] using hav
      · by_cases hzero : f a + ∑ k ∈ s, f k = 0
        · exact Or.inl hzero
        · exact Or.inr ((le_min hav hsv).trans (padicValRat.min_le_padicValRat_add hzero))

theorem harmonicRat_prime_digit_error_valuation {p n d : ℕ}
    (hp : p.Prime) (hd : 0 < d) :
    (p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p) = 0 ∨
      1 ≤ padicValRat p ((p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [harmonicRat_prime_digit_error p d n hp.pos]
  apply finite_sum_valuation_zero_or_one_le
  intro k _
  by_cases hk : p ∣ k + 1
  · exact Or.inl (if_pos hk)
  · right
    rw [if_neg hk]
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hkq : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [padicValRat.div (pow_ne_zero d hpq) (pow_ne_zero d hkq),
      padicValRat.pow, padicValRat.pow, padicValRat.self hp.one_lt,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hk]
    simpa using (show 1 ≤ (d : ℤ) by omega)

end InternalCatalan



namespace InternalCatalan










open scoped BigOperators




end InternalCatalan



namespace InternalCatalan

private theorem prime_sub_valuation_nonneg {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a - b) := by
  by_cases hz : a - b = 0
  · simp [hz]
  · have h := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa only [sub_eq_add_neg] using hz)
    rw [← sub_eq_add_neg, padicValRat.neg] at h
    exact (le_min ha hb).trans h

private theorem prime_sub_valuation_pos_or_zero {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : a = 0 ∨ 1 ≤ padicValRat p a) (hb : b = 0 ∨ 1 ≤ padicValRat p b) :
    a - b = 0 ∨ 1 ≤ padicValRat p (a - b) := by
  by_cases hz : a - b = 0
  · exact Or.inl hz
  · apply Or.inr
    rcases ha with rfl | ha
    · simpa using hb.resolve_left (by intro h; apply hz; simp [h])
    rcases hb with rfl | hb
    · simpa using ha
    have h := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa only [sub_eq_add_neg] using hz)
    rw [← sub_eq_add_neg, padicValRat.neg] at h
    exact (le_min ha hb).trans h

theorem rational_den_ne_zero_of_valuation_nonneg {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hv : 0 ≤ padicValRat p q) : (q.den : ZMod p) ≠ 0 := by
  have hdval : padicValNat p q.den = 0 := by
    rcases portRat_num_or_den_zero_padicVal q hp.out with hn | hd
    · rw [padicValRat_def, hn] at hv
      omega
    · exact hd
  intro hden
  have hdiv := (ZMod.natCast_eq_zero_iff q.den p).mp hden
  have hge := one_le_padicValNat_of_dvd q.den_ne_zero hdiv
  omega

private theorem zero_residue_of_zero_or_positive {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q = 0 ∨ 1 ≤ padicValRat p q) :
    (q.den : ZMod p) ≠ 0 ∧ (q.num : ZMod p) / (q.den : ZMod p) = 0 := by
  rcases hq with rfl | hq
  · norm_num
  · exact rational_residue_zero_of_positive_valuation (by omega)

theorem rational_residue_eq_of_difference {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0)
    (hd : ((a - b).den : ZMod p) ≠ 0)
    (he : ((a - b).num : ZMod p) / ((a - b).den : ZMod p) = 0) :
    (a.num : ZMod p) / (a.den : ZMod p) =
      (b.num : ZMod p) / (b.den : ZMod p) := by
  have hn : ((a - b).num : ZMod p) = 0 := by
    have h := congrArg (fun x : ZMod p => x * ((a - b).den : ZMod p)) he
    simpa only [div_mul_cancel₀ _ hd, zero_mul] using h
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.substr_num_den' a b)
  push_cast at hc
  rw [hn, zero_mul, zero_mul] at hc
  have hc' : (a.num : ZMod p) * (b.den : ZMod p) -
      (b.num : ZMod p) * (a.den : ZMod p) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_right hd
  exact (div_eq_div_iff ha hb).mpr (sub_eq_zero.mp hc')

private theorem zetaRat_prime_sq_lower_of_le {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hji : j ≤ i) : -2 ≤ padicValRat p (zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, padicValRat.neg]
    simpa using harmonicRat_prime_sq_lower hp hi 2
  · have hnum := harmonicRat_sub_ne_zero 1 hij
    have hden : ((i - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show i - j ≠ 0 by omega)
    have hival : -1 ≤ padicValRat p (harmonicRat 1 i) := by
      simpa using harmonicRat_prime_sq_lower hp hi 1
    have hjval : -1 ≤ padicValRat p (harmonicRat 1 j) := by
      simpa using harmonicRat_prime_sq_lower hp (show j < p ^ 2 by omega) 1
    have hsum := padicValRat.min_le_padicValRat_add (p := p)
      (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
      (by simpa only [sub_eq_add_neg] using hnum)
    rw [← sub_eq_add_neg, padicValRat.neg] at hsum
    have hnumval := (le_min hival hjval).trans hsum
    have hdenval : padicValNat p (i - j) ≤ 1 := by
      rw [nat_valuation_below_prime_sq hp (by omega) (by omega)]
      split_ifs <;> omega
    rw [zetaRat_of_ne hij, ← Nat.cast_sub hji, padicValRat.div hnum hden,
      padicValRat.of_nat]
    omega

theorem zetaRat_prime_sq_scaled_valuation_nonneg {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) ^ 2 * zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hz : zetaRat i j = 0
  · simp [hz]
  · have hval : -2 ≤ padicValRat p (zetaRat i j) := by
      rcases le_total j i with hji | hij
      · exact zetaRat_prime_sq_lower_of_le hp hi hji
      · rw [zetaRat_symm]
        exact zetaRat_prime_sq_lower_of_le hp hj hij
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.mul (pow_ne_zero _ hpq) hz, padicValRat.pow,
      padicValRat.self hp.one_lt]
    omega

private theorem quotients_ne_of_residue_eq {p i j : ℕ} (hij : i ≠ j)
    (hres : i % p = j % p) : i / p ≠ j / p := by
  intro hq
  have hi := Nat.mod_add_div i p
  have hj := Nat.mod_add_div j p
  rw [hres, hq] at hi
  exact hij (hi.symm.trans hj)

private theorem sub_eq_prime_mul_quotient_sub {p i j : ℕ}
    (hres : i % p = j % p) :
    (i : ℚ) - (j : ℚ) =
      (p : ℚ) * (((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ)) := by
  have hi : (i : ℚ) = ((i % p : ℕ) : ℚ) + (p : ℚ) * (i / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div i p).symm
  have hj : (j : ℚ) = ((j % p : ℕ) : ℚ) + (p : ℚ) * (j / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div j p).symm
  rw [hi, hj, hres]
  ring

theorem zetaRat_same_residue_error_identity {p i j : ℕ} (hp : p.Prime)
    (hij : i ≠ j) (hres : i % p = j % p) :
    (p : ℚ) ^ 2 * zetaRat i j - zetaRat (i / p) (j / p) =
      ((p * harmonicRat 1 i - harmonicRat 1 (i / p)) -
        (p * harmonicRat 1 j - harmonicRat 1 (j / p))) /
        (((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ)) := by
  have hq := quotients_ne_of_residue_eq hij hres
  have hd : ((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ) ≠ 0 := by
    exact sub_ne_zero.mpr (fun h => hq (Nat.cast_injective h))
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [zetaRat_of_ne hij, zetaRat_of_ne hq, sub_eq_prime_mul_quotient_sub hres]
  field_simp [hpq, hd]
  ring

theorem zetaRat_same_residue_error_valuation {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p = j % p) :
    (p : ℚ) ^ 2 * zetaRat i j - zetaRat (i / p) (j / p) = 0 ∨
      1 ≤ padicValRat p ((p : ℚ) ^ 2 * zetaRat i j - zetaRat (i / p) (j / p)) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, zetaRat_diagonal]
    have heq : (p : ℚ) ^ 2 * -harmonicRat 2 i - -harmonicRat 2 (i / p) =
        -((p : ℚ) ^ 2 * harmonicRat 2 i - harmonicRat 2 (i / p)) := by ring
    rw [heq]
    rcases harmonicRat_prime_digit_error_valuation (n := i) hp (by decide : 0 < 2) with hz | hv
    · exact Or.inl (by simp [hz])
    · exact Or.inr (by simpa only [padicValRat.neg] using hv)
  · rw [zetaRat_same_residue_error_identity hp hij hres]
    have hei : (p * harmonicRat 1 i - harmonicRat 1 (i / p) : ℚ) = 0 ∨
        1 ≤ padicValRat p (p * harmonicRat 1 i - harmonicRat 1 (i / p)) := by
      simpa only [pow_one] using
        harmonicRat_prime_digit_error_valuation (n := i) hp (by decide : 0 < 1)
    have hej : (p * harmonicRat 1 j - harmonicRat 1 (j / p) : ℚ) = 0 ∨
        1 ≤ padicValRat p (p * harmonicRat 1 j - harmonicRat 1 (j / p)) := by
      simpa only [pow_one] using
        harmonicRat_prime_digit_error_valuation (n := j) hp (by decide : 0 < 1)
    have hq := quotients_ne_of_residue_eq hij hres
    have hiq : i / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using hi)
    have hjq : j / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using hj)
    have hd : ((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ) ≠ 0 := by
      exact sub_ne_zero.mpr (fun h => hq (Nat.cast_injective h))
    have hqres : (i / p) % p ≠ (j / p) % p := by
      simpa only [Nat.mod_eq_of_lt hiq, Nat.mod_eq_of_lt hjq] using hq
    have hdval := sub_natCast_valuation_of_mod_ne hqres
    rcases prime_sub_valuation_pos_or_zero hei hej with hz | hv
    · exact Or.inl (by rw [hz, zero_div])
    · apply Or.inr
      have hn : (p * harmonicRat 1 i - harmonicRat 1 (i / p)) -
          (p * harmonicRat 1 j - harmonicRat 1 (j / p)) ≠ 0 := by
        intro h
        rw [h, padicValRat.zero] at hv
        omega
      rw [padicValRat.div hn hd, hdval, sub_zero]
      exact hv

theorem zetaRat_same_residue_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p = j % p) :
    (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) ≠ 0 ∧
      ((zetaRat (i / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * zetaRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) =
            ((zetaRat (i / p) (j / p)).num : ZMod p) /
              ((zetaRat (i / p) (j / p)).den : ZMod p) := by
  let a : ℚ := (p : ℚ) ^ 2 * zetaRat i j
  let b : ℚ := zetaRat (i / p) (j / p)
  have ha : 0 ≤ padicValRat p a := zetaRat_prime_sq_scaled_valuation_nonneg hp.out hi hj
  have he : a - b = 0 ∨ 1 ≤ padicValRat p (a - b) :=
    zetaRat_same_residue_error_valuation hp.out hi hj hres
  have heval : 0 ≤ padicValRat p (a - b) := by
    rcases he with hz | hv
    · simp [hz]
    · omega
  have hb : 0 ≤ padicValRat p b := by
    have h := prime_sub_valuation_nonneg ha heval
    have heq : a - (a - b) = b := by ring
    rwa [heq] at h
  have haden := rational_den_ne_zero_of_valuation_nonneg ha
  have hbden := rational_den_ne_zero_of_valuation_nonneg hb
  have heloc := zero_residue_of_zero_or_positive he
  exact ⟨haden, hbden, rational_residue_eq_of_difference haden hbden heloc.1 heloc.2⟩

theorem zetaRat_prime_digit_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hi : i < p ^ 2) (hj : j < p ^ 2) :
    (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * zetaRat i j).num : ZMod p) /
        (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) =
          if i % p = j % p then
            ((zetaRat (i / p) (j / p)).num : ZMod p) /
              ((zetaRat (i / p) (j / p)).den : ZMod p)
          else 0 := by
  by_cases hres : i % p = j % p
  · rw [if_pos hres]
    have h := zetaRat_same_residue_reduction hi hj hres
    exact ⟨h.1, h.2.2⟩
  · rw [if_neg hres]
    exact zetaRat_distinct_residue_reduction hi hj hres





theorem boundaryFactor_odd_prime_valuation {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    padicValRat p (boundaryFactor z) = if (z % p) % 2 = 0 then -1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzpos : 0 < z := by omega
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hzpos)
  have hprev : (z - 1) % 2 = 0 := by omega
  have hprevfac : boundaryFactor (z - 1) = centralCoeff ((z - 1) / 2) := by
    rw [boundaryFactor, if_pos hprev]
  have hc : padicValRat p (centralCoeff ((z - 1) / 2)) =
      if ((z - 1) % p) % 2 = 1 then 1 else 0 := by
    rw [← hprevfac]
    exact boundaryFactor_even_odd_prime_valuation hp hp2 hprev (by omega)
  rw [boundaryFactor, if_neg (by omega : z % 2 ≠ 0), one_div,
    padicValRat.inv, padicValRat.mul hzq (centralCoeff_ne_zero _),
    padicValRat.of_nat, nat_valuation_below_prime_sq hp (by omega) hz, hc]
  have hpOdd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hslt : (z - 1) % p < p := Nat.mod_lt _ hp.pos
  have hsucc : z - 1 + 1 = z := by omega
  have hmod := Nat.add_mod (z - 1) 1 p
  rw [hsucc, Nat.mod_eq_of_lt hp.one_lt] at hmod
  by_cases hlast : (z - 1) % p + 1 = p
  · rw [hlast, Nat.mod_self] at hmod
    have hsEven : ((z - 1) % p) % 2 = 0 := by omega
    simp [hmod, hsEven]
  · rw [Nat.mod_eq_of_lt (show (z - 1) % p + 1 < p by omega)] at hmod
    split_ifs <;> omega

theorem boundaryFactor_odd_inverse_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    0 ≤ padicValRat p (1 / boundaryFactor z) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [one_div, padicValRat.inv, boundaryFactor_odd_prime_valuation hp hp2 hzOdd hz]
  split_ifs <;> norm_num

theorem boundaryFactor_odd_scaled_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) * boundaryFactor z) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul hpq (boundaryFactor_ne_zero z), padicValRat.self hp.one_lt,
    boundaryFactor_odd_prime_valuation hp hp2 hzOdd hz]
  split_ifs <;> norm_num

theorem boundaryFactor_odd_integral_denominators {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    ((1 / boundaryFactor z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * boundaryFactor z).den : ZMod p) ≠ 0 := by
  exact ⟨rational_den_ne_zero_of_valuation_nonneg
      (boundaryFactor_odd_inverse_valuation_nonneg hp.out hp2 hzOdd hz),
    rational_den_ne_zero_of_valuation_nonneg
      (boundaryFactor_odd_scaled_valuation_nonneg hp.out hp2 hzOdd hz)⟩

theorem boundaryFactor_odd_odd_remainder_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2)
    (hrOdd : (z % p) % 2 = 1) :
    (((p : ℚ) * boundaryFactor z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * boundaryFactor z).num : ZMod p) /
        (((p : ℚ) * boundaryFactor z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicValRat.mul hpq (boundaryFactor_ne_zero z), padicValRat.self hp.out.one_lt,
    boundaryFactor_odd_prime_valuation hp.out hp2 hzOdd hz]
  norm_num [hrOdd]

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeWeight
namespace OAI


open scoped BigOperators Polynomial

noncomputable section

namespace InternalCatalan

open Polynomial

def oddPrimeWeight (p : ℕ) : (ZMod p)[X] := (1 - X ^ 2) ^ ((p - 1) / 2)

private theorem one_sub_X_sq_pow_expansion (R : Type*) [CommRing R] (s : ℕ) :
    (1 - X ^ 2 : R[X]) ^ s =
      ∑ k ∈ Finset.range (s + 1),
        C ((-1 : R) ^ k * (s.choose k : R)) * X ^ (2 * k) := by
  calc
    (1 - X ^ 2 : R[X]) ^ s = (-X ^ 2 + 1) ^ s := by congr 1; ring
    _ = ∑ k ∈ Finset.range (s + 1),
        (-X ^ 2 : R[X]) ^ k * 1 ^ (s - k) * (s.choose k : R[X]) :=
      add_pow (-X ^ 2 : R[X]) 1 s
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [neg_pow, ← pow_mul]
      simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, C_eq_natCast]
      ring

private theorem one_sub_X_sq_pow_coeff_even (R : Type*) [CommRing R] (s k : ℕ) :
    ((1 - X ^ 2 : R[X]) ^ s).coeff (2 * k) = (-1 : R) ^ k * (s.choose k : R) := by
  rw [one_sub_X_sq_pow_expansion, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    have hne : 2 * k ≠ 2 * j := by omega
    simp [hne]
  · intro hk
    have hsk : s < k := by
      simp only [Finset.mem_range] at hk
      omega
    simp [Nat.choose_eq_zero_of_lt hsk]

private theorem one_sub_X_sq_pow_coeff_odd (R : Type*) [CommRing R] (s d : ℕ)
    (hd : d % 2 ≠ 0) : ((1 - X ^ 2 : R[X]) ^ s).coeff d = 0 := by
  rw [one_sub_X_sq_pow_expansion, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [coeff_C_mul_X_pow]
  have hne : d ≠ 2 * k := by omega
  simp [hne]

theorem oddPrimeWeight_coeff_even (p k : ℕ) :
    (oddPrimeWeight p).coeff (2 * k) =
      (-1 : ZMod p) ^ k * (((p - 1) / 2).choose k : ZMod p) :=
  one_sub_X_sq_pow_coeff_even (ZMod p) ((p - 1) / 2) k

theorem oddPrimeWeight_coeff_odd (p d : ℕ) (hd : d % 2 ≠ 0) :
    (oddPrimeWeight p).coeff d = 0 :=
  one_sub_X_sq_pow_coeff_odd (ZMod p) ((p - 1) / 2) d hd

theorem oddPrimeWeight_coeff_eq_zero_of_ge {p d : ℕ} (hp : 0 < p) (hd : p ≤ d) :
    (oddPrimeWeight p).coeff d = 0 := by
  by_cases he : d % 2 = 0
  · have heq : d = 2 * (d / 2) := by omega
    rw [heq, oddPrimeWeight_coeff_even]
    have hlt : (p - 1) / 2 < d / 2 := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  · exact oddPrimeWeight_coeff_odd p d he

private theorem one_sub_X_sq_pow_coeff_reverse (R : Type*) [CommRing R] (s d : ℕ)
    (hd : d ≤ 2 * s) :
    ((1 - X ^ 2 : R[X]) ^ s).coeff (2 * s - d) =
      (-1 : R) ^ s * ((1 - X ^ 2 : R[X]) ^ s).coeff d := by
  by_cases he : d % 2 = 0
  · have hd2 : d = 2 * (d / 2) := by omega
    generalize d / 2 = k at hd2
    subst d
    have hk : k ≤ s := by omega
    have hr : 2 * s - 2 * k = 2 * (s - k) := by omega
    rw [hr, one_sub_X_sq_pow_coeff_even, one_sub_X_sq_pow_coeff_even,
      Nat.choose_symm hk]
    have hprod : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
      rw [← mul_pow]
      simp
    have hsign : (-1 : R) ^ (s - k) = (-1 : R) ^ s * (-1 : R) ^ k := by
      calc
        (-1 : R) ^ (s - k) =
            (-1 : R) ^ (s - k) * ((-1 : R) ^ k * (-1 : R) ^ k) := by
          rw [hprod, mul_one]
        _ = ((-1 : R) ^ (s - k) * (-1 : R) ^ k) * (-1 : R) ^ k := by ring
        _ = (-1 : R) ^ s * (-1 : R) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hsign]
    ring
  · have hr : (2 * s - d) % 2 ≠ 0 := by omega
    rw [one_sub_X_sq_pow_coeff_odd R s (2 * s - d) hr,
      one_sub_X_sq_pow_coeff_odd R s d he, mul_zero]

theorem oddPrimeWeight_coeff_reverse {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : d < p) :
    (oddPrimeWeight p).coeff (p - 1 - d) =
      (-1 : ZMod p) ^ ((p - 1) / 2) * (oddPrimeWeight p).coeff d := by
  have hodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hdeg : 2 * ((p - 1) / 2) = p - 1 := by omega
  simpa only [oddPrimeWeight, hdeg] using
    one_sub_X_sq_pow_coeff_reverse (ZMod p) ((p - 1) / 2) d (by omega)

theorem oddPrimeWeight_four_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    rcases (Nat.dvd_prime Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz) with h | h
    · exact hp.ne_one h
    · exact hp2 h
  rw [show (4 : ZMod p) = (2 : ZMod p) * 2 by norm_num]
  exact mul_ne_zero htwo htwo

theorem oddPrimeWeight_four_pow_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : ℕ) : (4 : ZMod p) ^ k ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  exact pow_ne_zero _ (oddPrimeWeight_four_ne_zero hp hp2)

theorem oddPrimeWeight_centralCoeff_mul_identity {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 * k < p) :
    (-1 : ZMod p) ^ k * (((p - 1) / 2).choose k : ZMod p) * 4 ^ k =
      (Nat.centralBinom k : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  let m : ℕ := (p - 1) / 2
  have hm : 2 * m + 1 = p := by
    have hodd := hp.eq_two_or_odd.resolve_left hp2
    have hpos := hp.two_le
    dsimp [m]
    omega
  have hmcast : 2 * (m : ZMod p) + 1 = 0 := by
    have hh := congrArg (fun a : ℕ ↦ (a : ZMod p)) hm
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_self] using hh
  change (-1 : ZMod p) ^ k * (m.choose k : ZMod p) * 4 ^ k = _
  revert hk
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    have hkm : k ≤ m := by omega
    have hkprev : 2 * k < p := by omega
    have hknz : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hz
      have hdiv := (ZMod.natCast_eq_zero_iff (k + 1) p).mp hz
      have hle := Nat.le_of_dvd (by omega : 0 < k + 1) hdiv
      omega
    have hchoose :
        (m.choose (k + 1) : ZMod p) * ((k : ZMod p) + 1) =
          (m.choose k : ZMod p) * ((m : ZMod p) - k) := by
      have hh := congrArg (fun a : ℕ ↦ (a : ZMod p))
        (Nat.choose_succ_right_eq m k)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hkm] using hh
    have hcentral :
        (((k + 1 : ℕ) : ZMod p)) * (Nat.centralBinom (k + 1) : ZMod p) =
          2 * (2 * (k : ZMod p) + 1) * (Nat.centralBinom k : ZMod p) := by
      have hh := congrArg (fun a : ℕ ↦ (a : ZMod p))
        (Nat.succ_mul_centralBinom_succ k)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hh
    have hfactor : (-4 : ZMod p) * ((m : ZMod p) - k) =
        2 * (2 * (k : ZMod p) + 1) := by
      linear_combination -2 * hmcast
    apply mul_left_cancel₀ hknz
    calc
      (((k + 1 : ℕ) : ZMod p)) *
          ((-1 : ZMod p) ^ (k + 1) * (m.choose (k + 1) : ZMod p) * 4 ^ (k + 1)) =
          (-1 : ZMod p) ^ k * 4 ^ k * (-4) *
            ((m.choose (k + 1) : ZMod p) * ((k : ZMod p) + 1)) := by
              simp only [Nat.cast_add, Nat.cast_one, pow_succ]
              ring
      _ = (-1 : ZMod p) ^ k * 4 ^ k * (-4) *
          ((m.choose k : ZMod p) * ((m : ZMod p) - k)) := by rw [hchoose]
      _ = ((-4 : ZMod p) * ((m : ZMod p) - k)) *
          ((-1 : ZMod p) ^ k * (m.choose k : ZMod p) * 4 ^ k) := by ring
      _ = 2 * (2 * (k : ZMod p) + 1) * (Nat.centralBinom k : ZMod p) := by
        rw [hfactor, ih hkprev]
      _ = (((k + 1 : ℕ) : ZMod p)) * (Nat.centralBinom (k + 1) : ZMod p) :=
        hcentral.symm

theorem oddPrimeWeight_centralCoeff_identity {p k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 * k < p) :
    (-1 : ZMod p) ^ k * (((p - 1) / 2).choose k : ZMod p) =
      ((2 * k).choose k : ZMod p) / (4 : ZMod p) ^ k := by
  apply (eq_div_iff (oddPrimeWeight_four_pow_ne_zero hp.out hp2 k)).2
  exact oddPrimeWeight_centralCoeff_mul_identity hp.out hp2 hk


theorem oddPrimeWeight_coeff_central {p k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 * k < p) :
    (oddPrimeWeight p).coeff (2 * k) =
      ((2 * k).choose k : ZMod p) / (4 : ZMod p) ^ k := by
  rw [oddPrimeWeight_coeff_even]
  exact oddPrimeWeight_centralCoeff_identity hp2 hk


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicQuadratic
namespace OAI

namespace InternalCatalan

section

def L (N : ℕ) : ℕ := 59 * N
def A (N : ℕ) : ℕ := 19 * N



theorem L_eq_n_add_b_add_q (N : ℕ) : L N = n N + b N + q N := by
  unfold L n b q
  omega




theorem Cdegree_pos {N : ℕ} (hN : 0 < N) : 0 < Cdegree N := by
  unfold Cdegree
  omega

theorem rawColumn_lt_L {N k v : ℕ} (hk : k < n N) (hv : v ≤ q N) :
    b N + k + v < L N := by
  rw [L_eq_n_add_b_add_q]
  omega


theorem rowDistance_le {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r ≤ n N - 1 - g N := by
  unfold rowDistance rowOffset n g at *
  omega

theorem rowDistance_lt_Cdegree {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r < Cdegree N := by
  have hd := rowDistance_le hN hr
  unfold n g Cdegree at *
  omega











end

noncomputable section
open Set
open scoped BigOperators



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

theorem reversedRow_coeff (C : ℕ) (F : ℤ[X]) (i : ℕ) :
    (reversedRow C F).coeff i = if i < C then F.coeff (C - 1 - i) else 0 := by
  classical
  unfold reversedRow
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hi : i < C
  · rw [if_pos hi, Finset.sum_eq_single (C - 1 - i)]
    · rw [if_pos (by omega : i = C - 1 - (C - 1 - i))]
    · intro u hu hne
      have hu' := Finset.mem_range.mp hu
      rw [if_neg (by omega : i ≠ C - 1 - u)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [if_neg (by omega : i ≠ C - 1 - u)]

theorem reversedRow_coeff_eq_zero_of_ge (C : ℕ) (F : ℤ[X])
    {i : ℕ} (hi : C ≤ i) : (reversedRow C F).coeff i = 0 := by
  rw [reversedRow_coeff, if_neg (by omega)]

theorem reversedRow_natDegree_le (C : ℕ) (F : ℤ[X]) :
    (reversedRow C F).natDegree ≤ C - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply reversedRow_coeff_eq_zero_of_ge
  omega



theorem natDegree_one_sub_X : (1 - X : ℤ[X]).natDegree = 1 := by
  rw [Polynomial.natDegree_sub]
  simpa using (Polynomial.natDegree_X_sub_C (1 : ℤ))

theorem rowFactor_natDegree_le (N : ℕ) :
    ((1 - X : ℤ[X]) ^ h N).natDegree ≤ h N := by
  calc
    _ ≤ h N * (1 - X : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
    _ = h N := by rw [InternalCatalan.natDegree_one_sub_X, mul_one]

theorem rowP_natDegree_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (rowP N r).natDegree ≤ H N - 1 := by
  unfold rowP
  calc
    _ ≤ ((1 - X : ℤ[X]) ^ h N).natDegree +
        (reversedRow (Cdegree N) (Chebyshev.T ℤ (rowDistance N r : ℤ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ h N + (Cdegree N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le N) (reversedRow_natDegree_le _ _)
    _ ≤ H N - 1 := by unfold h Cdegree H; omega





theorem rowP_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowP N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowP_natDegree_le hN r
  have hH : 0 < H N := by unfold H; omega
  omega






















end

section

open scoped BigOperators






theorem rawEntryRat_zero (N r j : ℕ) :
    rawEntryRat 0 N r j =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) * momentRat i j) -
      (3 / 2 : ℚ) *
        ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j := by
  simp [rawEntryRat]

def rawCatalanCoeffRat (N r j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (H N),
    ((rowP N r).coeff i : ℚ) * (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))

theorem rawEntryRat_affine (z : ℚ) (N r j : ℕ) :
    rawEntryRat z N r j = rawEntryRat 0 N r j + z * rawCatalanCoeffRat N r j := by
  unfold rawEntryRat rawCatalanCoeffRat
  simp only [mul_zero, zero_mul, add_zero]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) *
        (4 * z * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) =
      ∑ i ∈ Finset.range (H N), z *
        (((rowP N r).coeff i : ℚ) * (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, ← Finset.mul_sum]
  ring

end

section

open Polynomial





theorem polynomial_support_subset_range {F : ℤ[X]} {C : ℕ}
    (hF : F.natDegree < C) : F.support ⊆ Finset.range C := by
  intro i hi
  apply Finset.mem_range.mpr
  exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hi)) hF


variable {K : Type*} [Field K]

theorem reversedRow_eval₂ (f : ℤ →+* K) {C : ℕ} {F : ℤ[X]}
    (hF : F.natDegree < C) {x : K} (hx : x ≠ 0) :
    (reversedRow C F).eval₂ f x = x ^ (C - 1) * F.eval₂ f x⁻¹ := by
  classical
  have hev : F.eval₂ f x⁻¹ =
      ∑ u ∈ Finset.range C, f (F.coeff u) * (x⁻¹) ^ u := by
    rw [eval₂_eq_sum]
    exact sum_eq_of_subset (fun u a => f a * (x⁻¹) ^ u)
      (by intro u; simp) (polynomial_support_subset_range hF)
  rw [hev, Finset.mul_sum]
  unfold reversedRow
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  have hpow : x ^ (C - 1) = x ^ (C - 1 - u) * x ^ u := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, inv_pow]
  field_simp [hx]



end

open Polynomial



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeFilterDigits
namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem prime_add_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a + b) := by
  by_cases h : a + b = 0
  · simp [h]
  · exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add h)

private theorem prime_sub_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a - b) := by
  rw [sub_eq_add_neg]
  exact prime_add_integral ha (by simpa only [padicValRat.neg] using hb)

private theorem prime_mul_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a * b) := by
  by_cases hza : a = 0
  · simp [hza]
  by_cases hzb : b = 0
  · simp [hzb]
  rw [padicValRat.mul hza hzb]
  omega

private theorem prime_div_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : padicValRat p b = 0) (hb0 : b ≠ 0) :
    0 ≤ padicValRat p (a / b) := by
  by_cases hz : a = 0
  · simp [hz]
  rw [padicValRat.div hz hb0, hb, sub_zero]
  exact ha

private theorem prime_sum_integral {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (hf : ∀ a ∈ s, 0 ≤ padicValRat p (f a)) :
    0 ≤ padicValRat p (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact prime_add_integral (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

private theorem prime_nat_den_valuation {p k : ℕ} (hk0 : 0 < k) (hk : k < p) :
    padicValRat p (k : ℚ) = 0 := by
  rw [padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk0 hk)]
  norm_num

theorem centralCoeff_odd_prime_valuation_zero_of_lt {p l : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hl : 2 * l < p) :
    padicValRat p (centralCoeff l) = 0 := by
  have hsq : 2 * l < p ^ 2 := by nlinarith [hp.two_le]
  have hlp : l < p := by omega
  rw [centralCoeff_odd_prime_single_carry hp hp2 hsq,
    Nat.mod_eq_of_lt hlp, if_neg (by omega : ¬p ≤ 2 * l)]

theorem momentScalar_even_odd_prime_valuation_zero_of_lt {p l : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hl : 2 * l + 1 < p) :
    padicValRat p (momentScalar (2 * l)) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat_primes hp2]
    norm_num
  have hden : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hndvd : ¬p ∣ 2 * l + 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) hl
  rw [momentScalar_even,
    padicValRat.div (by norm_num) (mul_ne_zero hden (centralCoeff_ne_zero l)),
    padicValRat.mul hden (centralCoeff_ne_zero l), htwo,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hndvd,
    centralCoeff_odd_prime_valuation_zero_of_lt hp hp2 (by omega)]
  norm_num

theorem momentScalar_odd_prime_valuation_nonneg {p i : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i + 1 < p) :
    0 ≤ padicValRat p (momentScalar i) := by
  by_cases heven : i % 2 = 0
  · have heq : i = 2 * (i / 2) := by omega
    have hv : padicValRat p (momentScalar i) = 0 := by
      rw [heq]
      exact momentScalar_even_odd_prime_valuation_zero_of_lt hp hp2 (by omega)
    exact le_of_eq hv.symm
  · simp [momentScalar, heven]

theorem boundaryMinus_odd_prime_valuation_nonneg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n < p) : 0 ≤ padicValRat p (boundaryMinus n) := by
  have : Fact p.Prime := ⟨hp⟩
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simpa using (zero_le_padicValRat_of_nat (p := p) 2)
      | succ d =>
        rw [boundaryMinus]
        apply prime_div_integral
        · apply prime_add_integral
          · apply prime_add_integral
            · exact prime_mul_integral (zero_le_padicValRat_of_nat _)
                (ih d (by omega) (by omega))
            · exact momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega)
          · exact momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega)
        · exact prime_nat_den_valuation (by omega) (by omega)
        · positivity

theorem boundaryPlus_odd_prime_valuation_nonneg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n < p) : 0 ≤ padicValRat p (boundaryPlus n) := by
  have : Fact p.Prime := ⟨hp⟩
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat_primes hp2]
    norm_num
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ d =>
        rw [boundaryPlus]
        apply prime_div_integral
        · apply prime_add_integral
          · exact prime_mul_integral (zero_le_padicValRat_of_nat _)
              (ih d (by omega) (by omega))
          · exact prime_div_integral (le_of_eq htwo.symm)
              (prime_nat_den_valuation (by omega) (by omega)) (by positivity)
        · exact prime_nat_den_valuation (by omega) (by omega)
        · positivity

theorem momentRat_odd_prime_small_valuation_nonneg {p i j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i < p) (hj : j < p) :
    0 ≤ padicValRat p (momentRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji]
    apply prime_sub_integral
    · exact boundaryMinus_odd_prime_valuation_nonneg hp hp2 _ (by omega)
    · apply prime_sum_integral
      intro k hk
      have hk' : k < j := Finset.mem_range.mp hk
      exact prime_div_integral
        (momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega))
        (prime_nat_den_valuation (by omega) (by omega)) (by positivity)
  · rw [momentRat_of_lt (by omega : i < j)]
    apply prime_sub_integral
    · exact boundaryPlus_odd_prime_valuation_nonneg hp hp2 _ (by omega)
    · apply prime_sum_integral
      intro k hk
      have hk' : k < i := Finset.mem_range.mp hk
      exact prime_div_integral
        (momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega))
        (prime_nat_den_valuation (by omega) (by omega)) (by positivity)

theorem momentRat_odd_prime_small_den_ne_zero {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hi : i < p) (hj : j < p) :
    ((momentRat i j).den : ZMod p) ≠ 0 :=
  rational_den_ne_zero_of_valuation_nonneg
    (momentRat_odd_prime_small_valuation_nonneg hp.out hp2 hi hj)


end InternalCatalan



namespace InternalCatalan

theorem nat_fraction_reduced_residue {p : ℕ} [hp : Fact p.Prime] (n d : ℕ)
    (hd : (d : ZMod p) ≠ 0) :
    (((n : ℚ) / d).den : ZMod p) ≠ 0 ∧
      (((n : ℚ) / d).num : ZMod p) / (((n : ℚ) / d).den : ZMod p) =
        (n : ZMod p) / (d : ZMod p) := by
  let q : ℚ := (n : ℚ) / d
  have hd0 : d ≠ 0 := by intro h; apply hd; simp [h]
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hdnot : ¬p ∣ d := fun h => hd ((ZMod.natCast_eq_zero_iff d p).mpr h)
  have hdval : padicValRat p (d : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hdnot]
    norm_num
  have hqval : 0 ≤ padicValRat p q := by
    by_cases hn : n = 0
    · simp [q, hn]
    · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      dsimp only [q]
      rw [padicValRat.div hnq hdq, hdval, sub_zero]
      exact zero_le_padicValRat_of_nat n
  have hqd := rational_den_ne_zero_of_valuation_nonneg hqval
  have hqeq : (q.num : ℚ) / (q.den : ℚ) = (n : ℚ) / (d : ℚ) := q.num_div_den
  have hcrossq := (div_eq_div_iff (by exact_mod_cast q.den_ne_zero) hdq).mp hqeq
  have hcrossz : q.num * (d : ℤ) = (n : ℤ) * (q.den : ℤ) := by
    exact_mod_cast hcrossq
  have hcross := congrArg (fun z : ℤ => (z : ZMod p)) hcrossz
  push_cast at hcross
  exact ⟨hqd, (div_eq_div_iff hqd hd).mpr hcross⟩

theorem centralCoeff_reduced_residue {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (l : ℕ) :
    ((centralCoeff l).den : ZMod p) ≠ 0 ∧
      ((centralCoeff l).num : ZMod p) / ((centralCoeff l).den : ZMod p) =
        ((2 * l).choose l : ZMod p) / (4 : ZMod p) ^ l := by
  have hd : ((4 ^ l : ℕ) : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using oddPrimeWeight_four_pow_ne_zero hp.out hp2 l
  simpa only [centralCoeff, Nat.cast_pow, Nat.cast_ofNat] using
    nat_fraction_reduced_residue ((2 * l).choose l) (4 ^ l) hd

theorem centralBinom_residue_digit_no_carry {p l : ℕ} [hp : Fact p.Prime]
    (hl : 2 * (l % p) < p) :
    ((2 * l).choose l : ZMod p) =
      ((2 * (l / p)).choose (l / p) : ZMod p) *
        ((2 * (l % p)).choose (l % p) : ZMod p) := by
  have hmod : (2 * l) % p = 2 * (l % p) := by
    rw [← Nat.mul_mod_mod 2 l p, Nat.mod_eq_of_lt hl]
  have hdiv : (2 * l) / p = 2 * (l / p) := by
    have h := Nat.add_div (a := l) (b := l) hp.out.pos
    simpa [← two_mul, show ¬p ≤ 2 * (l % p) by omega] using h
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := 2 * l) (k := l)
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [hmod, hdiv, Nat.cast_mul] at hc
  simpa only [mul_comm] using hc

theorem centralCoeff_denominator_digit {p : ℕ} [Fact p.Prime] (l : ℕ) :
    (4 : ZMod p) ^ l = (4 : ZMod p) ^ (l / p) * (4 : ZMod p) ^ (l % p) := by
  calc
    (4 : ZMod p) ^ l = (4 : ZMod p) ^ (l % p + p * (l / p)) := by rw [Nat.mod_add_div]
    _ = (4 : ZMod p) ^ (l % p) * ((4 : ZMod p) ^ p) ^ (l / p) := by
      rw [pow_add, pow_mul]
    _ = _ := by rw [ZMod.pow_card]; ring

theorem centralCoeff_finite_digit_no_carry {p l : ℕ} [Fact p.Prime]
    (hl : 2 * (l % p) < p) :
    ((2 * l).choose l : ZMod p) / (4 : ZMod p) ^ l =
      (((2 * (l / p)).choose (l / p) : ZMod p) / (4 : ZMod p) ^ (l / p)) *
        (((2 * (l % p)).choose (l % p) : ZMod p) / (4 : ZMod p) ^ (l % p)) := by
  rw [centralBinom_residue_digit_no_carry hl, centralCoeff_denominator_digit,
    mul_div_mul_comm]

theorem centralCoeff_digit_no_carry {p l : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hl : 2 * (l % p) < p) :
    ((centralCoeff l).den : ZMod p) ≠ 0 ∧
      ((centralCoeff (l / p)).den : ZMod p) ≠ 0 ∧
        ((centralCoeff (l % p)).den : ZMod p) ≠ 0 ∧
          ((centralCoeff l).num : ZMod p) / ((centralCoeff l).den : ZMod p) =
            (((centralCoeff (l / p)).num : ZMod p) / ((centralCoeff (l / p)).den : ZMod p)) *
              (((centralCoeff (l % p)).num : ZMod p) / ((centralCoeff (l % p)).den : ZMod p)) := by
  have h := centralCoeff_reduced_residue hp2 l
  have hq := centralCoeff_reduced_residue hp2 (l / p)
  have hr := centralCoeff_reduced_residue hp2 (l % p)
  refine ⟨h.1, hq.1, hr.1, ?_⟩
  rw [h.2, hq.2, hr.2]
  exact centralCoeff_finite_digit_no_carry hl





theorem boundaryFactor_even_digit_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hrEven : (z % p) % 2 = 0) :
    ((boundaryFactor z).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor (z / p)).den : ZMod p) ≠ 0 ∧
        ((centralCoeff ((z % p) / 2)).den : ZMod p) ≠ 0 ∧
          ((boundaryFactor z).num : ZMod p) / ((boundaryFactor z).den : ZMod p) =
            (((boundaryFactor (z / p)).num : ZMod p) /
              ((boundaryFactor (z / p)).den : ZMod p)) *
                (((centralCoeff ((z % p) / 2)).num : ZMod p) /
                  ((centralCoeff ((z % p) / 2)).den : ZMod p)) := by
  have hz2 : 2 * (z / 2) = z := by omega
  have hc : 2 * ((z / 2) % p) < p := by
    have hiff := double_carry_iff_remainder_odd p (z / 2)
      (hp.out.mod_two_eq_one_iff_ne_two.mpr hp2)
    rw [hz2] at hiff
    have hnot : ¬(z % p) % 2 = 1 := by omega
    exact Nat.lt_of_not_ge (fun h => hnot (hiff.mp h))
  have hmod : z % p = 2 * ((z / 2) % p) := by
    conv_lhs => rw [← hz2]
    rw [← Nat.mul_mod_mod 2 (z / 2) p, Nat.mod_eq_of_lt hc]
  have hdiv : z / p = 2 * ((z / 2) / p) := by
    have h := Nat.add_div (a := z / 2) (b := z / 2) hp.out.pos
    have h' : (2 * (z / 2)) / p = 2 * ((z / 2) / p) := by
      simpa [← two_mul, show ¬p ≤ 2 * ((z / 2) % p) by omega] using h
    simpa only [hz2] using h'
  have hqEven : (z / p) % 2 = 0 := by omega
  have hq : (z / 2) / p = (z / p) / 2 := by omega
  have hr : (z / 2) % p = (z % p) / 2 := by omega
  have hzfac : boundaryFactor z = centralCoeff (z / 2) := by
    rw [boundaryFactor, if_pos hzEven]
  have hqfac : boundaryFactor (z / p) = centralCoeff ((z / p) / 2) := by
    rw [boundaryFactor, if_pos hqEven]
  simpa only [hzfac, hqfac, hq, hr] using centralCoeff_digit_no_carry hp2 hc

theorem boundaryFactor_even_carry_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hrOdd : (z % p) % 2 = 1) :
    ((boundaryFactor z).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor z).num : ZMod p) / ((boundaryFactor z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  rw [boundaryFactor_even_odd_prime_eq_one hp.out hp2 hzEven hz hrOdd]
  norm_num






theorem filterCoeffRat_reduced_residue {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat N v).den : ZMod p) ≠ 0 ∧
      ((filterCoeffRat N v).num : ZMod p) / ((filterCoeffRat N v).den : ZMod p) =
        (-1 : ZMod p) ^ v * ((q N).choose v : ZMod p) := by
  have hint : filterCoeffRat N v =
      (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) := by
    simp [filterCoeffRat]
  rw [hint, Rat.den_intCast, Rat.num_intCast]
  simp

theorem filterBinomial_prime_digit {p v : ℕ} [hp : Fact p.Prime] :
    ((4 * p).choose v : ZMod p) =
      if v % p = 0 then ((4 : ℕ).choose (v / p) : ZMod p) else 0 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := 4 * p) (k := v)
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [Nat.mul_mod_left, Nat.mul_div_cancel 4 hp.out.pos, Nat.cast_mul] at hc
  by_cases hv : v % p = 0
  · simpa [hv] using hc
  · have hzero : (0 : ℕ).choose (v % p) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simpa [hv, hzero] using hc

theorem filterCoeffRat_prime_digit_reduction {p v : ℕ} [hp : Fact p.Prime] :
    ((filterCoeffRat p v).den : ZMod p) ≠ 0 ∧
      ((filterCoeffRat p v).num : ZMod p) / ((filterCoeffRat p v).den : ZMod p) =
        if v % p = 0 then
          (-1 : ZMod p) ^ (v / p) * ((4 : ℕ).choose (v / p) : ZMod p) else 0 := by
  have hcanon := filterCoeffRat_reduced_residue (p := p) p v
  refine ⟨hcanon.1, ?_⟩
  rw [hcanon.2, q, filterBinomial_prime_digit]
  by_cases hv : v % p = 0
  · have hfactor : v = p * (v / p) := by
      have h := Nat.mod_add_div v p
      rw [hv, zero_add] at h
      exact h.symm
    have hsign : (-1 : ZMod p) ^ v = (-1 : ZMod p) ^ (v / p) := by
      calc
        (-1 : ZMod p) ^ v = (-1 : ZMod p) ^ (p * (v / p)) :=
          congrArg (fun n : ℕ => (-1 : ZMod p) ^ n) hfactor
        _ = ((-1 : ZMod p) ^ p) ^ (v / p) := pow_mul _ _ _
        _ = _ := by rw [ZMod.pow_card]
    rw [if_pos hv, if_pos hv, hsign]
  · rw [if_neg hv, if_neg hv, mul_zero]

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeEvenStartingZero
namespace OAI


namespace InternalCatalan

theorem rational_residue_mul {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    ((a * b).den : ZMod p) ≠ 0 ∧
      ((a * b).num : ZMod p) / ((a * b).den : ZMod p) =
        ((a.num : ZMod p) / (a.den : ZMod p)) *
          ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hab : ((a * b).den : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ (a * b).den :=
      (ZMod.natCast_eq_zero_iff (a * b).den p).mp hzero
    have hprod : p ∣ a.den * b.den := hdiv.trans (Rat.mul_den_dvd a b)
    have hcast := (ZMod.natCast_eq_zero_iff (a.den * b.den) p).mpr hprod
    exact mul_ne_zero ha hb (by simpa only [Nat.cast_mul] using hcast)
  refine ⟨hab, ?_⟩
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hab (mul_ne_zero ha hb)).mpr
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.mul_num_den' a b)
  push_cast at hc
  simpa only [mul_assoc] using hc

theorem rational_residue_inv {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ≠ 0) (hv : padicValRat p q = 0) :
    ((q⁻¹).den : ZMod p) ≠ 0 ∧
      ((q⁻¹).num : ZMod p) / ((q⁻¹).den : ZMod p) =
        ((q.num : ZMod p) / (q.den : ZMod p))⁻¹ := by
  have hd : (q.den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg (by omega)
  have hdi : ((q⁻¹).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg (by simp [padicValRat.inv, hv])
  refine ⟨hdi, ?_⟩
  have hm := rational_residue_mul hd hdi
  have hprod : ((q.num : ZMod p) / (q.den : ZMod p)) *
      (((q⁻¹).num : ZMod p) / ((q⁻¹).den : ZMod p)) = 1 := by
    simpa [mul_inv_cancel₀ hq] using hm.2.symm
  exact ((mul_eq_one_iff_inv_eq₀ (left_ne_zero_of_mul_eq_one hprod)).mp hprod).symm

theorem rational_residue_nat_mul_eq {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (n m : ℕ) (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0)
    (h : (n : ℚ) * a = (m : ℚ) * b) :
    (n : ZMod p) * ((a.num : ZMod p) / (a.den : ZMod p)) =
      (m : ZMod p) * ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hna := rational_residue_mul (a := (n : ℚ)) (b := a) (by simp) ha
  have hmb := rational_residue_mul (a := (m : ℚ)) (b := b) (by simp) hb
  have he := congrArg (fun q : ℚ => (q.num : ZMod p) / (q.den : ZMod p)) h
  rw [hna.2, hmb.2] at he
  simpa using he

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

theorem rational_residue_add {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    ((a + b).den : ZMod p) ≠ 0 ∧
      ((a + b).num : ZMod p) / ((a + b).den : ZMod p) =
        ((a.num : ZMod p) / (a.den : ZMod p)) +
          ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hab : ((a + b).den : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ (a + b).den :=
      (ZMod.natCast_eq_zero_iff (a + b).den p).mp hzero
    have hprod : p ∣ a.den * b.den := hdiv.trans (Rat.add_den_dvd a b)
    have hcast := (ZMod.natCast_eq_zero_iff (a.den * b.den) p).mpr hprod
    exact mul_ne_zero ha hb (by simpa only [Nat.cast_mul] using hcast)
  refine ⟨hab, ?_⟩
  rw [div_add_div _ _ ha hb]
  apply (div_eq_div_iff hab (mul_ne_zero ha hb)).mpr
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.add_num_den' a b)
  push_cast at hc
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hc

theorem rational_residue_sum {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hden : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    ((∑ i ∈ s, f i).den : ZMod p) ≠ 0 ∧
      ((∑ i ∈ s, f i).num : ZMod p) / ((∑ i ∈ s, f i).den : ZMod p) =
        ∑ i ∈ s, ((f i).num : ZMod p) / ((f i).den : ZMod p) := by
  classical
  revert hden
  induction s using Finset.induction_on with
  | empty => intro hden; simp
  | @insert a s ha ih =>
    intro hden
    have hda : ((f a).den : ZMod p) ≠ 0 := hden a (Finset.mem_insert_self a s)
    have hds : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0 :=
      fun i hi => hden i (Finset.mem_insert_of_mem hi)
    have hs := ih hds
    have hadd := rational_residue_add hda hs.1
    simpa only [Finset.sum_insert ha, hs.2] using hadd

end InternalCatalan

end


namespace InternalCatalan

open scoped BigOperators

private theorem scaled_two_div_den_ne_zero {p : ℕ} [hp : Fact p.Prime]
    (e : ℕ) {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q ≤ (e : ℤ)) :
    (((p : ℚ) ^ e * (2 / q)).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  rw [← mul_div_assoc,
    padicValRat.div (mul_ne_zero (pow_ne_zero e hpq) (by norm_num)) hq,
    padicValRat.mul (pow_ne_zero e hpq) (by norm_num),
    padicValRat.pow, padicValRat.self hp.out.one_lt, mul_one]
  omega

private theorem parityBoundarySum_scaled_den_ne_zero {p : ℕ} [Fact p.Prime]
    (a : ℚ) (f : ℕ → ℚ) (u : ℕ)
    (hf : ∀ z, 0 < z → z ≤ u → z % 2 = u % 2 → ((a * f z).den : ZMod p) ≠ 0) :
    ((a * parityBoundarySum f u).den : ZMod p) ≠ 0 := by
  have hsum := rational_residue_sum (p := p) (Finset.range (u + 1))
    (fun z => a * (if 0 < z ∧ z % 2 = u % 2 then f z else 0)) (by
      intro z hz
      by_cases hgood : 0 < z ∧ z % 2 = u % 2
      · rw [if_pos hgood]
        exact hf z hgood.1 (by have := Finset.mem_range.mp hz; omega) hgood.2
      · simp [hgood])
  simpa only [parityBoundarySum, Finset.mul_sum] using hsum.1

theorem boundaryPlusWeight_even_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryPlusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hvz : padicValRat p (z : ℚ) = if z % p = 0 then 1 else 0 := by
    rw [padicValRat.of_nat, nat_valuation_below_prime_sq hp.out (by omega) hz]
    split_ifs <;> norm_num
  have hvden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z) ≤ 2 := by
    rw [padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
      padicValRat.pow, hvz, boundaryFactor_even_odd_prime_valuation hp.out hp2 hzEven hz]
    by_cases hr0 : z % p = 0
    · simp [hr0]
    · simp only [if_neg hr0]
      split_ifs <;> norm_num
  exact scaled_two_div_den_ne_zero 2
    (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)) hvden

theorem boundaryPlusWeight_odd_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    (((p : ℚ) * boundaryPlusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hvz : padicValRat p (z : ℚ) = if z % p = 0 then 1 else 0 := by
    rw [padicValRat.of_nat, nat_valuation_below_prime_sq hp.out (by omega) hz]
    split_ifs <;> norm_num
  have hvden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z) ≤ 1 := by
    rw [padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
      padicValRat.pow, hvz, boundaryFactor_odd_prime_valuation hp.out hp2 hzOdd hz]
    by_cases hr0 : z % p = 0
    · simp [hr0]
    · simp only [if_neg hr0]
      split_ifs <;> norm_num
  simpa only [pow_one, boundaryPlusWeight] using
    scaled_two_div_den_ne_zero 1
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)) hvden

theorem boundaryMinusWeight_even_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hvden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z ^ 2) ≤ 2 := by
    rw [← mul_pow, padicValRat.pow,
      boundaryFactor_even_mul_odd_prime_valuation hp.out hp2 hzEven (by omega) hz]
    split_ifs <;> norm_num
  rw [boundaryMinusWeight, if_pos hzEven]
  exact scaled_two_div_den_ne_zero 2
    (mul_ne_zero (pow_ne_zero 2 hzq) (pow_ne_zero 2 (boundaryFactor_ne_zero z))) hvden

theorem boundaryMinusWeight_odd_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    (((p : ℚ) * boundaryMinusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hvz : padicValRat p (z : ℚ) ≤ 1 := by
    rw [padicValRat.of_nat, nat_valuation_below_prime_sq hp.out (by omega) hz]
    split_ifs <;> norm_num
  rw [boundaryMinusWeight, if_neg (by omega : z % 2 ≠ 0)]
  simpa only [pow_one] using scaled_two_div_den_ne_zero 1 hzq hvz

theorem boundaryPlus_prime_sq_scaled_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).den : ZMod p) ≠ 0 := by
  rw [boundaryPlus_explicit]
  by_cases huEven : u % 2 = 0
  · have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
      apply rational_den_ne_zero_of_valuation_nonneg
      rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 huEven hu]
      split_ifs <;> norm_num
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      ((p : ℚ) ^ 2) boundaryPlusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryPlusWeight_even_scaled_den_ne_zero hp2 hz0
          (hzpar.trans huEven) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryPlusWeight u) =
        boundaryFactor u * ((p : ℚ) ^ 2 * parityBoundarySum boundaryPlusWeight u) := by ring
    rw [heq]
    exact hprod.1
  · have huOdd : u % 2 = 1 := by omega
    have hH := (boundaryFactor_odd_integral_denominators hp2 huOdd hu).2
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      (p : ℚ) boundaryPlusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryPlusWeight_odd_scaled_den_ne_zero hp2
          (hzpar.trans huOdd) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryPlusWeight u) =
        ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * parityBoundarySum boundaryPlusWeight u) := by ring
    rw [heq]
    exact hprod.1

theorem boundaryMinus_prime_sq_scaled_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 := by
  rw [boundaryMinus_explicit]
  by_cases huEven : u % 2 = 0
  · have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
      apply rational_den_ne_zero_of_valuation_nonneg
      rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 huEven hu]
      split_ifs <;> norm_num
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      ((p : ℚ) ^ 2) boundaryMinusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryMinusWeight_even_scaled_den_ne_zero hp2 hz0
          (hzpar.trans huEven) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryMinusWeight u) =
        boundaryFactor u * ((p : ℚ) ^ 2 * parityBoundarySum boundaryMinusWeight u) := by ring
    rw [heq]
    exact hprod.1
  · have huOdd : u % 2 = 1 := by omega
    have hH := (boundaryFactor_odd_integral_denominators hp2 huOdd hu).2
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      (p : ℚ) boundaryMinusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryMinusWeight_odd_scaled_den_ne_zero
          (hzpar.trans huOdd) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryMinusWeight u) =
        ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * parityBoundarySum boundaryMinusWeight u) := by ring
    rw [heq]
    exact hprod.1

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

def oddHarmonicRat (u : ℕ) : ℚ :=
  ∑ z ∈ Finset.range (u + 1), if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0

@[simp] theorem oddHarmonicRat_zero : oddHarmonicRat 0 = 0 := by
  simp [oddHarmonicRat]

theorem oddHarmonicRat_succ (u : ℕ) :
    oddHarmonicRat (u + 1) = oddHarmonicRat u +
      (if 0 < u + 1 ∧ (u + 1) % 2 = 1 then 2 / ((u + 1 : ℕ) : ℚ) else 0) := by
  unfold oddHarmonicRat
  rw [Finset.sum_range_succ]

private theorem oddHarmonicTerm_den_ne_zero {p z : ℕ} [Fact p.Prime]
    (hz : ¬p ∣ z) :
    ((if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0).den : ZMod p) ≠ 0 := by
  by_cases hodd : 0 < z ∧ z % 2 = 1
  · rw [if_pos hodd]
    have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hodd.1)
    have hzval : padicValRat p (z : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hz]
      norm_num
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [padicValRat.div (by norm_num : (2 : ℚ) ≠ 0) hzq, hzval, sub_zero]
    exact zero_le_padicValRat_of_nat 2
  · simp only [if_neg hodd]
    norm_num


private theorem oddHarmonicTerm_scaled_zero {p z : ℕ} [Fact p.Prime]
    (hz : ¬p ∣ z) :
    (((p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0)).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0)).num : ZMod p) /
        (((p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0)).den : ZMod p) = 0 := by
  have h := rational_residue_mul (a := (p : ℚ)) (by simp)
    (oddHarmonicTerm_den_ne_zero hz)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

private theorem oddHarmonicTerm_scaled_multiple {p z : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hz : p ∣ z) :
    (p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0) =
      (if 0 < z / p ∧ (z / p) % 2 = 1 then 2 / ((z / p : ℕ) : ℚ) else 0) := by
  have heq : z = p * (z / p) := (Nat.mul_div_cancel' hz).symm
  have hpOdd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar : z % 2 = (z / p) % 2 := by
    conv_lhs => rw [heq, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod]
  have hpos : 0 < z ↔ 0 < z / p := by
    constructor
    · intro hzpos
      by_contra hq
      have hq0 : z / p = 0 := Nat.eq_zero_of_not_pos hq
      rw [hq0, mul_zero] at heq
      omega
    · intro hq
      have hmul : 0 < p * (z / p) := Nat.mul_pos hp.pos hq
      rwa [← heq] at hmul
  simp only [hpos, hpar]
  by_cases hodd : 0 < z / p ∧ (z / p) % 2 = 1
  · rw [if_pos hodd, if_pos hodd]
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hqq : ((z / p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hodd.1)
    have hcast : (z : ℚ) = (p : ℚ) * ((z / p : ℕ) : ℚ) := by exact_mod_cast heq
    rw [hcast]
    field_simp [hpq, hqq]
  · simp only [if_neg hodd, mul_zero]

theorem oddHarmonicRat_prime_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) * oddHarmonicRat u).den : ZMod p) ≠ 0 ∧
      ((oddHarmonicRat (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * oddHarmonicRat u).num : ZMod p) /
          (((p : ℚ) * oddHarmonicRat u).den : ZMod p) =
            ((oddHarmonicRat (u / p)).num : ZMod p) /
              ((oddHarmonicRat (u / p)).den : ZMod p) := by
  revert hu
  induction u with
  | zero => intro hu; simp
  | succ u ih =>
    intro hu
    have hprev := ih (by omega : u < p ^ 2)
    have hscale : (p : ℚ) * oddHarmonicRat (u + 1) =
        (p : ℚ) * oddHarmonicRat u +
          (p : ℚ) * (if 0 < u + 1 ∧ (u + 1) % 2 = 1 then
            2 / ((u + 1 : ℕ) : ℚ) else 0) := by
      rw [oddHarmonicRat_succ, mul_add]
    by_cases hdiv : p ∣ u + 1
    · have hquot : (u + 1) / p = u / p + 1 := Nat.succ_div_of_dvd hdiv
      have hsmall : u / p + 1 < p := by
        rw [← hquot]
        exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hu)
      have hterm := oddHarmonicTerm_scaled_multiple hp.out hp2 hdiv
      rw [hquot] at hterm
      have htd := oddHarmonicTerm_den_ne_zero (p := p)
        (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (u / p)) hsmall)
      have hscaledDen :
          (((p : ℚ) * (if 0 < u + 1 ∧ (u + 1) % 2 = 1 then
            2 / ((u + 1 : ℕ) : ℚ) else 0)).den : ZMod p) ≠ 0 := by
        rw [hterm]
        exact htd
      have hl := rational_residue_add hprev.1 hscaledDen
      have hr := rational_residue_add hprev.2.1 htd
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot, oddHarmonicRat_succ]
        exact hr.1
      · rw [hscale, hl.2, hterm, hquot, oddHarmonicRat_succ, hr.2, hprev.2.2]
    · have hquot : (u + 1) / p = u / p := Nat.succ_div_of_not_dvd hdiv
      have ht := oddHarmonicTerm_scaled_zero hdiv
      have hl := rational_residue_add hprev.1 ht.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, ht.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan

end


namespace InternalCatalan

theorem rational_residue_sub {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    ((a - b).den : ZMod p) ≠ 0 ∧
      ((a - b).num : ZMod p) / ((a - b).den : ZMod p) =
        ((a.num : ZMod p) / (a.den : ZMod p)) -
          ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hn : ((-b).den : ZMod p) ≠ 0 := by simpa only [Rat.neg_den] using hb
  simpa only [sub_eq_add_neg, Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_div] using
    rational_residue_add ha hn

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

theorem oddPrime_four_half_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (4 : ZMod p) ^ ((p - 1) / 2) = 1 := by
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hdeg : 2 * ((p - 1) / 2) = p - 1 := by omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    have hge := hp.out.two_le
    omega
  calc
    (4 : ZMod p) ^ ((p - 1) / 2) = ((2 : ZMod p) ^ 2) ^ ((p - 1) / 2) := by
      norm_num
    _ = (2 : ZMod p) ^ (2 * ((p - 1) / 2)) := (pow_mul _ _ _).symm
    _ = (2 : ZMod p) ^ (p - 1) := by rw [hdeg]
    _ = 1 := ZMod.pow_card_sub_one_eq_one htwo

theorem centralCoeff_residue_square_block {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (∑ j ∈ Finset.range ((p - 1) / 2 + 1),
      (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p)) ^ 2) =
        (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hk : 2 * ((p - 1) / 2) < p := by omega
  have hchoose :
      (∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        ((((p - 1) / 2).choose j : ℕ) : ZMod p) ^ 2) =
          ((2 * ((p - 1) / 2)).choose ((p - 1) / 2) : ZMod p) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.sum_range_choose_sq ((p - 1) / 2))
    simpa only [Nat.cast_sum, Nat.cast_pow] using hc
  calc
    _ = ∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        ((((p - 1) / 2).choose j : ℕ) : ZMod p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : 2 * j < p := by
        have hjle := Finset.mem_range.mp hj
        omega
      have hsign : ((-1 : ZMod p) ^ j) ^ 2 = 1 := by
        rw [pow_two, ← mul_pow]
        norm_num
      rw [(centralCoeff_reduced_residue hp2 j).2,
        ← oddPrimeWeight_centralCoeff_identity hp2 hjlt, mul_pow, hsign, one_mul]
    _ = ((2 * ((p - 1) / 2)).choose ((p - 1) / 2) : ZMod p) := hchoose
    _ = (-1 : ZMod p) ^ ((p - 1) / 2) := by
      simpa only [Nat.choose_self, Nat.cast_one, mul_one,
        oddPrime_four_half_pow hp2, Nat.centralBinom] using
          (oddPrimeWeight_centralCoeff_mul_identity hp.out hp2 hk).symm


end InternalCatalan

end


open scoped BigOperators

namespace InternalCatalan

theorem boundaryMinusWeight_even_no_carry_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hr0 : z % p ≠ 0) (hrEven : (z % p) % 2 = 0) :
    (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryMinusWeight z).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  have hden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z ^ 2) = 0 := by
    rw [← mul_pow, padicValRat.pow,
      boundaryFactor_even_mul_odd_prime_valuation hp.out hp2 hzEven (by omega) hz]
    simp [hr0, hrEven]
  rw [boundaryMinusWeight, if_pos hzEven, ← mul_div_assoc,
    padicValRat.div (mul_ne_zero (pow_ne_zero 2 hpq) (by norm_num))
      (mul_ne_zero (pow_ne_zero 2 hzq) (pow_ne_zero 2 (boundaryFactor_ne_zero z))),
    padicValRat.mul (pow_ne_zero 2 hpq) (by norm_num),
    padicValRat.pow, padicValRat.self hp.out.one_lt, hden]
  omega

theorem boundaryMinus_even_scaled_residue_sum {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p ^ 2) :
    ((∑ z ∈ Finset.range (u + 1),
      if 0 < z ∧ z % 2 = 0 then (p : ℚ) ^ 2 * boundaryMinusWeight z else 0).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
          (((boundaryFactor u).num : ZMod p) / ((boundaryFactor u).den : ZMod p)) *
            ∑ z ∈ Finset.range (u + 1),
              if 0 < z ∧ z % 2 = 0 then
                (((p : ℚ) ^ 2 * boundaryMinusWeight z).num : ZMod p) /
                  (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p)
              else 0 := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let f : ℕ → ℚ := fun z =>
    if 0 < z ∧ z % 2 = 0 then (p : ℚ) ^ 2 * boundaryMinusWeight z else 0
  have hsum := rational_residue_sum (p := p) (Finset.range (u + 1)) f (by
    intro z hz
    dsimp only [f]
    by_cases hgood : 0 < z ∧ z % 2 = 0
    · rw [if_pos hgood]
      exact boundaryMinusWeight_even_scaled_den_ne_zero hp2 hgood.1 hgood.2
        (by have := Finset.mem_range.mp hz; omega)
    · simp [hgood])
  have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 huEven hu]
    split_ifs <;> norm_num
  have hprod := rational_residue_mul (p := p) hH hsum.1
  have heq : (p : ℚ) ^ 2 * boundaryMinus u =
      boundaryFactor u * (∑ z ∈ Finset.range (u + 1), f z) := by
    rw [boundaryMinus_explicit, parityBoundarySum, huEven]
    simp only [f, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> ring
  refine ⟨hsum.1, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryMinus u) = _
  rw [heq]
  calc
    _ = R (boundaryFactor u) * R (∑ z ∈ Finset.range (u + 1), f z) := hprod.2
    _ = R (boundaryFactor u) *
        (∑ z ∈ Finset.range (u + 1), R (f z)) := by
      congr 1
      exact hsum.2
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hgood : 0 < z ∧ z % 2 = 0 <;> simp [f, R, hgood]

theorem boundaryMinus_even_odd_remainder_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p ^ 2)
    (hrOdd : (u % p) % 2 = 1) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) = 0 := by
  refine ⟨boundaryMinus_prime_sq_scaled_den_ne_zero hp2 hu, ?_⟩
  rw [(boundaryMinus_even_scaled_residue_sum hp2 huEven hu).2,
    (boundaryFactor_even_carry_reduction hp2 huEven hu hrOdd).2, zero_mul]

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.PalindromicCoefficientMatrices
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicU (p l : ℕ) : (ZMod p)[X] :=
  (2 * X) ^ l * (1 + X ^ 2) ^ (p - 1 - l)

def palindromicQ (p i : ℕ) : (ZMod p)[X] :=
  X ^ i * ∑ j ∈ Finset.range (p - i), X ^ (2 * j)

theorem palindromicU_factor (p l : ℕ) :
    palindromicU p l =
      C ((2 : ZMod p) ^ l) * (X ^ l * (1 + X ^ 2) ^ (p - 1 - l)) := by
  simp [palindromicU, mul_pow, mul_assoc, Polynomial.C_ofNat]

theorem palindromicU_coeff_below (p l : ℕ) {k : ℕ} (hk : k < l) :
    (palindromicU p l).coeff k = 0 := by
  rw [palindromicU_factor, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem palindromicU_coeff_self (p l : ℕ) :
    (palindromicU p l).coeff l = (2 : ZMod p) ^ l := by
  rw [palindromicU_factor, coeff_C_mul, coeff_X_pow_mul',
    if_pos le_rfl, Nat.sub_self]
  change (2 : ZMod p) ^ l * constantCoeff ((1 + X ^ 2) ^ (p - 1 - l)) = _
  have hx : constantCoeff (X : (ZMod p)[X]) = 0 := by
    change (X : (ZMod p)[X]).coeff 0 = 0
    simp
  rw [map_pow, map_add, map_one, map_pow, hx]
  simp

theorem palindromicQ_coeff_below (p i : ℕ) {k : ℕ} (hk : k < i) :
    (palindromicQ p i).coeff k = 0 := by
  rw [palindromicQ, coeff_X_pow_mul', if_neg (by omega)]

theorem palindromicQ_coeff_self {p i : ℕ} (hi : i < p) :
    (palindromicQ p i).coeff i = 1 := by
  classical
  rw [palindromicQ, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    simp [coeff_X_pow, hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def palindromicUCoeffMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun k l => (palindromicU p l.val).coeff k.val

def palindromicQCoeffMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun k i => (palindromicQ p i.val).coeff k.val

theorem palindromicUCoeffMatrix_lower (p : ℕ) :
    (palindromicUCoeffMatrix p).IsLowerTriangular := by
  intro k l hkl
  exact palindromicU_coeff_below p l.val hkl

theorem palindromicQCoeffMatrix_lower (p : ℕ) :
    (palindromicQCoeffMatrix p).IsLowerTriangular := by
  intro k i hki
  exact palindromicQ_coeff_below p i.val hki

theorem det_palindromicUCoeffMatrix (p : ℕ) :
    (palindromicUCoeffMatrix p).det = ∏ l : Fin p, (2 : ZMod p) ^ l.val := by
  rw [Matrix.det_of_isLowerTriangular _ (palindromicUCoeffMatrix_lower p)]
  simp only [palindromicUCoeffMatrix, palindromicU_coeff_self]

theorem det_palindromicQCoeffMatrix (p : ℕ) :
    (palindromicQCoeffMatrix p).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (palindromicQCoeffMatrix_lower p)]
  have hdiag : ∀ i : Fin p, palindromicQCoeffMatrix p i i = 1 := by
    intro i
    exact palindromicQ_coeff_self i.isLt
  simp only [hdiag, Finset.prod_const_one]

theorem palindromic_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have hd : p ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

theorem det_palindromicUCoeffMatrix_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (palindromicUCoeffMatrix p).det ≠ 0 := by
  rw [det_palindromicUCoeffMatrix]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  exact pow_ne_zero _ (palindromic_two_ne_zero hp2)


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.PalindromicReversalMultiplicities
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def IsPalindromicAt (p : ℕ) (P : (ZMod p)[X]) : Prop :=
  (∀ k, 2 * p - 2 < k → P.coeff k = 0) ∧
  (∀ k, k ≤ 2 * p - 2 → P.coeff (2 * p - 2 - k) = P.coeff k)

theorem IsPalindromicAt.ext {p : ℕ} (hp : 0 < p) {P Q : (ZMod p)[X]}
    (hP : IsPalindromicAt p P) (hQ : IsPalindromicAt p Q)
    (hlow : ∀ k < p, P.coeff k = Q.coeff k) : P = Q := by
  ext k
  by_cases hk : k < p
  · exact hlow k hk
  · by_cases hhigh : 2 * p - 2 < k
    · rw [hP.1 k hhigh, hQ.1 k hhigh]
    · have hle : k ≤ 2 * p - 2 := by omega
      have href : 2 * p - 2 - k < p := by omega
      exact (hP.2 k hle).symm.trans ((hlow _ href).trans (hQ.2 k hle))

theorem IsPalindromicAt.C_mul {p : ℕ} {P : (ZMod p)[X]}
    (hP : IsPalindromicAt p P) (c : ZMod p) :
    IsPalindromicAt p (C c * P) := by
  constructor
  · intro k hk
    simp only [coeff_C_mul, hP.1 k hk, mul_zero]
  · intro k hk
    simp only [coeff_C_mul, hP.2 k hk]

theorem IsPalindromicAt.sum {p : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → (ZMod p)[X]) (hP : ∀ i ∈ s, IsPalindromicAt p (P i)) :
    IsPalindromicAt p (∑ i ∈ s, P i) := by
  constructor
  · intro k hk
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hP i hi).1 k hk
  · intro k hk
    simp only [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hP i hi).2 k hk


end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem one_add_X_sq_natDegree_le (p : ℕ) :
    (1 + X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [coeff_one, show k ≠ 0 by omega, show k ≠ 2 by omega]

private theorem one_add_X_sq_pow_natDegree_le (p n : ℕ) :
    ((1 + X ^ 2 : (ZMod p)[X]) ^ n).natDegree ≤ 2 * n := by
  simpa only [Nat.mul_comm] using
    natDegree_pow_le_of_le n (one_add_X_sq_natDegree_le p)

private theorem reflect_one_add_X_sq (p : ℕ) :
    reflect 2 (1 + X ^ 2 : (ZMod p)[X]) = 1 + X ^ 2 := by
  rw [reflect_add, reflect_one, reflect_monomial, revAt_le (by omega)]
  simp [add_comm]

private theorem reflect_one_add_X_sq_pow (p n : ℕ) :
    reflect (2 * n) ((1 + X ^ 2 : (ZMod p)[X]) ^ n) =
      (1 + X ^ 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ (1 + X ^ 2 : (ZMod p)[X]) n]
    rw [show 2 * (n + 1) = 2 * n + 2 by omega,
      reflect_mul _ _ (one_add_X_sq_pow_natDegree_le p n)
        (one_add_X_sq_natDegree_le p), ih, reflect_one_add_X_sq]

theorem isPalindromicAt_of_reflect {p : ℕ} {P : (ZMod p)[X]}
    (hdeg : P.natDegree ≤ 2 * p - 2)
    (hreflect : reflect (2 * p - 2) P = P) : IsPalindromicAt p P := by
  constructor
  · intro k hk
    exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hk)
  · intro k hk
    have h := congrArg (fun Q : (ZMod p)[X] => Q.coeff k) hreflect
    simpa only [coeff_reflect, revAt_le hk] using h

theorem palindromicU_natDegree_le {p l : ℕ} (hp : 0 < p) (hl : l < p) :
    (palindromicU p l).natDegree ≤ 2 * p - 2 := by
  have hD : 2 * p - 2 = 2 * l + 2 * (p - 1 - l) := by omega
  have hx : (X ^ l : (ZMod p)[X]).natDegree ≤ 2 * l :=
    (natDegree_X_pow_le l).trans (by omega)
  rw [palindromicU_factor, hD]
  apply (natDegree_C_mul_le _ _).trans
  exact natDegree_mul_le.trans
    (Nat.add_le_add hx (one_add_X_sq_pow_natDegree_le p (p - 1 - l)))

theorem palindromicU_reflect {p l : ℕ} (hp : 0 < p) (hl : l < p) :
    reflect (2 * p - 2) (palindromicU p l) = palindromicU p l := by
  have hD : 2 * p - 2 = 2 * l + 2 * (p - 1 - l) := by omega
  have hx : (X ^ l : (ZMod p)[X]).natDegree ≤ 2 * l :=
    (natDegree_X_pow_le l).trans (by omega)
  simp only [palindromicU_factor]
  rw [hD, reflect_C_mul,
    reflect_mul _ _ hx (one_add_X_sq_pow_natDegree_le p (p - 1 - l)),
    reflect_monomial, revAt_le (by omega), show 2 * l - l = l by omega,
    reflect_one_add_X_sq_pow]

theorem palindromicU_isPalindromic {p l : ℕ} (hp : 0 < p) (hl : l < p) :
    IsPalindromicAt p (palindromicU p l) :=
  isPalindromicAt_of_reflect (palindromicU_natDegree_le hp hl)
    (palindromicU_reflect hp hl)

theorem palindromicQ_eq_sum (p i : ℕ) :
    palindromicQ p i = ∑ j ∈ Finset.range (p - i),
      (X : (ZMod p)[X]) ^ (i + 2 * j) := by
  rw [palindromicQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (pow_add _ _ _).symm

theorem palindromicQ_natDegree_le {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    (palindromicQ p i).natDegree ≤ 2 * p - 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [palindromicQ_eq_sum, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [coeff_X_pow, if_neg (by omega)]

theorem palindromicQ_reflect {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    reflect (2 * p - 2) (palindromicQ p i) = palindromicQ p i := by
  simp only [palindromicQ_eq_sum]
  calc
    reflect (2 * p - 2) (∑ j ∈ Finset.range (p - i),
        (X : (ZMod p)[X]) ^ (i + 2 * j)) =
        ∑ j ∈ Finset.range (p - i),
          reflect (2 * p - 2) ((X : (ZMod p)[X]) ^ (i + 2 * j)) := by
      ext k
      simp only [coeff_reflect, finsetSum_coeff]
    _ = ∑ j ∈ Finset.range (p - i),
        (X : (ZMod p)[X]) ^ (i + 2 * (p - i - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [reflect_monomial, revAt_le (by omega)]
      congr 1
      omega
    _ = ∑ j ∈ Finset.range (p - i),
        (X : (ZMod p)[X]) ^ (i + 2 * j) :=
      Finset.sum_range_reflect (fun j => (X : (ZMod p)[X]) ^ (i + 2 * j)) (p - i)

theorem palindromicQ_isPalindromic {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    IsPalindromicAt p (palindromicQ p i) :=
  isPalindromicAt_of_reflect (palindromicQ_natDegree_le hp hi)
    (palindromicQ_reflect hp hi)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicUCombination (p : ℕ) (c : Fin p → ZMod p) : (ZMod p)[X] :=
  ∑ l : Fin p, C (c l) * palindromicU p l.val

def palindromicUCoordinates (p : ℕ) (P : (ZMod p)[X]) : Fin p → ZMod p :=
  (palindromicUCoeffMatrix p)⁻¹.mulVec (fun k => P.coeff k.val)

theorem palindromicUCombination_coeff (p : ℕ) (c : Fin p → ZMod p) (k : Fin p) :
    (palindromicUCombination p c).coeff k.val =
      (palindromicUCoeffMatrix p).mulVec c k := by
  simp only [palindromicUCombination, finsetSum_coeff, coeff_C_mul,
    Matrix.mulVec_apply_eq_sum, palindromicUCoeffMatrix]
  apply Finset.sum_congr rfl
  intro l hl
  exact mul_comm _ _

theorem palindromicUCombination_isPalindromic {p : ℕ} (hp : 0 < p)
    (c : Fin p → ZMod p) : IsPalindromicAt p (palindromicUCombination p c) := by
  apply IsPalindromicAt.sum
  intro l hl
  exact (palindromicU_isPalindromic hp l.isLt).C_mul (c l)

theorem palindromicUCoordinates_spec {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : (ZMod p)[X]) :
    (palindromicUCoeffMatrix p).mulVec (palindromicUCoordinates p P) =
      fun k => P.coeff k.val := by
  have hunit : IsUnit (palindromicUCoeffMatrix p).det :=
    isUnit_iff_ne_zero.mpr (det_palindromicUCoeffMatrix_ne_zero hp2)
  unfold palindromicUCoordinates
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

theorem palindromicU_expansion {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : (ZMod p)[X]) (hP : IsPalindromicAt p P) :
    P = palindromicUCombination p (palindromicUCoordinates p P) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply IsPalindromicAt.ext hp hP (palindromicUCombination_isPalindromic hp _)
  intro k hk
  rw [palindromicUCombination_coeff p _ (⟨k, hk⟩ : Fin p)]
  exact (congrFun (palindromicUCoordinates_spec hp2 P) (⟨k, hk⟩ : Fin p)).symm

def palindromicTransitionMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  (palindromicUCoeffMatrix p)⁻¹ * palindromicQCoeffMatrix p

theorem palindromicUCoordinates_Q (p : ℕ) (i : Fin p) :
    palindromicUCoordinates p (palindromicQ p i.val) =
      fun l => palindromicTransitionMatrix p l i := by
  funext l
  rfl


theorem palindromicQ_eq_sum_U {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (i : Fin p) :
    palindromicQ p i.val =
      ∑ l : Fin p, C (palindromicTransitionMatrix p l i) * palindromicU p l.val := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := palindromicU_expansion hp2 (palindromicQ p i.val)
    (palindromicQ_isPalindromic hp i.isLt)
  rw [palindromicUCoordinates_Q] at h
  exact h

theorem det_palindromicTransitionMatrix {p : ℕ} [Fact p.Prime] :
    (palindromicTransitionMatrix p).det =
      (∏ l : Fin p, (2 : ZMod p) ^ l.val)⁻¹ := by
  rw [palindromicTransitionMatrix, Matrix.det_mul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv, det_palindromicUCoeffMatrix, det_palindromicQCoeffMatrix, mul_one]

theorem det_palindromicTransitionMatrix_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (palindromicTransitionMatrix p).det ≠ 0 := by
  rw [det_palindromicTransitionMatrix]
  apply inv_ne_zero
  rw [← det_palindromicUCoeffMatrix]
  exact det_palindromicUCoeffMatrix_ne_zero hp2

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicReverseIndex {p : ℕ} (i : Fin p) (hi : 0 < i.val) : Fin p :=
  ⟨p - i.val, by have h := i.isLt; omega⟩

@[simp] theorem palindromicReverseIndex_val {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) : (palindromicReverseIndex i hi).val = p - i.val := rfl

theorem palindromicReverseIndex_pos {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    0 < (palindromicReverseIndex i hi).val := by
  have h := i.isLt
  simp only [palindromicReverseIndex_val]
  omega

@[simp] theorem palindromicReverseIndex_invol {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    palindromicReverseIndex (palindromicReverseIndex i hi)
      (palindromicReverseIndex_pos i hi) = i := by
  apply Fin.ext
  simp only [palindromicReverseIndex_val]
  have h := i.isLt
  omega

def palindromicQPrime (p : ℕ) (i : Fin p) : (ZMod p)[X] :=
  if i.val = 0 then 0 else palindromicQ p (p - i.val)

theorem palindromicQPrime_zero {p : ℕ} (i : Fin p) (hi : i.val = 0) :
    palindromicQPrime p i = 0 := by simp [palindromicQPrime, hi]

theorem palindromicQPrime_pos {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    palindromicQPrime p i =
      palindromicQ p (palindromicReverseIndex i hi).val := by
  simp [palindromicQPrime, show i.val ≠ 0 by omega]

def palindromicReversalMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun k i => if i.val = 0 then 0 else if k.val = p - i.val then 1 else 0

theorem palindromicReversalMatrix_column_zero {p : ℕ} (i : Fin p)
    (hi : i.val = 0) (k : Fin p) : palindromicReversalMatrix p k i = 0 := by
  simp [palindromicReversalMatrix, hi]

theorem palindromicReversalMatrix_column_pos {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) (k : Fin p) :
    palindromicReversalMatrix p k i =
      if k = palindromicReverseIndex i hi then 1 else 0 := by
  have heq : k.val = p - i.val ↔ k = palindromicReverseIndex i hi := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      exact congrArg Fin.val h
  simp only [palindromicReversalMatrix, if_neg (show i.val ≠ 0 by omega), heq]

theorem mul_palindromicReversalMatrix_column_zero {p : ℕ} {ι : Type*}
    (A : Matrix ι (Fin p) (ZMod p)) (l : ι) (i : Fin p) (hi : i.val = 0) :
    (A * palindromicReversalMatrix p) l i = 0 := by
  simp [Matrix.mul_apply, palindromicReversalMatrix_column_zero i hi]

theorem mul_palindromicReversalMatrix_column_pos {p : ℕ} {ι : Type*}
    (A : Matrix ι (Fin p) (ZMod p)) (l : ι) (i : Fin p) (hi : 0 < i.val) :
    (A * palindromicReversalMatrix p) l i = A l (palindromicReverseIndex i hi) := by
  simp [Matrix.mul_apply, palindromicReversalMatrix_column_pos i hi, mul_ite]

def palindromicReversedTransitionMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  palindromicTransitionMatrix p * palindromicReversalMatrix p

theorem palindromicReversedTransitionMatrix_column_zero {p : ℕ} (l i : Fin p)
    (hi : i.val = 0) : palindromicReversedTransitionMatrix p l i = 0 :=
  mul_palindromicReversalMatrix_column_zero _ l i hi

theorem palindromicReversedTransitionMatrix_column_pos {p : ℕ} (l i : Fin p)
    (hi : 0 < i.val) :
    palindromicReversedTransitionMatrix p l i =
      palindromicTransitionMatrix p l (palindromicReverseIndex i hi) :=
  mul_palindromicReversalMatrix_column_pos _ l i hi

theorem palindromicQPrime_eq_sum_U {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicQPrime p i = ∑ l : Fin p,
      C (palindromicReversedTransitionMatrix p l i) * palindromicU p l.val := by
  by_cases hi : i.val = 0
  · rw [palindromicQPrime_zero i hi]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    rw [palindromicReversedTransitionMatrix_column_zero l i hi]
    simp
  · have hip : 0 < i.val := by omega
    rw [palindromicQPrime_pos i hip, palindromicQ_eq_sum_U hp2]
    apply Finset.sum_congr rfl
    intro l hl
    rw [palindromicReversedTransitionMatrix_column_pos l i hip]




theorem palindromicReversalMatrix_mul_self {p : ℕ} (k i : Fin p) :
    (palindromicReversalMatrix p * palindromicReversalMatrix p) k i =
      if i.val = 0 then 0 else if k = i then 1 else 0 := by
  by_cases hi : i.val = 0
  · simp [mul_palindromicReversalMatrix_column_zero _ k i hi, hi]
  · have hip : 0 < i.val := by omega
    rw [mul_palindromicReversalMatrix_column_pos _ k i hip,
      palindromicReversalMatrix_column_pos _ (palindromicReverseIndex_pos i hip),
      palindromicReverseIndex_invol]
    simp [hi]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators







end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromicQPrime_formula {p : ℕ} (i : Fin p) :
    palindromicQPrime p i = (X : (ZMod p)[X]) ^ (p - i.val) *
      ∑ j ∈ Finset.range i.val, X ^ (2 * j) := by
  by_cases hi : i.val = 0
  · simp [palindromicQPrime, hi]
  · have hsub : p - (p - i.val) = i.val := by have h := i.isLt; omega
    simp only [palindromicQPrime, if_neg hi, palindromicQ, hsub]

theorem palindromicQ_add_X_pow_QPrime {p : ℕ} (i : Fin p) :
    palindromicQ p i.val + (X : (ZMod p)[X]) ^ p * palindromicQPrime p i =
      X ^ i.val * ∑ j ∈ Finset.range p, X ^ (2 * j) := by
  have hsplit := Finset.sum_range_add
    (fun j : ℕ => (X : (ZMod p)[X]) ^ (2 * j)) (p - i.val) i.val
  rw [Nat.sub_add_cancel (Nat.le_of_lt i.isLt)] at hsplit
  rw [palindromicQ, palindromicQPrime_formula, hsplit, mul_add]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← pow_add]
  congr 1
  have h := i.isLt
  omega

theorem palindromicPairing_eq_sum_U {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    (X : (ZMod p)[X]) ^ i.val * (∑ j ∈ Finset.range p, X ^ (2 * j)) =
      ∑ l : Fin p, (C (palindromicTransitionMatrix p l i) +
        C (palindromicReversedTransitionMatrix p l i) * X ^ p) *
          palindromicU p l.val := by
  rw [← palindromicQ_add_X_pow_QPrime, palindromicQ_eq_sum_U hp2,
    palindromicQPrime_eq_sum_U hp2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicResidueSum {R : Type*} [CommSemiring R] (p : ℕ)
    (A : Fin p → R[X]) : R[X] :=
  ∑ l : Fin p, X ^ l.val * (A l).comp (X ^ p)

theorem palindromicResidue_sub_not_dvd {p : ℕ} (l ell : Fin p) (u : ℕ)
    (hne : l ≠ ell) (hle : l.val ≤ u * p + ell.val) :
    ¬ p ∣ u * p + ell.val - l.val := by
  intro hd
  have hz : (u * p + ell.val - l.val) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hmod := congrArg (fun n : ℕ => n % p) (Nat.sub_add_cancel hle)
  have hval : l.val = ell.val := by
    simpa only [Nat.add_mod, Nat.mul_mod, hz, Nat.mod_self, Nat.mul_zero,
      Nat.zero_mod, zero_add, Nat.mod_eq_of_lt l.isLt,
      Nat.mod_eq_of_lt ell.isLt] using hmod
  exact hne (Fin.ext hval)

theorem palindromicResidueSum_coeff {R : Type*} [CommSemiring R] {p : ℕ}
    (hp : 0 < p) (A : Fin p → R[X]) (u : ℕ) (ell : Fin p) :
    (palindromicResidueSum p A).coeff (u * p + ell.val) = (A ell).coeff u := by
  classical
  rw [palindromicResidueSum, finsetSum_coeff, Finset.sum_eq_single ell]
  · rw [coeff_X_pow_mul, ← expand_eq_comp_X_pow, coeff_expand_mul hp]
  · intro l hl hne
    rw [coeff_X_pow_mul']
    split_ifs with hle
    · rw [← expand_eq_comp_X_pow, coeff_expand hp,
        if_neg (palindromicResidue_sub_not_dvd l ell u hne hle)]
    · rfl
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ ell))

def palindromicPBase (p j : ℕ) : (ZMod p)[X] :=
  (rowP 1 j).map (Int.castRingHom (ZMod p))

def palindromicDBase (p j : ℕ) : (ZMod p)[X] :=
  (rowD 1 j).map (Int.castRingHom (ZMod p))

def palindromicPBaseCombination (p r0 : ℕ) (i l : Fin p) : (ZMod p)[X] :=
  C (palindromicTransitionMatrix p l i) * palindromicPBase p r0 +
    C (palindromicReversedTransitionMatrix p l i) * palindromicPBase p (r0 + 1)

def palindromicDBaseCombination (p r0 : ℕ) (i l : Fin p) : (ZMod p)[X] :=
  C (palindromicTransitionMatrix p l i) * palindromicDBase p r0 +
    C (palindromicReversedTransitionMatrix p l i) * palindromicDBase p (r0 + 1)

def palindromicPResidueSum (p r0 : ℕ) (i : Fin p) : (ZMod p)[X] :=
  ∑ l : Fin p, X ^ l.val * X ^ p *
    (C (palindromicTransitionMatrix p l i) * (palindromicPBase p r0).comp (X ^ p) +
      C (palindromicReversedTransitionMatrix p l i) *
        (palindromicPBase p (r0 + 1)).comp (X ^ p))

def palindromicDResidueSum (p r0 : ℕ) (i : Fin p) : (ZMod p)[X] :=
  ∑ l : Fin p, X ^ l.val *
    (C (palindromicTransitionMatrix p l i) * (palindromicDBase p r0).comp (X ^ p) +
      C (palindromicReversedTransitionMatrix p l i) *
        (palindromicDBase p (r0 + 1)).comp (X ^ p))

theorem palindromicPResidueSum_eq_X_pow_mul (p r0 : ℕ) (i : Fin p) :
    palindromicPResidueSum p r0 i = X ^ p *
      palindromicResidueSum p (palindromicPBaseCombination p r0 i) := by
  classical
  simp only [palindromicPResidueSum, palindromicResidueSum,
    palindromicPBaseCombination, add_comp, mul_comp, C_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem palindromicDResidueSum_eq (p r0 : ℕ) (i : Fin p) :
    palindromicDResidueSum p r0 i =
      palindromicResidueSum p (palindromicDBaseCombination p r0 i) := by
  simp only [palindromicDResidueSum, palindromicResidueSum,
    palindromicDBaseCombination, add_comp, mul_comp, C_comp]

theorem palindromicPResidueSum_coeff (p r0 u : ℕ) (i ell : Fin p) :
    (palindromicPResidueSum p r0 i).coeff ((u + 1) * p + ell.val) =
      palindromicTransitionMatrix p ell i * (palindromicPBase p r0).coeff u +
        palindromicReversedTransitionMatrix p ell i *
          (palindromicPBase p (r0 + 1)).coeff u := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le ell.val) ell.isLt
  have hindex : (u + 1) * p + ell.val = (u * p + ell.val) + p := by ring
  rw [palindromicPResidueSum_eq_X_pow_mul, hindex, coeff_X_pow_mul,
    palindromicResidueSum_coeff hp]
  simp only [palindromicPBaseCombination, coeff_add, coeff_C_mul]

theorem palindromicDResidueSum_coeff (p r0 u : ℕ) (i ell : Fin p) :
    (palindromicDResidueSum p r0 i).coeff (u * p + ell.val) =
      palindromicTransitionMatrix p ell i * (palindromicDBase p r0).coeff u +
        palindromicReversedTransitionMatrix p ell i *
          (palindromicDBase p (r0 + 1)).coeff u := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le ell.val) ell.isLt
  rw [palindromicDResidueSum_eq, palindromicResidueSum_coeff hp]
  simp only [palindromicDBaseCombination, coeff_add, coeff_C_mul]

theorem palindromicPResidueSum_coeff_below (p r0 : ℕ) (i ell : Fin p) :
    (palindromicPResidueSum p r0 i).coeff ell.val = 0 := by
  rw [palindromicPResidueSum_eq_X_pow_mul, coeff_X_pow_mul',
    if_neg (Nat.not_le_of_lt ell.isLt)]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan




























open Matrix Module

































end InternalCatalan




open scoped BigOperators

namespace InternalCatalan


end InternalCatalan

end



noncomputable section
open scoped BigOperators Matrix

namespace InternalCatalan

section CoordinateKernel

variable {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι]




end CoordinateKernel
















end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.PalindromicBlockInverse
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan





@[simp] theorem fixedMatrix_zero : fixedMatrix 0 = fixedB0 := by simp [fixedMatrix]
@[simp] theorem fixedMatrix_one : fixedMatrix 1 = fixedB0 + fixedB1 := by
  simp [fixedMatrix]
@[simp] theorem fixedMatrix_neg_one : fixedMatrix (-1) = fixedB0 - fixedB1 := by
  simp [fixedMatrix, sub_eq_add_neg]




end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan




end InternalCatalan

end



noncomputable section

namespace InternalCatalan

theorem palindromicReversalMatrix_cube_mul (p : ℕ) :
    (palindromicReversalMatrix p * palindromicReversalMatrix p) *
      palindromicReversalMatrix p = palindromicReversalMatrix p := by
  ext k i
  by_cases hi : i.val = 0
  · rw [mul_palindromicReversalMatrix_column_zero _ k i hi,
      palindromicReversalMatrix_column_zero i hi k]
  · have hip : 0 < i.val := by omega
    rw [mul_palindromicReversalMatrix_column_pos _ k i hip,
      palindromicReversalMatrix_mul_self,
      if_neg (show (palindromicReverseIndex i hip).val ≠ 0 by
        have h := palindromicReverseIndex_pos i hip
        omega)]
    exact (palindromicReversalMatrix_column_pos i hip k).symm


def palindromicReversalProjZero (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  1 - palindromicReversalMatrix p * palindromicReversalMatrix p

def palindromicReversalProjPlus (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  (1 / 2 : ZMod p) •
    (palindromicReversalMatrix p * palindromicReversalMatrix p +
      palindromicReversalMatrix p)

def palindromicReversalProjMinus (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  (1 / 2 : ZMod p) •
    (palindromicReversalMatrix p * palindromicReversalMatrix p -
      palindromicReversalMatrix p)

theorem palindromicReversalProjections_sum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicReversalProjZero p + palindromicReversalProjPlus p +
      palindromicReversalProjMinus p = 1 := by
  ext k i
  simp only [palindromicReversalProjZero, palindromicReversalProjPlus,
    palindromicReversalProjMinus, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [palindromic_two_ne_zero hp2]
  ring




theorem palindromicReversalProjZero_mul_matrix {p : ℕ} [Fact p.Prime] :
    palindromicReversalProjZero p * palindromicReversalMatrix p = 0 := by
  rw [palindromicReversalProjZero, sub_mul, one_mul,
    palindromicReversalMatrix_cube_mul, sub_self]

theorem palindromicReversalProjPlus_mul_matrix {p : ℕ} [Fact p.Prime] :
    palindromicReversalProjPlus p * palindromicReversalMatrix p =
      palindromicReversalProjPlus p := by
  simp only [palindromicReversalProjPlus, Matrix.smul_mul, add_mul]
  rw [palindromicReversalMatrix_cube_mul]
  congr 1
  exact add_comm _ _

theorem palindromicReversalProjMinus_mul_matrix {p : ℕ} [Fact p.Prime] :
    palindromicReversalProjMinus p * palindromicReversalMatrix p =
      -palindromicReversalProjMinus p := by
  simp only [palindromicReversalProjMinus, Matrix.smul_mul, sub_mul]
  rw [palindromicReversalMatrix_cube_mul, ← smul_neg, neg_sub]







open scoped BigOperators

def palindromicRatResidue (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p :=
  (x.num : ZMod p) / (x.den : ZMod p)

def fixedB0Residue (p : ℕ) [Fact p.Prime] : Matrix (Fin 48) (Fin 48) (ZMod p) :=
  fun r k => palindromicRatResidue p (fixedB0 r k)

def fixedB1Residue (p : ℕ) [Fact p.Prime] : Matrix (Fin 48) (Fin 48) (ZMod p) :=
  fun r k => palindromicRatResidue p (fixedB1 r k)

theorem fixedB0Residue_apply (p : ℕ) [Fact p.Prime] (r k : Fin 48) :
    fixedB0Residue p r k = palindromicRatResidue p (fixedBaseEntryRat r.castSucc k) :=
  rfl

theorem fixedB1Residue_apply (p : ℕ) [Fact p.Prime] (r k : Fin 48) :
    fixedB1Residue p r k = palindromicRatResidue p (fixedBaseEntryRat r.succ k) :=
  rfl

@[simp] theorem palindromicRatResidue_intCast (p : ℕ) [Fact p.Prime] (z : ℤ) :
    palindromicRatResidue p (z : ℚ) = (z : ZMod p) := by
  simp [palindromicRatResidue]

theorem palindromicRatResidue_mul {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    palindromicRatResidue p (a * b) =
      palindromicRatResidue p a * palindromicRatResidue p b :=
  (rational_residue_mul ha hb).2

theorem palindromicRatResidue_add {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    palindromicRatResidue p (a + b) =
      palindromicRatResidue p a + palindromicRatResidue p b :=
  (rational_residue_add ha hb).2

theorem palindromicRatResidue_sub {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    palindromicRatResidue p (a - b) =
      palindromicRatResidue p a - palindromicRatResidue p b :=
  (rational_residue_sub ha hb).2

theorem palindromicRatResidue_sum {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    palindromicRatResidue p (∑ i ∈ s, f i) =
      ∑ i ∈ s, palindromicRatResidue p (f i) :=
  (rational_residue_sum s f hf).2

private theorem fixed_nat_inverse_pow_den {p n : ℕ} [Fact p.Prime]
    (hn0 : 0 < n) (hn : n < p) (d : ℕ) :
    ((1 / (n : ℚ) ^ d).den : ZMod p) ≠ 0 := by
  have hv : padicValRat p ((n : ℚ) ^ d) = 0 := by
    rw [padicValRat.pow, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hn0 hn)]
    simp
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  simpa only [one_div] using (rational_residue_inv (pow_ne_zero d hnq) hv).1

theorem harmonicRat_small_den_ne_zero {p n : ℕ} [Fact p.Prime]
    (hn : n < p) (d : ℕ) : ((harmonicRat d n).den : ZMod p) ≠ 0 := by
  apply (rational_residue_sum (Finset.range n)
    (fun k => 1 / (((k + 1 : ℕ) : ℚ) ^ d)) ?_).1
  intro k hk
  exact fixed_nat_inverse_pow_den (by omega) (by
    have := Finset.mem_range.mp hk
    omega) d

theorem zetaRat_small_den_ne_zero {p i j : ℕ} [Fact p.Prime]
    (hi : i < p) (hj : j < p) : ((zetaRat i j).den : ZMod p) ≠ 0 := by
  have hle : ∀ a b : ℕ, a < p → b < p → b ≤ a →
      ((zetaRat a b).den : ZMod p) ≠ 0 := by
    intro a b ha hb hba
    by_cases hab : a = b
    · subst b
      simpa only [zetaRat_diagonal, Rat.neg_den] using
        harmonicRat_small_den_ne_zero ha 2
    · rw [zetaRat_of_ne hab, ← Nat.cast_sub hba, div_eq_mul_inv]
      have hinv : (((((a - b : ℕ) : ℚ)⁻¹).den : ℕ) : ZMod p) ≠ 0 := by
        simpa only [pow_one, one_div] using
          (fixed_nat_inverse_pow_den (p := p) (n := a - b) (by omega) (by omega) 1)
      exact (rational_residue_mul
        (rational_residue_sub (harmonicRat_small_den_ne_zero ha 1)
          (harmonicRat_small_den_ne_zero hb 1)).1 hinv).1
  rcases le_total j i with hji | hij
  · exact hle i j hi hj hji
  · rw [zetaRat_symm]
    exact hle j i hj hi hij

private theorem fixed_three_halves_den {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) : (((3 / 2 : ℚ).den : ℕ) : ZMod p) ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p)) hdiv
  simpa only [show (3 / 2 : ℚ).den = 2 by norm_num, Nat.cast_ofNat] using htwo

theorem fixed_rawEntryRat_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r j : ℕ) (hj : j < p) :
    ((rawEntryRat 0 1 r j).den : ZMod p) ≠ 0 := by
  have hM : ∀ i ∈ Finset.range (H 1),
      (((((rowP 1 r).coeff i : ℚ) * momentRat i j)).den : ZMod p) ≠ 0 := by
    intro i hi
    apply (rational_residue_mul (by simp) ?_).1
    exact momentRat_odd_prime_small_den_ne_zero (by omega)
      (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj
  have hZ : ∀ i ∈ Finset.range (H 1),
      (((((rowD 1 r).coeff i : ℚ) * zetaRat i j)).den : ZMod p) ≠ 0 := by
    intro i hi
    apply (rational_residue_mul (by simp) ?_).1
    exact zetaRat_small_den_ne_zero
      (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj
  rw [rawEntryRat_zero]
  exact (rational_residue_sub
    (rational_residue_sum _ _ hM).1
    (rational_residue_mul (fixed_three_halves_den hp)
      (rational_residue_sum _ _ hZ).1).1).1

theorem filterCoeffRat_den_ne_zero {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat N v).den : ZMod p) ≠ 0 := by
  have hcast : (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) =
      filterCoeffRat N v := by simp [filterCoeffRat]
  rw [← hcast, Rat.den_intCast, Nat.cast_one]
  exact one_ne_zero

theorem palindromicRatResidue_int_sum {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (a : ι → ℤ) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    ((∑ i ∈ s, (a i : ℚ) * f i).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (∑ i ∈ s, (a i : ℚ) * f i) =
        ∑ i ∈ s, (a i : ZMod p) * palindromicRatResidue p (f i) := by
  have hterm : ∀ i ∈ s, (((a i : ℚ) * f i).den : ZMod p) ≠ 0 :=
    fun i hi => (rational_residue_mul (by simp) (hf i hi)).1
  refine ⟨(rational_residue_sum s _ hterm).1, ?_⟩
  rw [palindromicRatResidue_sum s _ hterm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [palindromicRatResidue_mul (by simp) (hf i hi), palindromicRatResidue_intCast]

theorem fixed_rawEntryRat_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r j : ℕ) (hj : j < p) :
    palindromicRatResidue p (rawEntryRat 0 1 r j) =
      (∑ i ∈ Finset.range (H 1), ((rowP 1 r).coeff i : ZMod p) *
        palindromicRatResidue p (momentRat i j)) -
      (3 / 2 : ZMod p) *
        ∑ i ∈ Finset.range (H 1), ((rowD 1 r).coeff i : ZMod p) *
          palindromicRatResidue p (zetaRat i j) := by
  have hM := palindromicRatResidue_int_sum (p := p) (Finset.range (H 1))
    (fun i => (rowP 1 r).coeff i) (fun i => momentRat i j) (by
      intro i hi
      exact momentRat_odd_prime_small_den_ne_zero (by omega)
        (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj)
  have hZ := palindromicRatResidue_int_sum (p := p) (Finset.range (H 1))
    (fun i => (rowD 1 r).coeff i) (fun i => zetaRat i j) (by
      intro i hi
      exact zetaRat_small_den_ne_zero
        (by have := Finset.mem_range.mp hi; simp only [H] at this; omega) hj)
  rw [rawEntryRat_zero,
    palindromicRatResidue_sub hM.1
      (rational_residue_mul (fixed_three_halves_den hp) hZ.1).1,
    palindromicRatResidue_mul (fixed_three_halves_den hp) hZ.1, hM.2, hZ.2]
  have hthree : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := by
    norm_num [palindromicRatResidue]
  rw [hthree]

theorem filterCoeffRat_residue (p N v : ℕ) [Fact p.Prime] :
    palindromicRatResidue p (filterCoeffRat N v) =
      (-1 : ZMod p) ^ v * ((q N).choose v : ZMod p) := by
  simpa [filterCoeffRat] using
    palindromicRatResidue_intCast p ((-1 : ℤ) ^ v * ((q N).choose v : ℤ))

theorem fixedBaseEntryRat_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r : Fin 49) (k : Fin 48) :
    ((fixedBaseEntryRat r k).den : ZMod p) ≠ 0 := by
  unfold fixedBaseEntryRat filteredEntryRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  apply (rational_residue_mul (filterCoeffRat_den_ne_zero 1 v) ?_).1
  apply fixed_rawEntryRat_den_ne_zero hp
  have hk := k.isLt
  have hv' := Finset.mem_range.mp hv
  simp only [q, b] at hv' ⊢
  omega

theorem fixedB0_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) : ((fixedB0 r k).den : ZMod p) ≠ 0 :=
  fixedBaseEntryRat_den_ne_zero hp r.castSucc k

theorem fixedB1_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) : ((fixedB1 r k).den : ZMod p) ≠ 0 :=
  fixedBaseEntryRat_den_ne_zero hp r.succ k

theorem fixedBaseEntryRat_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r : Fin 49) (k : Fin 48) :
    palindromicRatResidue p (fixedBaseEntryRat r k) =
      ∑ v ∈ Finset.range (q 1 + 1),
        ((-1 : ZMod p) ^ v * ((q 1).choose v : ZMod p)) *
          palindromicRatResidue p (rawEntryRat 0 1 r.val (b 1 + k.val + v)) := by
  have hraw : ∀ v ∈ Finset.range (q 1 + 1),
      ((rawEntryRat 0 1 r.val (b 1 + k.val + v)).den : ZMod p) ≠ 0 := by
    intro v hv
    apply fixed_rawEntryRat_den_ne_zero hp
    have hk := k.isLt
    have hv' := Finset.mem_range.mp hv
    simp only [q, b] at hv' ⊢
    omega
  unfold fixedBaseEntryRat filteredEntryRat
  rw [palindromicRatResidue_sum _ _ (fun v hv =>
    (rational_residue_mul (filterCoeffRat_den_ne_zero 1 v) (hraw v hv)).1)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [palindromicRatResidue_mul (filterCoeffRat_den_ne_zero 1 v) (hraw v hv),
    filterCoeffRat_residue]

theorem fixedMatrix_one_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) :
    palindromicRatResidue p (fixedMatrix 1 r k) =
      fixedB0Residue p r k + fixedB1Residue p r k := by
  rw [fixedMatrix_one]
  exact palindromicRatResidue_add (fixedB0_den_ne_zero hp r k)
    (fixedB1_den_ne_zero hp r k)

theorem fixedMatrix_neg_one_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : Fin 48) :
    palindromicRatResidue p (fixedMatrix (-1) r k) =
      fixedB0Residue p r k - fixedB1Residue p r k := by
  rw [fixedMatrix_neg_one]
  exact palindromicRatResidue_sub (fixedB0_den_ne_zero hp r k)
    (fixedB1_den_ne_zero hp r k)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker

def palindromicScaledResidueMatrix (z : ℚ) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicRatResidue p
    ((p : ℚ) ^ 2 * filteredEntryRat z p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val))

def palindromicResidueBlockMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicTransitionMatrix p k.1 r.1 * fixedB0Residue p r.2 k.2 +
    palindromicReversedTransitionMatrix p k.1 r.1 * fixedB1Residue p r.2 k.2

theorem palindromicResidueBlockMatrix_kronecker (p : ℕ) [Fact p.Prime] :
    palindromicResidueBlockMatrix p =
      (palindromicTransitionMatrix p)ᵀ ⊗ₖ fixedB0Residue p +
        (palindromicReversedTransitionMatrix p)ᵀ ⊗ₖ fixedB1Residue p := by
  ext r k
  rfl


def palindromicReducedBlockMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  (1 : Matrix (Fin p) (Fin p) (ZMod p)) ⊗ₖ fixedB0Residue p +
    (palindromicReversalMatrix p)ᵀ ⊗ₖ fixedB1Residue p

theorem palindromicReversedTransitionMatrix_transpose (p : ℕ) :
    (palindromicReversedTransitionMatrix p)ᵀ =
      (palindromicReversalMatrix p)ᵀ * (palindromicTransitionMatrix p)ᵀ := by
  rw [palindromicReversedTransitionMatrix, Matrix.transpose_mul]

theorem palindromicResidueBlockMatrix_factor (p : ℕ) [Fact p.Prime] :
    palindromicResidueBlockMatrix p = palindromicReducedBlockMatrix p *
      ((palindromicTransitionMatrix p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p))) := by
  rw [palindromicResidueBlockMatrix_kronecker, palindromicReducedBlockMatrix,
    Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    ← palindromicReversedTransitionMatrix_transpose]




theorem det_palindromicResidueBlockMatrix {p : ℕ} [Fact p.Prime] :
    (palindromicResidueBlockMatrix p).det =
      (palindromicTransitionMatrix p).det ^ 48 *
        (palindromicReducedBlockMatrix p).det := by
  rw [palindromicResidueBlockMatrix_factor, Matrix.det_mul, Matrix.det_kronecker,
    Matrix.det_transpose, Matrix.det_one, one_pow, mul_one]
  simpa using mul_comm (palindromicReducedBlockMatrix p).det
    ((palindromicTransitionMatrix p).det ^ 48)

theorem det_palindromicResidueBlockMatrix_ne_zero_iff {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicResidueBlockMatrix p).det ≠ 0 ↔
      (palindromicReducedBlockMatrix p).det ≠ 0 := by
  rw [det_palindromicResidueBlockMatrix]
  exact mul_ne_zero_iff.trans
    (and_iff_right (pow_ne_zero 48 (det_palindromicTransitionMatrix_ne_zero hp2)))

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker

def palindromicReducedBlockRightInverse (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  (palindromicReversalProjZero p)ᵀ ⊗ₖ (fixedB0Residue p)⁻¹ +
    (palindromicReversalProjPlus p)ᵀ ⊗ₖ (fixedB0Residue p + fixedB1Residue p)⁻¹ +
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ (fixedB0Residue p - fixedB1Residue p)⁻¹

theorem palindromicReducedBlock_mul_projZero {p : ℕ} [Fact p.Prime]
    (h0 : (fixedB0Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p *
        ((palindromicReversalProjZero p)ᵀ ⊗ₖ (fixedB0Residue p)⁻¹) =
      (palindromicReversalProjZero p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p)) := by
  have hp0 : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjZero p)ᵀ = 0 := by
    rw [← Matrix.transpose_mul, palindromicReversalProjZero_mul_matrix, Matrix.transpose_zero]
  rw [palindromicReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hp0, Matrix.zero_kronecker, add_zero,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h0)]

theorem palindromicReducedBlock_mul_projPlus {p : ℕ} [Fact p.Prime]
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p *
        ((palindromicReversalProjPlus p)ᵀ ⊗ₖ
          (fixedB0Residue p + fixedB1Residue p)⁻¹) =
      (palindromicReversalProjPlus p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p)) := by
  have hpp : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjPlus p)ᵀ =
      (palindromicReversalProjPlus p)ᵀ := by
    rw [← Matrix.transpose_mul, palindromicReversalProjPlus_mul_matrix]
  rw [palindromicReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hpp, ← Matrix.kronecker_add, ← Matrix.add_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hplus)]

theorem palindromicReducedBlock_mul_projMinus {p : ℕ} [Fact p.Prime]
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p *
        ((palindromicReversalProjMinus p)ᵀ ⊗ₖ
          (fixedB0Residue p - fixedB1Residue p)⁻¹) =
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ
        (1 : Matrix (Fin 48) (Fin 48) (ZMod p)) := by
  have hpm : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjMinus p)ᵀ =
      -(palindromicReversalProjMinus p)ᵀ := by
    rw [← Matrix.transpose_mul, palindromicReversalProjMinus_mul_matrix, Matrix.transpose_neg]
  rw [palindromicReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hpm]
  have hcombine (C : Matrix (Fin 48) (Fin 48) (ZMod p)) :
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ (fixedB0Residue p * C) +
        (-(palindromicReversalProjMinus p)ᵀ) ⊗ₖ (fixedB1Residue p * C) =
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ ((fixedB0Residue p - fixedB1Residue p) * C) := by
    rw [Matrix.sub_mul]
    ext ⟨i, r⟩ ⟨j, k⟩
    simp only [Matrix.add_apply, Matrix.kronecker_apply, Matrix.neg_apply, Matrix.sub_apply]
    ring
  rw [hcombine, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hminus)]

theorem palindromicReducedBlock_mul_rightInverse {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    palindromicReducedBlockMatrix p * palindromicReducedBlockRightInverse p = 1 := by
  rw [palindromicReducedBlockRightInverse, Matrix.mul_add, Matrix.mul_add,
    palindromicReducedBlock_mul_projZero h0, palindromicReducedBlock_mul_projPlus hplus,
    palindromicReducedBlock_mul_projMinus hminus,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.transpose_add, ← Matrix.transpose_add,
    palindromicReversalProjections_sum hp2, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem det_palindromicReducedBlockMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicReducedBlockMatrix p).det ≠ 0 := by
  have hd := congrArg Matrix.det (palindromicReducedBlock_mul_rightInverse hp2 h0 hplus hminus)
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact left_ne_zero_of_mul_eq_one hd

theorem det_palindromicResidueBlockMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicResidueBlockMatrix p).det ≠ 0 :=
  (det_palindromicResidueBlockMatrix_ne_zero_iff hp2).mpr
    (det_palindromicReducedBlockMatrix_ne_zero_of_fixed hp2 h0 hplus hminus)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeExtractionIndices
namespace OAI


namespace InternalCatalan

def oddPrimeDigitRemainder (p i j : ℕ) : ℕ :=
  (((j : ℤ) - (i : ℤ) - 1) % (p : ℤ)).toNat

def oddPrimeDigitRow (p i j : ℕ) : ℤ :=
  ((i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ)) /
    (p : ℤ) - 1

theorem oddPrimeDigitRemainder_lt {p i j : ℕ} (hp : 0 < p) :
    oddPrimeDigitRemainder p i j < p := by
  unfold oddPrimeDigitRemainder
  have hpz : 0 < (p : ℤ) := by omega
  have hlo := Int.emod_nonneg ((j : ℤ) - (i : ℤ) - 1) (by omega : (p : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos ((j : ℤ) - (i : ℤ) - 1) hpz
  omega

theorem oddPrimeDigitRemainder_of_le {p i j : ℕ} (hp : 0 < p) (hji : j ≤ i) :
    oddPrimeDigitRemainder p i j = p - 1 - (i - j) % p := by
  have hx : (j : ℤ) - (i : ℤ) - 1 = Int.negSucc (i - j) := by omega
  have hr : (i - j) % p < p := Nat.mod_lt _ hp
  unfold oddPrimeDigitRemainder
  rw [hx, Int.negSucc_emod (i - j) (by omega : 0 < (p : ℤ)),
    ← Int.natCast_emod]
  omega

theorem oddPrimeDigitRemainder_of_lt {p i j : ℕ} (_hp : 0 < p) (hij : i < j) :
    oddPrimeDigitRemainder p i j = (j - i - 1) % p := by
  have hx : (j : ℤ) - (i : ℤ) - 1 = ((j - i - 1 : ℕ) : ℤ) := by omega
  unfold oddPrimeDigitRemainder
  rw [hx, ← Int.natCast_emod, Int.toNat_natCast]

private theorem digit_numerator_of_le {p i j : ℕ} (hp : 0 < p) (hji : j ≤ i) :
    (i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ) =
      (p : ℤ) * ((((i - j) / p : ℕ) : ℤ) + ((j / p : ℕ) : ℤ) + 1) := by
  have hr : (i - j) % p < p := Nat.mod_lt _ hp
  have hrem : ((p - 1 - (i - j) % p : ℕ) : ℤ) =
      (p : ℤ) - 1 - (((i - j) % p : ℕ) : ℤ) := by omega
  have hk : (((i - j) % p : ℕ) : ℤ) + (p : ℤ) * (((i - j) / p : ℕ) : ℤ) =
      ((i - j : ℕ) : ℤ) := by exact_mod_cast Nat.mod_add_div (i - j) p
  have hj : ((j % p : ℕ) : ℤ) + (p : ℤ) * ((j / p : ℕ) : ℤ) = (j : ℤ) := by
    exact_mod_cast Nat.mod_add_div j p
  have hsub : ((i - j : ℕ) : ℤ) = (i : ℤ) - (j : ℤ) := by omega
  rw [oddPrimeDigitRemainder_of_le hp hji, hrem]
  nlinarith

private theorem digit_numerator_of_lt {p i j : ℕ} (hp : 0 < p) (hij : i < j) :
    (i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ) =
      (p : ℤ) * (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ)) := by
  have hk : (((j - i - 1) % p : ℕ) : ℤ) +
      (p : ℤ) * (((j - i - 1) / p : ℕ) : ℤ) = ((j - i - 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.mod_add_div (j - i - 1) p
  have hj : ((j % p : ℕ) : ℤ) + (p : ℤ) * ((j / p : ℕ) : ℤ) = (j : ℤ) := by
    exact_mod_cast Nat.mod_add_div j p
  have hsub : ((j - i - 1 : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) - 1 := by omega
  rw [oddPrimeDigitRemainder_of_lt hp hij]
  nlinarith


theorem oddPrimeDigitRow_of_le {p i j : ℕ} (hp : 0 < p) (hji : j ≤ i) :
    oddPrimeDigitRow p i j = (((i - j) / p : ℕ) : ℤ) + ((j / p : ℕ) : ℤ) := by
  unfold oddPrimeDigitRow
  rw [digit_numerator_of_le hp hji,
    Int.mul_ediv_cancel_left _ (by omega : (p : ℤ) ≠ 0)]
  omega

theorem oddPrimeDigitRow_of_lt {p i j : ℕ} (hp : 0 < p) (hij : i < j) :
    oddPrimeDigitRow p i j = ((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1 := by
  unfold oddPrimeDigitRow
  rw [digit_numerator_of_lt hp hij,
    Int.mul_ediv_cancel_left _ (by omega : (p : ℤ) ≠ 0)]






theorem oddPrimeExtractionIndices_unique {p i k ell d v : ℕ}
    (hp : 0 < p) (hell : ell < p) (hd : d < p)
    (hindex : i + 1 + d = v * p + ell) :
    d = oddPrimeDigitRemainder p i (k * p + ell) ∧
      oddPrimeDigitRow p i (k * p + ell) = (v : ℤ) - 1 := by
  have hcast : (i : ℤ) + 1 + (d : ℤ) = (v : ℤ) * (p : ℤ) + (ell : ℤ) := by
    exact_mod_cast hindex
  have hdiff : ((k * p + ell : ℕ) : ℤ) - (i : ℤ) - 1 =
      (d : ℤ) + ((k : ℤ) - (v : ℤ)) * (p : ℤ) := by
    push_cast
    nlinarith [hcast]
  have hrem : oddPrimeDigitRemainder p i (k * p + ell) = d := by
    unfold oddPrimeDigitRemainder
    rw [hdiff, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (Int.natCast_nonneg d) (by exact_mod_cast hd),
      Int.toNat_natCast]
  have hcol : (k * p + ell) % p = ell := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hell]
  refine ⟨hrem.symm, ?_⟩
  unfold oddPrimeDigitRow
  rw [hrem, hcol]
  have hnum : (i : ℤ) + 1 + (d : ℤ) - (ell : ℤ) = (p : ℤ) * (v : ℤ) := by
    nlinarith [hcast]
  rw [hnum, Int.mul_ediv_cancel_left _ (by omega : (p : ℤ) ≠ 0)]

theorem oddPrimeExtractionIndices_exists {p H i k ell : ℕ}
    (hp : 0 < p) (hell : ell < p) (hi : i < H) :
    ∃ v ∈ Finset.range (H + 1),
      i + 1 + oddPrimeDigitRemainder p i (k * p + ell) = v * p + ell ∧
        oddPrimeDigitRow p i (k * p + ell) = (v : ℤ) - 1 := by
  by_cases hle : ell ≤ i
  · let v : ℕ := (i - ell) / p + 1
    let d : ℕ := p - 1 - (i - ell) % p
    have hr : (i - ell) % p < p := Nat.mod_lt _ hp
    have hd : d < p := by dsimp only [d]; omega
    have hquot := Nat.mod_add_div (i - ell) p
    have hsub : i - ell + ell = i := Nat.sub_add_cancel hle
    have hdigit : (i - ell) % p + d + 1 = p := by dsimp only [d]; omega
    have hindex : i + 1 + d = v * p + ell := by
      dsimp only [v]
      nlinarith [hquot, hsub, hdigit]
    have hv : v < H + 1 := by
      have hdiv : (i - ell) / p ≤ i - ell := Nat.div_le_self (i - ell) p
      dsimp only [v]
      omega
    have hunique := oddPrimeExtractionIndices_unique (k := k) hp hell hd hindex
    refine ⟨v, Finset.mem_range.mpr hv, ?_, hunique.2⟩
    rw [← hunique.1]
    exact hindex
  · let d : ℕ := ell - i - 1
    have hd : d < p := by dsimp only [d]; omega
    have hindex : i + 1 + d = 0 * p + ell := by dsimp only [d]; omega
    have hunique := oddPrimeExtractionIndices_unique (k := k) hp hell hd hindex
    refine ⟨0, by simp, ?_, hunique.2⟩
    rw [← hunique.1]
    exact hindex

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeGeneralExtraction
namespace OAI


namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem polynomial_eq_sum_range_of_coeff_ge_eq_zero {R : Type*} [CommSemiring R]
    (P : R[X]) (H : ℕ) (hP : ∀ i, H ≤ i → P.coeff i = 0) :
    P = ∑ i ∈ Finset.range H, C (P.coeff i) * X ^ i := by
  ext n
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hn : n < H
  · simp [Finset.mem_range, hn]
  · simp [Finset.mem_range, hn, hP n (by omega)]

theorem oddPrimeExtraction_coeff {p H : ℕ} (hp : 0 < p)
    (P : (ZMod p)[X]) (hP : ∀ i, H ≤ i → P.coeff i = 0) (n : ℕ) :
    (X * P * oddPrimeWeight p).coeff n =
      ∑ i ∈ Finset.range H, ∑ d ∈ Finset.range p,
        if n = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0 := by
  have hPexp := polynomial_eq_sum_range_of_coeff_ge_eq_zero P H hP
  have hEexp := polynomial_eq_sum_range_of_coeff_ge_eq_zero (oddPrimeWeight p) p
    (fun d hd => oddPrimeWeight_coeff_eq_zero_of_ge hp hd)
  have hXp : X * P = ∑ i ∈ Finset.range H, C (P.coeff i) * X ^ (i + 1) := by
    calc
      X * P = X * (∑ i ∈ Finset.range H, C (P.coeff i) * X ^ i) :=
        congrArg (fun Q : (ZMod p)[X] => X * Q) hPexp
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        ring
  have hpoly : X * P * oddPrimeWeight p =
      ∑ i ∈ Finset.range H, ∑ d ∈ Finset.range p,
        C (P.coeff i * (oddPrimeWeight p).coeff d) * X ^ (i + 1 + d) := by
    calc
      X * P * oddPrimeWeight p =
          (∑ i ∈ Finset.range H, C (P.coeff i) * X ^ (i + 1)) * oddPrimeWeight p :=
        congrArg (fun Q : (ZMod p)[X] => Q * oddPrimeWeight p) hXp
      _ = ∑ i ∈ Finset.range H,
          (C (P.coeff i) * X ^ (i + 1)) * oddPrimeWeight p := by rw [Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = (C (P.coeff i) * X ^ (i + 1)) *
              (∑ d ∈ Finset.range p, C ((oddPrimeWeight p).coeff d) * X ^ d) :=
            congrArg (fun Q : (ZMod p)[X] => (C (P.coeff i) * X ^ (i + 1)) * Q) hEexp
          _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            rw [map_mul, pow_add X (i + 1) d]
            ring
  rw [hpoly]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]

theorem oddPrime_P_coefficient_contraction {p B k ell : ℕ}
    (hp : 0 < p) (hell : ell < p) (P : (ZMod p)[X])
    (hP : ∀ i, B * p ≤ i → P.coeff i = 0) (f : ℤ → ZMod p) :
    (∑ i ∈ Finset.range (B * p),
      P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
        f (oddPrimeDigitRow p i (k * p + ell))) =
      ∑ v ∈ Finset.range (B + 1),
        (X * P * oddPrimeWeight p).coeff (v * p + ell) * f ((v : ℤ) - 1) := by
  have hsingle (i : ℕ) (hi : i ∈ Finset.range (B * p)) :
      (∑ d ∈ Finset.range p, ∑ v ∈ Finset.range (B + 1),
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1)) =
        P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
          f (oddPrimeDigitRow p i (k * p + ell)) := by
    obtain ⟨v₀, hv₀loose, hindex, hrow⟩ :=
      oddPrimeExtractionIndices_exists (k := k) hp hell (Finset.mem_range.mp hi)
    have hdigit : oddPrimeDigitRemainder p i (k * p + ell) < p :=
      oddPrimeDigitRemainder_lt hp
    have hv₀ : v₀ ∈ Finset.range (B + 1) := by
      apply Finset.mem_range.mpr
      by_contra hnot
      have hle : B + 1 ≤ v₀ := by omega
      have hmul := Nat.mul_le_mul_right p hle
      have hi' := Finset.mem_range.mp hi
      nlinarith
    rw [Finset.sum_eq_single (oddPrimeDigitRemainder p i (k * p + ell))]
    · rw [Finset.sum_eq_single v₀]
      · rw [hindex, if_pos rfl, hrow]
      · intro v hv hne
        have hneq : v * p + ell ≠ i + 1 + oddPrimeDigitRemainder p i (k * p + ell) := by
          intro heq
          have hu := oddPrimeExtractionIndices_unique (k := k) hp hell hdigit heq.symm
          have hvEq : v = v₀ := by have h := hu.2; omega
          exact hne hvEq
        simp only [if_neg hneq, zero_mul]
      · intro hnot
        exact (hnot hv₀).elim
    · intro d hd hne
      apply Finset.sum_eq_zero
      intro v hv
      have hneq : v * p + ell ≠ i + 1 + d := by
        intro heq
        exact hne (oddPrimeExtractionIndices_unique (k := k) hp hell
          (Finset.mem_range.mp hd) heq.symm).1
      simp only [if_neg hneq, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hdigit)).elim
  calc
    _ = ∑ i ∈ Finset.range (B * p), ∑ d ∈ Finset.range p, ∑ v ∈ Finset.range (B + 1),
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hsingle i hi).symm
    _ = ∑ i ∈ Finset.range (B * p), ∑ v ∈ Finset.range (B + 1), ∑ d ∈ Finset.range p,
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ v ∈ Finset.range (B + 1), ∑ i ∈ Finset.range (B * p), ∑ d ∈ Finset.range p,
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [oddPrimeExtraction_coeff hp P hP]
      simp only [Finset.sum_mul]

end InternalCatalan



namespace InternalCatalan

open Polynomial
open scoped BigOperators


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeEvenBlockPartition
namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem evenBlock_quotient_parity {p z : ℕ}
    (hp : p % 2 = 1) (hz : z % 2 = 0) :
    (z / p) % 2 = (z % p) % 2 := by
  have he := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div z p)
  rw [Nat.add_mod, Nat.mul_mod, hp, one_mul, hz] at he
  simp only [Nat.mod_mod] at he
  omega

private theorem evenBlock_bounds {p a j : ℕ} (hp : p % 2 = 1)
    (hj : j < (p - 1) / 2 + 1) :
    (2 * a + 1) * p < 2 * (a + 1) * p - 2 * j ∧
      2 * (a + 1) * p - 2 * j ≤ 2 * (a + 1) * p := by
  have hjp : 2 * j < p := by omega
  have he : (2 * a + 1) * p + p = 2 * (a + 1) * p := by ring
  constructor <;> omega

private theorem evenBlock_survives {p a j : ℕ} (hp : p % 2 = 1)
    (hj : j < (p - 1) / 2 + 1) :
    0 < 2 * (a + 1) * p - 2 * j ∧
      (2 * (a + 1) * p - 2 * j) % 2 = 0 ∧
        ((2 * (a + 1) * p - 2 * j) % p = 0 ∨
          ((2 * (a + 1) * p - 2 * j) % p) % 2 = 1) := by
  have hb := evenBlock_bounds (a := a) hp hj
  have hmeven : (2 * (a + 1) * p) % 2 = 0 := by simp [Nat.mul_mod]
  have hjp : 2 * j < p := by omega
  refine ⟨by omega, by omega, ?_⟩
  by_cases hj0 : j = 0
  · left
    simp [hj0]
  · right
    have hr : p - 2 * j < p := by omega
    have he : (2 * a + 1) * p + p = 2 * (a + 1) * p := by ring
    have hz : 2 * (a + 1) * p - 2 * j =
        (2 * a + 1) * p + (p - 2 * j) := by omega
    have hmod : (2 * (a + 1) * p - 2 * j) % p = p - 2 * j := by
      rw [hz]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    rw [hmod]
    omega

private theorem evenBlock_injective {p a b i j : ℕ} (hp : p % 2 = 1)
    (hi : i < (p - 1) / 2 + 1) (hj : j < (p - 1) / 2 + 1)
    (he : 2 * (a + 1) * p - 2 * i = 2 * (b + 1) * p - 2 * j) :
    a = b ∧ i = j := by
  have ha := evenBlock_bounds (a := a) hp hi
  have hb := evenBlock_bounds (a := b) hp hj
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · have hm := Nat.mul_le_mul_right p (show 2 * (a + 1) ≤ 2 * b + 1 by omega)
      omega
    · exact h
    · have hm := Nat.mul_le_mul_right p (show 2 * (b + 1) ≤ 2 * a + 1 by omega)
      omega
  subst b
  exact ⟨rfl, by omega⟩

private theorem evenBlock_preimage {p u z : ℕ} (hp : p % 2 = 1)
    (hu : u % 2 = 0) (hur : (u % p) % 2 = 0)
    (hz0 : 0 < z) (hzu : z ≤ u) (hz : z % 2 = 0)
    (hr : z % p = 0 ∨ (z % p) % 2 = 1) :
    ∃ a < (u / p) / 2, ∃ j < (p - 1) / 2 + 1,
      2 * (a + 1) * p - 2 * j = z := by
  have hp0 : 0 < p := by omega
  have huq : (u / p) % 2 = 0 := by
    rw [evenBlock_quotient_parity hp hu, hur]
  have hzq := evenBlock_quotient_parity hp hz
  have hquot : z / p ≤ u / p := Nat.div_le_div_right hzu
  have hdecomp : z % p + (z / p) * p = z := by
    simpa only [Nat.mul_comm p (z / p)] using Nat.mod_add_div z p
  rcases hr with hr0 | hr1
  · have hqe : (z / p) % 2 = 0 := by simpa [hr0] using hzq
    have hq0 : 0 < z / p := by
      by_cases hq : z / p = 0
      · simp [hr0, hq] at hdecomp
        omega
      · exact Nat.pos_of_ne_zero hq
    refine ⟨z / p / 2 - 1, by omega, 0, by omega, ?_⟩
    have ha : 2 * (z / p / 2 - 1 + 1) = z / p := by omega
    rw [ha]
    simp only [mul_zero, Nat.sub_zero]
    omega
  · have hqo : (z / p) % 2 = 1 := by omega
    have hrlt : z % p < p := Nat.mod_lt z hp0
    have hrpos : 0 < z % p := by omega
    refine ⟨z / p / 2, by omega, (p - z % p) / 2, by omega, ?_⟩
    have ha : 2 * (z / p / 2 + 1) = z / p + 1 := by omega
    have hj : 2 * ((p - z % p) / 2) = p - z % p := by omega
    rw [ha, hj, Nat.add_mul, one_mul]
    omega

theorem even_surviving_sum_eq_complete_blocks {β : Type*} [AddCommMonoid β]
    {p u : ℕ} (hp : p % 2 = 1) (hu : u % 2 = 0)
    (hur : (u % p) % 2 = 0) (f : ℕ → β) :
    (∑ z ∈ (Finset.range (u + 1)).filter
        (fun z => 0 < z ∧ z % 2 = 0 ∧ (z % p = 0 ∨ (z % p) % 2 = 1)), f z) =
      ∑ a ∈ Finset.range ((u / p) / 2),
        ∑ j ∈ Finset.range ((p - 1) / 2 + 1), f (2 * (a + 1) * p - 2 * j) := by
  classical
  have huq : (u / p) % 2 = 0 := by
    rw [evenBlock_quotient_parity hp hu, hur]
  rw [← Finset.sum_product (Finset.range ((u / p) / 2))
    (Finset.range ((p - 1) / 2 + 1))
    (fun x : ℕ × ℕ => f (2 * (x.1 + 1) * p - 2 * x.2))]
  symm
  refine Finset.sum_bij (fun x _ => 2 * (x.1 + 1) * p - 2 * x.2) ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_product.mp hx with ⟨ha, hj⟩
    have ha' := Finset.mem_range.mp ha
    have hj' := Finset.mem_range.mp hj
    have hm : 2 * (x.1 + 1) ≤ u / p := by omega
    have hmp := (Nat.mul_le_mul_right p hm).trans (Nat.div_mul_le_self u p)
    have hb := evenBlock_bounds (a := x.1) hp hj'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      evenBlock_survives (a := x.1) hp hj'⟩
  · intro x hx y hy he
    have hjx := Finset.mem_range.mp (Finset.mem_product.mp hx).2
    have hjy := Finset.mem_range.mp (Finset.mem_product.mp hy).2
    have hxy := evenBlock_injective hp hjx hjy he
    exact Prod.ext hxy.1 hxy.2
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzu, hz0, hzEven, hr⟩
    obtain ⟨a, ha, j, hj, he⟩ := evenBlock_preimage hp hu hur hz0
      (by have := Finset.mem_range.mp hzu; omega) hzEven hr
    refine ⟨(a, j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hj⟩, he⟩
  · intro x hx
    rfl

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimePlusStartingDigits
namespace OAI


namespace InternalCatalan

theorem centralCoeff_half_prime_reduced_residue {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    ((centralCoeff ((p - 1) / 2)).den : ZMod p) ≠ 0 ∧
      ((centralCoeff ((p - 1) / 2)).num : ZMod p) /
        ((centralCoeff ((p - 1) / 2)).den : ZMod p) =
          (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hk : 2 * ((p - 1) / 2) < p := by omega
  have hc := centralCoeff_reduced_residue hp2 ((p - 1) / 2)
  refine ⟨hc.1, ?_⟩
  rw [hc.2]
  simpa using (oddPrimeWeight_centralCoeff_identity hp2 hk).symm

theorem boundaryFactor_odd_multiple_reduction {p P : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hPOdd : P % 2 = 1) (hP : P < p) :
    (((p : ℚ) * boundaryFactor (P * p)).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor P).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * boundaryFactor (P * p)).num : ZMod p) /
          (((p : ℚ) * boundaryFactor (P * p)).den : ZMod p) =
            (-1 : ZMod p) ^ ((p - 1) / 2) *
              (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by
  let A : ℕ := (P - 1) / 2
  let s : ℕ := (p - 1) / 2
  let l : ℕ := p * A + s
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hPpos : 0 < P := by omega
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hA : 2 * A + 1 = P := by dsimp [A]; omega
  have hs : 2 * s + 1 = p := by dsimp [s]; omega
  have hslt : s < p := by omega
  have hl : 2 * l + 1 = P * p := by dsimp [l]; nlinarith
  have hlmod : l % p = s := by
    dsimp only [l]
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hslt]
  have hldiv : l / p = A := by
    dsimp only [l]
    rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hslt, add_zero]
  have hncarry : 2 * (l % p) < p := by rw [hlmod]; omega
  have hcl := centralCoeff_digit_no_carry hp2 hncarry
  have hsign := centralCoeff_half_prime_reduced_residue (p := p) hp2
  have hsignR : R (centralCoeff s) = (-1 : ZMod p) ^ s := hsign.2
  have hsplit : R (centralCoeff l) = R (centralCoeff A) * (-1 : ZMod p) ^ s := by
    have hsplitR : R (centralCoeff l) = R (centralCoeff A) * R (centralCoeff s) := by
      simpa only [R, hldiv, hlmod] using hcl.2.2.2
    rw [hsignR] at hsplitR
    exact hsplitR
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hPpos)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hPval : padicValRat p (P : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hPpos hP)]
    norm_num
  have hcAval : padicValRat p (centralCoeff A) = 0 :=
    centralCoeff_odd_prime_valuation_zero_of_lt hp.out hp2 (by omega)
  have hclval : padicValRat p (centralCoeff l) = 0 := by
    have hbound : 2 * l < p ^ 2 := by nlinarith [hp.out.pos]
    rw [centralCoeff_odd_prime_single_carry hp.out hp2 hbound,
      if_neg (by omega : ¬p ≤ 2 * (l % p))]
  have hprodAval : padicValRat p ((P : ℚ) * centralCoeff A) = 0 := by
    rw [padicValRat.mul hPq (centralCoeff_ne_zero A), hPval, hcAval, add_zero]
  have hprodlval : padicValRat p ((P : ℚ) * centralCoeff l) = 0 := by
    rw [padicValRat.mul hPq (centralCoeff_ne_zero l), hPval, hclval, add_zero]
  have hinvA := rational_residue_inv (mul_ne_zero hPq (centralCoeff_ne_zero A)) hprodAval
  have hinvl := rational_residue_inv (mul_ne_zero hPq (centralCoeff_ne_zero l)) hprodlval
  have hinvAR : R (((P : ℚ) * centralCoeff A)⁻¹) =
      (R ((P : ℚ) * centralCoeff A))⁻¹ := hinvA.2
  have hinvlR : R (((P : ℚ) * centralCoeff l)⁻¹) =
      (R ((P : ℚ) * centralCoeff l))⁻¹ := hinvl.2
  have hmulA := rational_residue_mul (a := (P : ℚ)) (b := centralCoeff A)
    (by simp) (centralCoeff_reduced_residue (p := p) hp2 A).1
  have hmull := rational_residue_mul (a := (P : ℚ)) (b := centralCoeff l)
    (by simp) (centralCoeff_reduced_residue (p := p) hp2 l).1
  have hRA : R ((P : ℚ) * centralCoeff A) = (P : ZMod p) * R (centralCoeff A) := by
    simpa [R] using hmulA.2
  have hRl : R ((P : ℚ) * centralCoeff l) = (P : ZMod p) * R (centralCoeff l) := by
    simpa [R] using hmull.2
  have hboundaryA : boundaryFactor P = ((P : ℚ) * centralCoeff A)⁻¹ := by
    have heq := boundaryFactor_odd A
    rw [hA, one_div] at heq
    exact heq
  have hboundaryl : (p : ℚ) * boundaryFactor (P * p) =
      ((P : ℚ) * centralCoeff l)⁻¹ := by
    have heq := boundaryFactor_odd l
    rw [hl] at heq
    rw [heq, Nat.cast_mul]
    field_simp [hPq, hpq, centralCoeff_ne_zero l]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hboundaryl] using hinvl.1
  · simpa only [hboundaryA] using hinvA.1
  · change R ((p : ℚ) * boundaryFactor (P * p)) = (-1 : ZMod p) ^ s * R (boundaryFactor P)
    rw [hboundaryl, hboundaryA]
    rw [hinvlR, hinvAR, hRl, hRA, hsplit]
    simp only [mul_inv_rev]
    ring_nf
    norm_num
    ring





theorem boundaryFactor_odd_even_digit_reduction {p P k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hPOdd : P % 2 = 1) (hP : P < p) (hk : 2 * k < p) :
    (((p : ℚ) * boundaryFactor (P * p + 2 * k)).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor P).den : ZMod p) ≠ 0 ∧
        ((centralCoeff k).den : ZMod p) ≠ 0 ∧
          (((p : ℚ) * boundaryFactor (P * p + 2 * k)).num : ZMod p) /
            (((p : ℚ) * boundaryFactor (P * p + 2 * k)).den : ZMod p) =
              (-1 : ZMod p) ^ ((p - 1) / 2) *
                (((centralCoeff k).num : ZMod p) / ((centralCoeff k).den : ZMod p)) *
                  (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hbase := boundaryFactor_odd_multiple_reduction hp2 hPOdd hP
  have hden : ∀ u : ℕ, 2 * u < p →
      (((p : ℚ) * boundaryFactor (P * p + 2 * u)).den : ZMod p) ≠ 0 := by
    intro u hu
    have hodd : (P * p + 2 * u) % 2 = 1 := by
      simp [Nat.add_mod, Nat.mul_mod, hPOdd, hpOdd]
    have hmul := Nat.mul_le_mul_right p (show P + 1 ≤ p by omega)
    have hsmall : P * p + 2 * u < p ^ 2 := by nlinarith
    exact (boundaryFactor_odd_integral_denominators hp2 hodd hsmall).2
  have hcden : ∀ u : ℕ, ((centralCoeff u).den : ZMod p) ≠ 0 :=
    fun u => (centralCoeff_reduced_residue hp2 u).1
  refine ⟨hden k hk, hbase.2.1, hcden k, ?_⟩
  revert hk
  induction k with
  | zero =>
    intro hk
    simpa using hbase.2.2
  | succ k ih =>
    intro hk
    have hkprev : 2 * k < p := by omega
    have hzstep :
        (((P * p + 2 * k + 2 : ℕ) : ℚ)) *
            ((p : ℚ) * boundaryFactor (P * p + 2 * (k + 1))) =
          (((P * p + 2 * k + 1 : ℕ) : ℚ)) *
            ((p : ℚ) * boundaryFactor (P * p + 2 * k)) := by
      rw [show P * p + 2 * (k + 1) = (P * p + 2 * k) + 2 by omega]
      calc
        _ = (p : ℚ) * ((((P * p + 2 * k + 2 : ℕ) : ℚ)) *
            boundaryFactor (P * p + 2 * k + 2)) := by ring
        _ = (p : ℚ) * ((((P * p + 2 * k + 1 : ℕ) : ℚ)) *
            boundaryFactor (P * p + 2 * k)) := by rw [boundaryFactor_step]
        _ = _ := by ring
    have hs := rational_residue_nat_mul_eq (P * p + 2 * k + 2) (P * p + 2 * k + 1)
      (hden (k + 1) hk) (hden k hkprev) hzstep
    have hc := rational_residue_nat_mul_eq (2 * k + 2) (2 * k + 1)
      (hcden (k + 1)) (hcden k) (centralCoeff_step k)
    have hcast (v : ℕ) : ((P * p + v : ℕ) : ZMod p) = (v : ZMod p) := by
      push_cast
      simp
    rw [show P * p + 2 * k + 2 = P * p + (2 * k + 2) by omega,
      show P * p + 2 * k + 1 = P * p + (2 * k + 1) by omega,
      hcast, hcast] at hs
    have hnz : ((2 * k + 2 : ℕ) : ZMod p) ≠ 0 := by
      intro hzero
      have hd := (ZMod.natCast_eq_zero_iff (2 * k + 2) p).mp hzero
      have hle := Nat.le_of_dvd (by omega : 0 < 2 * k + 2) hd
      omega
    apply mul_left_cancel₀ hnz
    rw [hs, ih hkprev]
    calc
      _ = (-1 : ZMod p) ^ ((p - 1) / 2) *
          (((2 * k + 1 : ℕ) : ZMod p) *
            (((centralCoeff k).num : ZMod p) / ((centralCoeff k).den : ZMod p))) *
              (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by ring
      _ = (-1 : ZMod p) ^ ((p - 1) / 2) *
          (((2 * k + 2 : ℕ) : ZMod p) *
            (((centralCoeff (k + 1)).num : ZMod p) / ((centralCoeff (k + 1)).den : ZMod p))) *
              (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by rw [hc]
      _ = _ := by ring

theorem boundaryFactor_odd_even_remainder_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2)
    (hrEven : (z % p) % 2 = 0) :
    (((p : ℚ) * boundaryFactor z).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor (z / p)).den : ZMod p) ≠ 0 ∧
        ((centralCoeff ((z % p) / 2)).den : ZMod p) ≠ 0 ∧
          (((p : ℚ) * boundaryFactor z).num : ZMod p) /
            (((p : ℚ) * boundaryFactor z).den : ZMod p) =
              (-1 : ZMod p) ^ ((p - 1) / 2) *
                (((centralCoeff ((z % p) / 2)).num : ZMod p) /
                  ((centralCoeff ((z % p) / 2)).den : ZMod p)) *
                    (((boundaryFactor (z / p)).num : ZMod p) /
                      ((boundaryFactor (z / p)).den : ZMod p)) := by
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hdecomp := Nat.mod_add_div z p
  have hpar := congrArg (fun n : ℕ => n % 2) hdecomp
  simp only [Nat.add_mod, Nat.mul_mod, hrEven, hpOdd, zero_add, one_mul,
    Nat.mod_mod, hzOdd] at hpar
  have hP : z / p < p := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hz)
  have hr : 2 * ((z % p) / 2) = z % p := by omega
  have heq : (z / p) * p + 2 * ((z % p) / 2) = z := by
    rw [hr, Nat.mul_comm]
    omega
  have hk : 2 * ((z % p) / 2) < p := by rw [hr]; exact Nat.mod_lt _ hp.out.pos
  simpa only [heq] using boundaryFactor_odd_even_digit_reduction hp2 hpar hP hk





private theorem boundaryFactor_small_valuation_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < p) : padicValRat p (boundaryFactor z) = 0 := by
  have hsq : z < p ^ 2 := by nlinarith [hp.out.one_lt]
  by_cases hEven : z % 2 = 0
  · rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 hEven hsq,
      Nat.mod_eq_of_lt hz]
    simp [hEven]
  · have hOdd : z % 2 = 1 := by omega
    rw [boundaryFactor_odd_prime_valuation hp.out hp2 hOdd hsq,
      Nat.mod_eq_of_lt hz]
    simp [hOdd]

theorem boundaryPlusWeight_small_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hz : z < p) :
    ((boundaryPlusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hvz : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hz0 hz)]
    norm_num
  apply rational_den_ne_zero_of_valuation_nonneg
  rw [boundaryPlusWeight,
    padicValRat.div (by norm_num : (2 : ℚ) ≠ 0)
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)),
    padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
    padicValRat.pow, hvz, boundaryFactor_small_valuation_zero hp2 hz]
  simpa using zero_le_padicValRat_of_nat (p := p) 2

theorem boundaryPlusWeight_even_nonmultiple_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hnon : ¬p ∣ z) :
    (((p : ℚ) ^ 2 * boundaryPlusWeight z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryPlusWeight z).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryPlusWeight z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hw : boundaryPlusWeight z ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z))
  have hvz : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnon]
    norm_num
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  rw [padicValRat.mul (pow_ne_zero 2 hpq) hw, padicValRat.pow,
    padicValRat.self hp.out.one_lt, boundaryPlusWeight,
    padicValRat.div (by norm_num : (2 : ℚ) ≠ 0)
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)),
    padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
    padicValRat.pow, hvz,
    boundaryFactor_even_odd_prime_valuation hp.out hp2 hzEven hz]
  split_ifs <;> omega

theorem boundaryPlusWeight_odd_nonmultiple_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) (hnon : ¬p ∣ z) :
    (((p : ℚ) * boundaryPlusWeight z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * boundaryPlusWeight z).num : ZMod p) /
        (((p : ℚ) * boundaryPlusWeight z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hw : boundaryPlusWeight z ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z))
  have hvz : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnon]
    norm_num
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  rw [padicValRat.mul hpq hw, padicValRat.self hp.out.one_lt, boundaryPlusWeight,
    padicValRat.div (by norm_num : (2 : ℚ) ≠ 0)
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)),
    padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
    padicValRat.pow, hvz, boundaryFactor_odd_prime_valuation hp.out hp2 hzOdd hz]
  split_ifs <;> omega

private theorem two_div_square_mul_residue {p m : ℕ} [hp : Fact p.Prime]
    (hm0 : 0 < m) (hm : m < p) {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat p q = 0) :
    ((2 / ((m : ℚ) ^ 2 * q)).den : ZMod p) ≠ 0 ∧
      ((2 / ((m : ℚ) ^ 2 * q)).num : ZMod p) /
        ((2 / ((m : ℚ) ^ 2 * q)).den : ZMod p) =
          (((2 / (m : ℚ) ^ 2).num : ZMod p) /
            ((2 / (m : ℚ) ^ 2).den : ZMod p)) *
              ((q.num : ZMod p) / (q.den : ZMod p))⁻¹ := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have hvm : padicValRat p (m : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hm0 hm)]
    norm_num
  have ha : ((2 / (m : ℚ) ^ 2).den : ZMod p) ≠ 0 := by
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [padicValRat.div (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 2 hmq),
      padicValRat.pow, hvm]
    simpa using zero_le_padicValRat_of_nat (p := p) 2
  have hi := rational_residue_inv hq hv
  have hprod := rational_residue_mul ha hi.1
  have heq : (2 / (m : ℚ) ^ 2) * q⁻¹ = 2 / ((m : ℚ) ^ 2 * q) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, hi.2] at hprod
  exact hprod

theorem boundaryPlusWeight_even_multiple_reduction {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0) (hm : m < p) :
    (((p : ℚ) ^ 2 * boundaryPlusWeight (p * m)).den : ZMod p) ≠ 0 ∧
      ((boundaryPlusWeight m).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryPlusWeight (p * m)).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryPlusWeight (p * m)).den : ZMod p) =
            ((boundaryPlusWeight m).num : ZMod p) /
              ((boundaryPlusWeight m).den : ZMod p) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have hEven : (p * m) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hsmall : p * m < p ^ 2 := by nlinarith [hp.out.pos]
  have hrem : (p * m) % p = 0 := by simp
  have hdiv : (p * m) / p = m := by simp [hp.out.ne_zero]
  have hH : R (boundaryFactor (p * m)) = R (boundaryFactor m) := by
    have h := boundaryFactor_even_digit_reduction hp2 hEven
      (show ((p * m) % p) % 2 = 0 by rw [hrem])
    simpa [R, hrem, hdiv] using h.2.2.2
  have hvH : padicValRat p (boundaryFactor (p * m)) = 0 := by
    rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 hEven hsmall, hrem]
    norm_num
  have hi := two_div_square_mul_residue hm0 hm (boundaryFactor_ne_zero (p * m)) hvH
  have hj := two_div_square_mul_residue hm0 hm (boundaryFactor_ne_zero m)
    (boundaryFactor_small_valuation_zero hp2 hm)
  have heq : (p : ℚ) ^ 2 * boundaryPlusWeight (p * m) =
      2 / ((m : ℚ) ^ 2 * boundaryFactor (p * m)) := by
    rw [boundaryPlusWeight, Nat.cast_mul]
    field_simp [hpq, hmq, boundaryFactor_ne_zero (p * m)]
  refine ⟨?_, boundaryPlusWeight_small_den_ne_zero hp2 hm0 hm, ?_⟩
  · simpa only [heq] using hi.1
  · rw [heq]
    change R (2 / ((m : ℚ) ^ 2 * boundaryFactor (p * m))) =
      R (2 / ((m : ℚ) ^ 2 * boundaryFactor m))
    have hiR : R (2 / ((m : ℚ) ^ 2 * boundaryFactor (p * m))) =
        R (2 / (m : ℚ) ^ 2) * (R (boundaryFactor (p * m)))⁻¹ := hi.2
    have hjR : R (2 / ((m : ℚ) ^ 2 * boundaryFactor m)) =
        R (2 / (m : ℚ) ^ 2) * (R (boundaryFactor m))⁻¹ := hj.2
    rw [hiR, hjR, hH]

theorem boundaryPlusWeight_odd_multiple_reduction {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hmOdd : m % 2 = 1) (hm : m < p) :
    (((p : ℚ) * boundaryPlusWeight (p * m)).den : ZMod p) ≠ 0 ∧
      ((boundaryPlusWeight m).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * boundaryPlusWeight (p * m)).num : ZMod p) /
          (((p : ℚ) * boundaryPlusWeight (p * m)).den : ZMod p) =
            (-1 : ZMod p) ^ ((p - 1) / 2) *
              (((boundaryPlusWeight m).num : ZMod p) /
                ((boundaryPlusWeight m).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hm0 : 0 < m := by omega
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hOdd : (p * m) % 2 = 1 := by simp [Nat.mul_mod, hpOdd, hmOdd]
  have hsmall : p * m < p ^ 2 := by nlinarith [hp.out.pos]
  have hrem : (p * m) % p = 0 := by simp
  have hH : R ((p : ℚ) * boundaryFactor (p * m)) =
      (-1 : ZMod p) ^ ((p - 1) / 2) * R (boundaryFactor m) := by
    simpa only [Nat.mul_comm] using
      (boundaryFactor_odd_multiple_reduction hp2 hmOdd hm).2.2
  have hvH : padicValRat p ((p : ℚ) * boundaryFactor (p * m)) = 0 := by
    rw [padicValRat.mul hpq (boundaryFactor_ne_zero (p * m)),
      padicValRat.self hp.out.one_lt,
      boundaryFactor_odd_prime_valuation hp.out hp2 hOdd hsmall, hrem]
    norm_num
  have hi := two_div_square_mul_residue hm0 hm
    (mul_ne_zero hpq (boundaryFactor_ne_zero (p * m))) hvH
  have hj := two_div_square_mul_residue hm0 hm (boundaryFactor_ne_zero m)
    (boundaryFactor_small_valuation_zero hp2 hm)
  have heq : (p : ℚ) * boundaryPlusWeight (p * m) =
      2 / ((m : ℚ) ^ 2 * ((p : ℚ) * boundaryFactor (p * m))) := by
    rw [boundaryPlusWeight, Nat.cast_mul]
    field_simp [hpq, hmq, boundaryFactor_ne_zero (p * m)]
  refine ⟨?_, boundaryPlusWeight_small_den_ne_zero hp2 hm0 hm, ?_⟩
  · simpa only [heq] using hi.1
  · rw [heq]
    change R (2 / ((m : ℚ) ^ 2 * ((p : ℚ) * boundaryFactor (p * m)))) =
      (-1 : ZMod p) ^ ((p - 1) / 2) * R (2 / ((m : ℚ) ^ 2 * boundaryFactor m))
    have hiR : R (2 / ((m : ℚ) ^ 2 * ((p : ℚ) * boundaryFactor (p * m)))) =
        R (2 / (m : ℚ) ^ 2) * (R ((p : ℚ) * boundaryFactor (p * m)))⁻¹ := hi.2
    have hjR : R (2 / ((m : ℚ) ^ 2 * boundaryFactor m)) =
        R (2 / (m : ℚ) ^ 2) * (R (boundaryFactor m))⁻¹ := hj.2
    rw [hiR, hjR, hH]
    simp only [mul_inv_rev]
    ring_nf
    norm_num





def momentScalarPred (z : ℕ) : ℚ :=
  if z = 0 then 0 else momentScalar (z - 1)

@[simp] theorem momentScalarPred_zero : momentScalarPred 0 = 0 := by
  simp [momentScalarPred]

theorem momentScalarPred_of_odd {z : ℕ} (hz : z % 2 = 1) :
    momentScalarPred z = 2 * boundaryFactor z := by
  have heq : z = 2 * (z / 2) + 1 := by omega
  generalize z / 2 = l at heq
  subst z
  rw [momentScalarPred, if_neg (by omega : 2 * l + 1 ≠ 0),
    show 2 * l + 1 - 1 = 2 * l by omega, momentScalar_even, boundaryFactor_odd]
  ring

theorem momentScalarPred_of_even {z : ℕ} (hz : z % 2 = 0) :
    momentScalarPred z = 0 := by
  by_cases hzero : z = 0
  · simp [hzero]
  · have hprev : (z - 1) % 2 ≠ 0 := by omega
    simp [momentScalarPred, hzero, momentScalar, hprev]

theorem momentScalarPred_small_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : z < p) :
    0 ≤ padicValRat p (momentScalarPred z) := by
  by_cases hzero : z = 0
  · simp [hzero]
  · rw [momentScalarPred, if_neg hzero]
    exact momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega)

theorem momentScalarPred_scaled_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : z < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) * momentScalarPred z) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases heven : z % 2 = 0
  · simp [momentScalarPred_of_even heven]
  · have hodd : z % 2 = 1 := by omega
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hv := boundaryFactor_odd_scaled_valuation_nonneg hp hp2 hodd hz
    have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
    rw [momentScalarPred_of_odd hodd,
      show (p : ℚ) * (2 * boundaryFactor z) = 2 * ((p : ℚ) * boundaryFactor z) by ring,
      padicValRat.mul (by norm_num) (mul_ne_zero hpq (boundaryFactor_ne_zero z))]
    omega

theorem momentScalarPred_prime_digit_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < p ^ 2) :
    (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 ∧
      ((momentScalarPred (z / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * momentScalarPred z).num : ZMod p) /
          (((p : ℚ) * momentScalarPred z).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - z % p) *
              (((momentScalarPred (z / p)).num : ZMod p) /
                ((momentScalarPred (z / p)).den : ZMod p)) := by
  have hP : z / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hz)
  have hr : z % p < p := Nat.mod_lt _ hp.out.pos
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div z p)
  simp only [Nat.add_mod, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod] at hpar
  have hscaled : (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (momentScalarPred_scaled_valuation_nonneg hp.out hp2 hz)
  have hsmall : ((momentScalarPred (z / p)).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (momentScalarPred_small_valuation_nonneg hp.out hp2 hP)
  refine ⟨hscaled, hsmall, ?_⟩
  by_cases hzEven : z % 2 = 0
  · by_cases hrEven : (z % p) % 2 = 0
    · have hPEven : (z / p) % 2 = 0 := by omega
      rw [momentScalarPred_of_even hzEven, momentScalarPred_of_even hPEven]
      norm_num
    · have hEzero : (oddPrimeWeight p).coeff (p - 1 - z % p) = 0 := by
        rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
          oddPrimeWeight_coeff_odd p (z % p) hrEven, mul_zero]
      rw [momentScalarPred_of_even hzEven, hEzero]
      norm_num
  · have hzOdd : z % 2 = 1 := by omega
    by_cases hrEven : (z % p) % 2 = 0
    · have hPOdd : (z / p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_even_remainder_reduction hp2 hzOdd hz hrEven
      have hleft :
          (((p : ℚ) * momentScalarPred z).num : ZMod p) /
              (((p : ℚ) * momentScalarPred z).den : ZMod p) =
            2 * ((((p : ℚ) * boundaryFactor z).num : ZMod p) /
              (((p : ℚ) * boundaryFactor z).den : ZMod p)) := by
        have h := rational_residue_nat_mul_eq 1 2 hscaled hH.1
          (by rw [momentScalarPred_of_odd hzOdd]; ring)
        simpa only [Nat.cast_one, one_mul, Nat.cast_ofNat] using h
      have hright :
          ((momentScalarPred (z / p)).num : ZMod p) /
              ((momentScalarPred (z / p)).den : ZMod p) =
            2 * (((boundaryFactor (z / p)).num : ZMod p) /
              ((boundaryFactor (z / p)).den : ZMod p)) := by
        have h := rational_residue_nat_mul_eq 1 2 hsmall hH.2.1
          (by rw [momentScalarPred_of_odd hPOdd]; ring)
        simpa only [Nat.cast_one, one_mul, Nat.cast_ofNat] using h
      have hrem : 2 * ((z % p) / 2) = z % p := by omega
      have hcoeff : (oddPrimeWeight p).coeff (z % p) =
          ((centralCoeff ((z % p) / 2)).num : ZMod p) /
            ((centralCoeff ((z % p) / 2)).den : ZMod p) := by
        calc
          (oddPrimeWeight p).coeff (z % p) =
              (oddPrimeWeight p).coeff (2 * ((z % p) / 2)) := by rw [hrem]
          _ = ((2 * ((z % p) / 2)).choose ((z % p) / 2) : ZMod p) /
              (4 : ZMod p) ^ ((z % p) / 2) :=
            oddPrimeWeight_coeff_central hp2 (by omega)
          _ = _ := (centralCoeff_reduced_residue hp2 ((z % p) / 2)).2.symm
      rw [hleft, hH.2.2.2, oddPrimeWeight_coeff_reverse hp.out hp2 hr, hcoeff, hright]
      ring
    · have hrOdd : (z % p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_odd_remainder_reduction hp2 hzOdd hz hrOdd
      have hleft :
          (((p : ℚ) * momentScalarPred z).num : ZMod p) /
              (((p : ℚ) * momentScalarPred z).den : ZMod p) = 0 := by
        have h := rational_residue_nat_mul_eq 1 2 hscaled hH.1
          (by rw [momentScalarPred_of_odd hzOdd]; ring)
        simpa only [Nat.cast_one, one_mul, Nat.cast_ofNat, hH.2, mul_zero] using h
      have hEzero : (oddPrimeWeight p).coeff (p - 1 - z % p) = 0 := by
        rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
          oddPrimeWeight_coeff_odd p (z % p) hrEven, mul_zero]
      rw [hleft, hEzero, zero_mul]





open scoped BigOperators

theorem boundaryMinus_odd_explicit {u : ℕ} (huOdd : u % 2 = 1) :
    boundaryMinus u = boundaryFactor u * oddHarmonicRat u := by
  rw [boundaryMinus_explicit]
  congr 1
  unfold parityBoundarySum oddHarmonicRat
  apply Finset.sum_congr rfl
  intro z hz
  rw [huOdd]
  split_ifs with h
  · rw [boundaryMinusWeight, if_neg (by omega : z % 2 ≠ 0)]
  · rfl

theorem boundaryMinus_odd_scaled_product {p u : ℕ} (huOdd : u % 2 = 1) :
    (p : ℚ) ^ 2 * boundaryMinus u =
      ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * oddHarmonicRat u) := by
  rw [boundaryMinus_odd_explicit huOdd]
  ring

theorem boundaryMinus_odd_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huOdd : u % 2 = 1) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((boundaryMinus (u / p)).num : ZMod p) /
                ((boundaryMinus (u / p)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hP : u / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hu)
  have hr : u % p < p := Nat.mod_lt _ hp.out.pos
  have hstrip := oddHarmonicRat_prime_digit_reduction hp2 hu
  have hstripR : R ((p : ℚ) * oddHarmonicRat u) = R (oddHarmonicRat (u / p)) :=
    hstrip.2.2
  have hHden := (boundaryFactor_odd_integral_denominators hp2 huOdd hu).2
  have hmul := rational_residue_mul hHden hstrip.1
  have hprod := boundaryMinus_odd_scaled_product (p := p) huOdd
  have hscaled : (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      R ((p : ℚ) ^ 2 * boundaryMinus u) =
        R ((p : ℚ) * boundaryFactor u) * R ((p : ℚ) * oddHarmonicRat u) := by
    simpa only [R, ← hprod] using hmul
  have htarget : ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ hP)
  refine ⟨hscaled.1, htarget, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryMinus u) =
    (oddPrimeWeight p).coeff (p - 1 - u % p) * R (boundaryMinus (u / p))
  rw [hscaled.2, hstripR]
  by_cases hrEven : (u % p) % 2 = 0
  · have hH := boundaryFactor_odd_even_remainder_reduction hp2 huOdd hu hrEven
    have hHR : R ((p : ℚ) * boundaryFactor u) =
        (-1 : ZMod p) ^ ((p - 1) / 2) * R (centralCoeff ((u % p) / 2)) *
          R (boundaryFactor (u / p)) := hH.2.2.2
    have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
    have hdecomp := Nat.mod_add_div u p
    have hpar := congrArg (fun n : ℕ => n % 2) hdecomp
    simp only [Nat.add_mod, Nat.mul_mod, hrEven, hpOdd, zero_add, one_mul,
      Nat.mod_mod, huOdd] at hpar
    have hB := rational_residue_mul hH.2.1 hstrip.2.1
    have hBres : R (boundaryMinus (u / p)) =
        R (boundaryFactor (u / p)) * R (oddHarmonicRat (u / p)) := by
      rw [boundaryMinus_odd_explicit hpar]
      exact hB.2
    have hrEq : 2 * ((u % p) / 2) = u % p := by omega
    have hc : R (centralCoeff ((u % p) / 2)) = (oddPrimeWeight p).coeff (u % p) := by
      change ((centralCoeff ((u % p) / 2)).num : ZMod p) /
        ((centralCoeff ((u % p) / 2)).den : ZMod p) = _
      rw [(centralCoeff_reduced_residue hp2 ((u % p) / 2)).2]
      symm
      simpa only [hrEq] using
        (oddPrimeWeight_coeff_central hp2 (show 2 * ((u % p) / 2) < p by omega))
    rw [hHR, oddPrimeWeight_coeff_reverse hp.out hp2 hr, ← hc, hBres]
    ring
  · have hrOdd : (u % p) % 2 = 1 := by omega
    have hH := boundaryFactor_odd_odd_remainder_reduction hp2 huOdd hu hrOdd
    have hHR : R ((p : ℚ) * boundaryFactor u) = 0 := hH.2
    have hcoeff : (oddPrimeWeight p).coeff (p - 1 - u % p) = 0 := by
      rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
        oddPrimeWeight_coeff_odd p (u % p) hrEven, mul_zero]
    rw [hHR, hcoeff, zero_mul, zero_mul]

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

def boundaryPlusParitySum (e u : ℕ) : ℚ :=
  ∑ z ∈ Finset.range (u + 1), if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0

@[simp] theorem boundaryPlusParitySum_zero (e : ℕ) : boundaryPlusParitySum e 0 = 0 := by
  simp [boundaryPlusParitySum]

theorem boundaryPlusParitySum_succ (e u : ℕ) :
    boundaryPlusParitySum e (u + 1) = boundaryPlusParitySum e u +
      (if 0 < u + 1 ∧ (u + 1) % 2 = e then boundaryPlusWeight (u + 1) else 0) := by
  simp only [boundaryPlusParitySum, Finset.sum_range_succ]

theorem boundaryPlusParitySum_eq (u : ℕ) :
    boundaryPlusParitySum (u % 2) u = parityBoundarySum boundaryPlusWeight u := rfl

theorem boundaryPlusParitySum_small_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (e : ℕ) (hu : u < p) :
    ((boundaryPlusParitySum e u).den : ZMod p) ≠ 0 := by
  unfold boundaryPlusParitySum
  apply (rational_residue_sum _ _ ?_).1
  intro z hz
  by_cases hgood : 0 < z ∧ z % 2 = e
  · rw [if_pos hgood]
    exact boundaryPlusWeight_small_den_ne_zero hp2 hgood.1
      (by have := Finset.mem_range.mp hz; omega)
  · simp [hgood]

private theorem plusParityTerm_scaled_nonmultiple {p z e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (he : e ≤ 1) (hz0 : 0 < z) (hz : z < p ^ 2) (hnon : ¬p ∣ z) :
    (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
      (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) ≠ 0 ∧
      (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
        (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).num : ZMod p) /
        (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
          (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) = 0 := by
  by_cases hgood : 0 < z ∧ z % 2 = e
  · rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · simpa only [if_pos hgood, if_pos rfl, ite_true] using
        boundaryPlusWeight_even_nonmultiple_reduction hp2 hz0 hgood.2 hz hnon
    · simpa only [if_pos hgood, show (1 : ℕ) ≠ 0 by decide, ite_false] using
        boundaryPlusWeight_odd_nonmultiple_reduction hp2 hgood.2 hz hnon
  · simp [hgood]

private theorem plusParityTerm_scaled_multiple {p z e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (he : e ≤ 1) (hz0 : 0 < z) (hz : z < p ^ 2) (hdiv : p ∣ z) :
    (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
      (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) ≠ 0 ∧
      ((if 0 < z / p ∧ (z / p) % 2 = e then boundaryPlusWeight (z / p) else 0).den : ZMod p) ≠ 0 ∧
        (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
          (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).num : ZMod p) /
          (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
            (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) =
              (if e = 0 then 1 else (-1 : ZMod p) ^ ((p - 1) / 2)) *
                (((if 0 < z / p ∧ (z / p) % 2 = e then boundaryPlusWeight (z / p) else 0).num : ZMod p) /
                  ((if 0 < z / p ∧ (z / p) % 2 = e then boundaryPlusWeight (z / p) else 0).den : ZMod p)) := by
  have heq : z = p * (z / p) := (Nat.mul_div_cancel' hdiv).symm
  have hq0 : 0 < z / p := by
    by_contra hn
    have hzq : z / p = 0 := Nat.eq_zero_of_not_pos hn
    rw [hzq, mul_zero] at heq
    omega
  have hq : z / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hz)
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar : z % 2 = (z / p) % 2 := by
    conv_lhs => rw [heq, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod]
  by_cases hgood : 0 < z ∧ z % 2 = e
  · have hqgood : 0 < z / p ∧ (z / p) % 2 = e := ⟨hq0, hpar ▸ hgood.2⟩
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · have h := boundaryPlusWeight_even_multiple_reduction hp2 hq0 hqgood.2 hq
      rw [← heq] at h
      simpa only [if_pos hgood, if_pos hqgood, if_pos rfl, ite_true, one_mul] using h
    · have h := boundaryPlusWeight_odd_multiple_reduction hp2 hqgood.2 hq
      rw [← heq] at h
      simpa only [if_pos hgood, if_pos hqgood, show (1 : ℕ) ≠ 0 by decide, ite_false] using h
  · have hqbad : ¬(0 < z / p ∧ (z / p) % 2 = e) := by
      intro h
      exact hgood ⟨hz0, hpar.trans h.2⟩
    simp only [if_neg hgood, if_neg hqbad, mul_zero]
    norm_num

theorem boundaryPlusParitySum_prime_digit_reduction {p u e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (he : e ≤ 1) (hu : u < p ^ 2) :
    (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u).den : ZMod p) ≠ 0 ∧
      ((boundaryPlusParitySum e (u / p)).den : ZMod p) ≠ 0 ∧
        (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u).num : ZMod p) /
          (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u).den : ZMod p) =
            (if e = 0 then 1 else (-1 : ZMod p) ^ ((p - 1) / 2)) *
              (((boundaryPlusParitySum e (u / p)).num : ZMod p) /
                ((boundaryPlusParitySum e (u / p)).den : ZMod p)) := by
  revert hu
  induction u with
  | zero => intro hu; simp
  | succ u ih =>
    intro hu
    have hprev := ih (by omega : u < p ^ 2)
    have hscale :
        (if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e (u + 1) =
          (if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u +
            (if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
              (if 0 < u + 1 ∧ (u + 1) % 2 = e then boundaryPlusWeight (u + 1) else 0) := by
      rw [boundaryPlusParitySum_succ, mul_add]
    by_cases hdiv : p ∣ u + 1
    · have hquot : (u + 1) / p = u / p + 1 := Nat.succ_div_of_dvd hdiv
      have hterm := plusParityTerm_scaled_multiple hp2 he (by omega : 0 < u + 1) hu hdiv
      rw [hquot] at hterm
      have hl := rational_residue_add hprev.1 hterm.1
      have hr := rational_residue_add hprev.2.1 hterm.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot, boundaryPlusParitySum_succ]
        exact hr.1
      · rw [hscale, hl.2, hprev.2.2, hterm.2.2, hquot, boundaryPlusParitySum_succ, hr.2]
        ring
    · have hquot : (u + 1) / p = u / p := Nat.succ_div_of_not_dvd hdiv
      have hterm := plusParityTerm_scaled_nonmultiple hp2 he (by omega : 0 < u + 1) hu hdiv
      have hl := rational_residue_add hprev.1 hterm.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, hterm.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan



namespace InternalCatalan

private theorem plus_start_small_H_den {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p) : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  have hu2 : u < p ^ 2 := by nlinarith [hp.out.two_le]
  by_cases he : u % 2 = 0
  · rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 he hu2,
      Nat.mod_eq_of_lt hu]
    simp [he]
  · rw [boundaryFactor_odd_prime_valuation hp.out hp2 (by omega) hu2,
      Nat.mod_eq_of_lt hu]
    simp [he]

theorem boundaryPlus_small_successor_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p) : ((boundaryPlus (u + 1)).den : ZMod p) ≠ 0 := by
  rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq]
  exact (rational_residue_mul (plus_start_small_H_den hp2 hu)
    (boundaryPlusParitySum_small_den_ne_zero hp2 (u % 2) hu)).1

theorem boundaryPlus_prime_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).den : ZMod p) ≠ 0 ∧
      ((boundaryPlus (u / p + 1)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((boundaryPlus (u / p + 1)).num : ZMod p) /
                ((boundaryPlus (u / p + 1)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hP : u / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hu)
  have hr : u % p < p := Nat.mod_lt _ hp.out.pos
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div u p)
  simp only [Nat.add_mod, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod] at hpar
  have hcoeff (hrEven : (u % p) % 2 = 0) :
      (oddPrimeWeight p).coeff (u % p) = R (centralCoeff ((u % p) / 2)) := by
    have hrem : 2 * ((u % p) / 2) = u % p := by omega
    calc
      (oddPrimeWeight p).coeff (u % p) =
          (oddPrimeWeight p).coeff (2 * ((u % p) / 2)) := by rw [hrem]
      _ = ((2 * ((u % p) / 2)).choose ((u % p) / 2) : ZMod p) /
          (4 : ZMod p) ^ ((u % p) / 2) := oddPrimeWeight_coeff_central hp2 (by omega)
      _ = _ := (centralCoeff_reduced_residue hp2 ((u % p) / 2)).2.symm
  refine ⟨boundaryPlus_prime_sq_scaled_den_ne_zero hp2 hu,
    boundaryPlus_small_successor_den_ne_zero hp2 hP, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryPlus (u + 1)) =
    (oddPrimeWeight p).coeff (u % p) * R (boundaryPlus (u / p + 1))
  by_cases huEven : u % 2 = 0
  · have hstrip := boundaryPlusParitySum_prime_digit_reduction (e := 0) hp2 (by decide) hu
    simp only [ite_true, one_mul] at hstrip
    have hbig : (p : ℚ) ^ 2 * boundaryPlus (u + 1) =
        boundaryFactor u * ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) := by
      rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, huEven]
      ring
    by_cases hrEven : (u % p) % 2 = 0
    · have hPEven : (u / p) % 2 = 0 := by omega
      have hH := boundaryFactor_even_digit_reduction hp2 huEven hrEven
      have hbigR : R (boundaryFactor u * ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u)) =
          R (boundaryFactor u) * R ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hsmall : boundaryPlus (u / p + 1) =
          boundaryFactor (u / p) * boundaryPlusParitySum 0 (u / p) := by
        rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, hPEven]
      have hsmallR : R (boundaryPlus (u / p + 1)) =
          R (boundaryFactor (u / p)) * R (boundaryPlusParitySum 0 (u / p)) := by
        rw [hsmall]
        exact (rational_residue_mul hH.2.1 hstrip.2.1).2
      have hHR : R (boundaryFactor u) =
          R (boundaryFactor (u / p)) * R (centralCoeff ((u % p) / 2)) := hH.2.2.2
      have hstripR : R ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) =
          R (boundaryPlusParitySum 0 (u / p)) := hstrip.2.2
      rw [hbig, hbigR, hHR, hstripR, hcoeff hrEven, hsmallR]
      ring
    · have hrOdd : (u % p) % 2 = 1 := by omega
      have hH := boundaryFactor_even_carry_reduction hp2 huEven hu hrOdd
      have hbigR : R (boundaryFactor u * ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u)) =
          R (boundaryFactor u) * R ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hHR : R (boundaryFactor u) = 0 := hH.2
      rw [hbig, hbigR, hHR, oddPrimeWeight_coeff_odd p (u % p) hrEven, zero_mul, zero_mul]
  · have huOdd : u % 2 = 1 := by omega
    have hstrip := boundaryPlusParitySum_prime_digit_reduction (e := 1) hp2 (by decide) hu
    simp only [show (1 : ℕ) ≠ 0 by decide, ite_false] at hstrip
    have hbig : (p : ℚ) ^ 2 * boundaryPlus (u + 1) =
        ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * boundaryPlusParitySum 1 u) := by
      rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, huOdd]
      ring
    by_cases hrEven : (u % p) % 2 = 0
    · have hPOdd : (u / p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_even_remainder_reduction hp2 huOdd hu hrEven
      have hbigR : R (((p : ℚ) * boundaryFactor u) * ((p : ℚ) * boundaryPlusParitySum 1 u)) =
          R ((p : ℚ) * boundaryFactor u) * R ((p : ℚ) * boundaryPlusParitySum 1 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hsmall : boundaryPlus (u / p + 1) =
          boundaryFactor (u / p) * boundaryPlusParitySum 1 (u / p) := by
        rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, hPOdd]
      have hsmallR : R (boundaryPlus (u / p + 1)) =
          R (boundaryFactor (u / p)) * R (boundaryPlusParitySum 1 (u / p)) := by
        rw [hsmall]
        exact (rational_residue_mul hH.2.1 hstrip.2.1).2
      have hHR : R ((p : ℚ) * boundaryFactor u) =
          (-1 : ZMod p) ^ ((p - 1) / 2) * R (centralCoeff ((u % p) / 2)) *
            R (boundaryFactor (u / p)) := hH.2.2.2
      have hstripR : R ((p : ℚ) * boundaryPlusParitySum 1 u) =
          (-1 : ZMod p) ^ ((p - 1) / 2) * R (boundaryPlusParitySum 1 (u / p)) := hstrip.2.2
      have heps : ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm ((p - 1) / 2) 2, pow_mul]
        norm_num
      rw [hbig, hbigR, hHR, hstripR, hcoeff hrEven, hsmallR]
      calc
        _ = ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ 2 *
            (R (centralCoeff ((u % p) / 2)) *
              (R (boundaryFactor (u / p)) * R (boundaryPlusParitySum 1 (u / p)))) := by ring
        _ = _ := by rw [heps, one_mul]
    · have hrOdd : (u % p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_odd_remainder_reduction hp2 huOdd hu hrOdd
      have hbigR : R (((p : ℚ) * boundaryFactor u) * ((p : ℚ) * boundaryPlusParitySum 1 u)) =
          R ((p : ℚ) * boundaryFactor u) * R ((p : ℚ) * boundaryPlusParitySum 1 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hHR : R ((p : ℚ) * boundaryFactor u) = 0 := hH.2
      rw [hbig, hbigR, hHR, oddPrimeWeight_coeff_odd p (u % p) hrEven, zero_mul, zero_mul]

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeLowerMomentDigits
namespace OAI


namespace InternalCatalan

theorem boundaryFactor_even_multiple_reciprocal_reduction {p m : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm0 : 0 < m)
    (hmEven : m % 2 = 0) (hm : m < p) :
    (((p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p))).den : ZMod p) ≠ 0 ∧
      (((1 : ℚ) / ((m : ℚ) * boundaryFactor m)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p))).num : ZMod p) /
          (((p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p))).den : ZMod p) =
            (((1 : ℚ) / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
              (((1 : ℚ) / ((m : ℚ) * boundaryFactor m)).den : ZMod p) := by
  have hmpEven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hmpMod : (m * p) % p = 0 := Nat.mul_mod_left m p
  have hmpDiv : (m * p) / p = m := Nat.mul_div_cancel m hp.out.pos
  have hmpSmall : m * p < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hm hp.out.pos
  have hmSmall : m < p ^ 2 := by
    have hpp : p ≤ p * p := by
      have hp1 : 1 ≤ p := by have := hp.out.pos; omega
      simpa only [one_mul] using Nat.mul_le_mul_right p hp1
    simpa only [pow_two] using hm.trans_le hpp
  have hred := boundaryFactor_even_digit_reduction hp2 hmpEven
    (show ((m * p) % p) % 2 = 0 by rw [hmpMod])
  have hHres : ((boundaryFactor (m * p)).num : ZMod p) /
      ((boundaryFactor (m * p)).den : ZMod p) =
        ((boundaryFactor m).num : ZMod p) / ((boundaryFactor m).den : ZMod p) := by
    simpa [hmpDiv, hmpMod] using hred.2.2.2
  have hHv : padicValRat p (boundaryFactor (m * p)) = 0 :=
    boundaryFactor_even_odd_prime_eq_zero hp.out hp2 hmpEven hmpSmall
      (by rw [hmpMod])
  have hmv : padicValRat p (boundaryFactor m) = 0 :=
    boundaryFactor_even_odd_prime_eq_zero hp.out hp2 hmEven hmSmall
      (by simpa only [Nat.mod_eq_of_lt hm] using hmEven)
  have hmNatv : padicValRat p (m : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hm0 hm)]
    norm_num
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have h1v : padicValRat p ((m : ℚ) * boundaryFactor (m * p)) = 0 := by
    rw [padicValRat.mul hmq (boundaryFactor_ne_zero _), hmNatv, hHv]
    norm_num
  have h2v : padicValRat p ((m : ℚ) * boundaryFactor m) = 0 := by
    rw [padicValRat.mul hmq (boundaryFactor_ne_zero _), hmNatv, hmv]
    norm_num
  have h1 := rational_residue_mul (p := p) (a := (m : ℚ)) (b := boundaryFactor (m * p))
    (by simp) hred.1
  have h2 := rational_residue_mul (p := p) (a := (m : ℚ)) (b := boundaryFactor m)
    (by simp) (by simpa only [hmpDiv] using hred.2.1)
  have hi1 := rational_residue_inv
    (mul_ne_zero hmq (boundaryFactor_ne_zero (m * p))) h1v
  have hi2 := rational_residue_inv
    (mul_ne_zero hmq (boundaryFactor_ne_zero m)) h2v
  have hcancel : (p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p)) =
      ((m : ℚ) * boundaryFactor (m * p))⁻¹ := by
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [Nat.cast_mul]
    field_simp [hpq, hmq, boundaryFactor_ne_zero]
  simp only [hcancel, one_div]
  refine ⟨hi1.1, hi2.1, ?_⟩
  rw [hi1.2, hi2.2, h1.2, h2.2, hHres]





theorem boundaryFactor_even_reciprocal_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0)
    (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) / ((z : ℚ) * boundaryFactor z)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz0
  rw [padicValRat.div hpq (mul_ne_zero hzq (boundaryFactor_ne_zero z)),
    padicValRat.self hp.one_lt,
    boundaryFactor_even_mul_odd_prime_valuation hp hp2 hzEven hz0 hz]
  split_ifs <;> norm_num

theorem boundaryFactor_even_reciprocal_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    (((p : ℚ) / ((z : ℚ) * boundaryFactor z)).den : ZMod p) ≠ 0 :=
  rational_den_ne_zero_of_valuation_nonneg
    (boundaryFactor_even_reciprocal_valuation_nonneg hp.out hp2 hzEven hz0 hz)

private theorem boundaryFactor_reciprocal_down_step (p z : ℕ) (hz : 0 < z) :
    (z : ℚ) * ((p : ℚ) / ((z : ℚ) * boundaryFactor z)) =
      ((z + 1 : ℕ) : ℚ) *
        ((p : ℚ) / (((z + 2 : ℕ) : ℚ) * boundaryFactor (z + 2))) := by
  rw [boundaryFactor_step]
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  have hz1q : ((z + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hzq, hz1q, boundaryFactor_ne_zero z]

private theorem evenBlock_cast_sub (p m n : ℕ) (hn : n ≤ m * p) :
    ((m * p - n : ℕ) : ZMod p) = -(n : ZMod p) := by
  rw [Nat.cast_sub hn]
  push_cast
  simp

theorem boundaryFactor_even_block_reciprocal_reduction {p m j : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0)
    (hm : m < p) (hj : 2 * j < p) :
    (((p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) *
      boundaryFactor (m * p - 2 * j))).den : ZMod p) ≠ 0 ∧
      ((centralCoeff j).den : ZMod p) ≠ 0 ∧
        ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p) ≠ 0 ∧
          (((p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) *
            boundaryFactor (m * p - 2 * j))).num : ZMod p) /
              (((p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) *
                boundaryFactor (m * p - 2 * j))).den : ZMod p) =
                  (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p)) *
                    (((1 / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
                      ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p)) := by
  have hbase := boundaryFactor_even_multiple_reciprocal_reduction hp2 hm0 hmEven hm
  have hmp : p ≤ m * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  have hmpsmall : m * p < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hm hp.out.pos
  have hmpeven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hzpos : ∀ u : ℕ, 2 * u < p → 0 < m * p - 2 * u := by
    intro u hu
    omega
  have hden : ∀ u : ℕ, 2 * u < p →
      (((p : ℚ) / (((m * p - 2 * u : ℕ) : ℚ) *
        boundaryFactor (m * p - 2 * u))).den : ZMod p) ≠ 0 := by
    intro u hu
    have heven : (m * p - 2 * u) % 2 = 0 := by omega
    exact boundaryFactor_even_reciprocal_den_ne_zero hp2 heven
      (Nat.ne_of_gt (hzpos u hu)) (by omega)
  have hcden : ∀ u : ℕ, ((centralCoeff u).den : ZMod p) ≠ 0 :=
    fun u => (centralCoeff_reduced_residue hp2 u).1
  refine ⟨hden j hj, hcden j, hbase.2.1, ?_⟩
  revert hj
  induction j with
  | zero =>
    intro hj
    simpa [centralCoeff] using hbase.2.2
  | succ j ih =>
    intro hj
    have hjprev : 2 * j < p := by omega
    have hz : 0 < m * p - 2 * (j + 1) := hzpos (j + 1) hj
    have hstep := boundaryFactor_reciprocal_down_step p
      (m * p - 2 * (j + 1)) hz
    have hback : m * p - 2 * (j + 1) + 2 = m * p - 2 * j := by omega
    rw [hback] at hstep
    have hs := rational_residue_nat_mul_eq (m * p - 2 * (j + 1))
      (m * p - 2 * (j + 1) + 1) (hden (j + 1) hj) (hden j hjprev) hstep
    have hc := rational_residue_nat_mul_eq (2 * j + 2) (2 * j + 1)
      (hcden (j + 1)) (hcden j) (centralCoeff_step j)
    have hmid : m * p - 2 * (j + 1) + 1 = m * p - (2 * j + 1) := by omega
    have hleftCast : ((m * p - 2 * (j + 1) : ℕ) : ZMod p) =
        -((2 * j + 2 : ℕ) : ZMod p) := by
      simpa only [show 2 * (j + 1) = 2 * j + 2 by omega] using
        evenBlock_cast_sub p m (2 * (j + 1)) (by omega)
    have hrightCast : ((m * p - 2 * (j + 1) + 1 : ℕ) : ZMod p) =
        -((2 * j + 1 : ℕ) : ZMod p) := by
      rw [hmid]
      exact evenBlock_cast_sub p m (2 * j + 1) (by omega)
    rw [hleftCast, hrightCast] at hs
    simp only [neg_mul, neg_inj] at hs
    have hnz : ((2 * j + 2 : ℕ) : ZMod p) ≠ 0 := by
      intro hzero
      have hd := (ZMod.natCast_eq_zero_iff (2 * j + 2) p).mp hzero
      have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 2) hd
      omega
    apply mul_left_cancel₀ hnz
    rw [hs, ih hjprev]
    calc
      _ = (((2 * j + 1 : ℕ) : ZMod p) *
          (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p))) *
            (((1 / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
              ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p)) := by ring
      _ = (((2 * j + 2 : ℕ) : ZMod p) *
          (((centralCoeff (j + 1)).num : ZMod p) /
            ((centralCoeff (j + 1)).den : ZMod p))) *
              (((1 / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
                ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p)) := by rw [hc]
      _ = _ := by ring

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

theorem boundaryMinusWeight_even_scaled_eq {p z : ℕ} (hzEven : z % 2 = 0) :
    (p : ℚ) ^ 2 * boundaryMinusWeight z =
      2 * ((p : ℚ) / ((z : ℚ) * boundaryFactor z)) ^ 2 := by
  rw [boundaryMinusWeight, if_pos hzEven, div_pow, mul_pow]
  ring

theorem boundaryMinusWeight_even_block_sum_reduction {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0) (hm : m < p) :
    ((∑ j ∈ Finset.range ((p - 1) / 2 + 1),
      (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p) ≠ 0 ∧
      ((boundaryMinusWeight m).den : ZMod p) ≠ 0 ∧
        ((∑ j ∈ Finset.range ((p - 1) / 2 + 1),
          (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).num : ZMod p) /
            ((∑ j ∈ Finset.range ((p - 1) / 2 + 1),
              (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p) =
                (-1 : ZMod p) ^ ((p - 1) / 2) *
                  (((boundaryMinusWeight m).num : ZMod p) /
                    ((boundaryMinusWeight m).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let I : ℚ := 1 / ((m : ℚ) * boundaryFactor m)
  let F : ℕ → ℚ := fun j =>
    (p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) * boundaryFactor (m * p - 2 * j))
  have htwo : R 2 = 2 := by norm_num [R]
  have hsquare {q : ℚ} (hd : (q.den : ZMod p) ≠ 0) :
      ((q ^ 2).den : ZMod p) ≠ 0 ∧ R (q ^ 2) = R q ^ 2 := by
    simpa only [R, pow_two] using rational_residue_mul (p := p) hd hd
  have hI : (I.den : ZMod p) ≠ 0 :=
    (boundaryFactor_even_multiple_reciprocal_reduction hp2 hm0 hmEven hm).2.1
  have hIsq := hsquare hI
  have hmweight : boundaryMinusWeight m = 2 * I ^ 2 := by
    dsimp only [I]
    simpa using (boundaryMinusWeight_even_scaled_eq (p := 1) hmEven)
  have hmw := rational_residue_mul (p := p) (a := (2 : ℚ)) (b := I ^ 2) (by norm_num) hIsq.1
  have hmwden : ((boundaryMinusWeight m).den : ZMod p) ≠ 0 := by
    simpa only [hmweight] using hmw.1
  have hmwR : R (boundaryMinusWeight m) = 2 * R I ^ 2 := by
    rw [hmweight]
    calc
      _ = R 2 * R (I ^ 2) := hmw.2
      _ = _ := by rw [htwo, hIsq.2]
  have hmp : p ≤ m * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  have hmpeven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hterm (j : ℕ) (hj : j ∈ Finset.range ((p - 1) / 2 + 1)) :
      (((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p) ≠ 0 ∧
        R ((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)) =
          R (centralCoeff j) ^ 2 * R (boundaryMinusWeight m) := by
    have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
    have hjlt : 2 * j < p := by
      have := Finset.mem_range.mp hj
      omega
    have hzEven : (m * p - 2 * j) % 2 = 0 := by omega
    have hblock := boundaryFactor_even_block_reciprocal_reduction hp2 hm0 hmEven hm hjlt
    have hF : R (F j) = R (centralCoeff j) * R I := hblock.2.2.2
    have hFsq := hsquare hblock.1
    have hFsqR : R (F j ^ 2) = R (F j) ^ 2 := hFsq.2
    have hprod := rational_residue_mul (p := p) (a := (2 : ℚ)) (b := F j ^ 2)
      (by norm_num) hFsq.1
    have heq : (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j) = 2 * F j ^ 2 :=
      boundaryMinusWeight_even_scaled_eq hzEven
    refine ⟨by simpa only [heq] using hprod.1, ?_⟩
    rw [heq]
    calc
      _ = R 2 * R (F j ^ 2) := hprod.2
      _ = R (centralCoeff j) ^ 2 * R (boundaryMinusWeight m) := by
        rw [htwo, hFsqR, hF, hmwR]
        ring
  have hsum := rational_residue_sum (p := p) (Finset.range ((p - 1) / 2 + 1))
    (fun j => (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j))
    (fun j hj => (hterm j hj).1)
  refine ⟨hsum.1, hmwden, ?_⟩
  rw [hsum.2]
  calc
    _ = ∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        R (centralCoeff j) ^ 2 * R (boundaryMinusWeight m) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).2
    _ = (∑ j ∈ Finset.range ((p - 1) / 2 + 1), R (centralCoeff j) ^ 2) *
        R (boundaryMinusWeight m) := (Finset.sum_mul _ _ _).symm
    _ = _ := by
      have hc : (∑ j ∈ Finset.range ((p - 1) / 2 + 1), R (centralCoeff j) ^ 2) =
          (-1 : ZMod p) ^ ((p - 1) / 2) := centralCoeff_residue_square_block hp2
      rw [hc]

end InternalCatalan

end


namespace InternalCatalan

private theorem lowerStrip_pred_succ (n : ℕ) :
    momentScalarPred (n + 1) = momentScalar n := by
  simp [momentScalarPred]

theorem momentLowerStrip_term_zero {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : u + j + 1 < p ^ 2) (hnd : ¬p ∣ j + 1) :
    (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
        (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) = 0 := by
  have hs := momentScalarPred_prime_digit_reduction hp2 hb
  have hj : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hnd ((ZMod.natCast_eq_zero_iff (j + 1) p).mp hzero)
  have hf := nat_fraction_reduced_residue p (j + 1) hj
  have hm := rational_residue_mul hs.1 hf.1
  have heq : (p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (u + j + 1)) *
        ((p : ℚ) / ((j + 1 : ℕ) : ℚ)) := by
    rw [lowerStrip_pred_succ]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hm.1
  · rw [heq, hm.2, hf.2]
    simp

theorem momentLowerStrip_term_multiple {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : u + j + 1 < p ^ 2) (hd : p ∣ j + 1) :
    (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      ((momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
          (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ)).num : ZMod p) /
                ((momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ)).den : ZMod p)) := by
  have hsucc : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hd
  have hjmul : j + 1 = p * (j / p + 1) := by
    rw [← hsucc]
    exact (Nat.mul_div_cancel' hd).symm
  have hquot : (u + j + 1) / p = u / p + (j / p + 1) := by
    rw [show u + j + 1 = u + (j + 1) by omega, hjmul]
    exact Nat.add_mul_div_left u (j / p + 1) hp.out.pos
  have hrem : (u + j + 1) % p = u % p := by
    rw [show u + j + 1 = u + (j + 1) by omega, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hd, add_zero, Nat.mod_mod]
  have hzsmall : (u + j + 1) / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hb)
  have hqsmall : j / p + 1 < p := by
    rw [hquot] at hzsmall
    exact (Nat.le_add_left (j / p + 1) (u / p)).trans_lt hzsmall
  have hqnot : ¬p ∣ j / p + 1 :=
    Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (j / p)) hqsmall
  have hqden : ((j / p + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hqnot ((ZMod.natCast_eq_zero_iff (j / p + 1) p).mp hzero)
  have hf := nat_fraction_reduced_residue 1 (j / p + 1) hqden
  simp only [Nat.cast_one] at hf
  have hs := momentScalarPred_prime_digit_reduction hp2 hb
  have hl := rational_residue_mul hs.1 hf.1
  have hr := rational_residue_mul hs.2.1 hf.1
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hqq : ((j / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hjcast : ((j + 1 : ℕ) : ℚ) =
      (p : ℚ) * ((j / p + 1 : ℕ) : ℚ) := by exact_mod_cast hjmul
  have hpred : momentScalarPred ((u + j + 1) / p) = momentScalar (u / p + j / p) := by
    rw [hquot, show u / p + (j / p + 1) = (u / p + j / p) + 1 by omega,
      lowerStrip_pred_succ]
  have hleft : (p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (u + j + 1)) *
        (1 / ((j / p + 1 : ℕ) : ℚ)) := by
    rw [lowerStrip_pred_succ, hjcast]
    field_simp [hpq, hqq]
  have hright : momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ) =
      momentScalarPred ((u + j + 1) / p) * (1 / ((j / p + 1 : ℕ) : ℚ)) := by
    rw [hpred]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl.1
  · rw [hright]
    exact hr.1
  · rw [hleft, hl.2, hs.2.2, hrem, hright, hr.2]
    ring

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

private theorem parityBoundarySum_even_range (f : ℕ → ℚ) (a : ℕ) :
    parityBoundarySum f (2 * a) =
      ∑ k ∈ Finset.range a, f (2 * (k + 1)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 2 by omega,
      parityBoundarySum_step, ih, Finset.sum_range_succ]
    congr 2

private theorem boundaryMinusWeight_even_residue_block {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0) (hm : m < p) :
    (∑ j ∈ Finset.range ((p - 1) / 2 + 1),
      (((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p)) =
      (-1 : ZMod p) ^ ((p - 1) / 2) *
        (((boundaryMinusWeight m).num : ZMod p) / ((boundaryMinusWeight m).den : ZMod p)) := by
  have hmp : p ≤ m * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  have hmpsmall : m * p < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hm hp.out.pos
  have hmpeven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hsum := rational_residue_sum (p := p) (Finset.range ((p - 1) / 2 + 1))
    (fun j => (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)) (by
      intro j hj
      have hjlt : 2 * j < p := by have := Finset.mem_range.mp hj; omega
      exact boundaryMinusWeight_even_scaled_den_ne_zero hp2 (by omega)
        (by omega) (by omega))
  exact hsum.2.symm.trans
    (boundaryMinusWeight_even_block_sum_reduction hp2 hm0 hmEven hm).2.2

private theorem boundaryMinus_small_even_residue_sum {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p) :
    ((boundaryMinus u).num : ZMod p) / ((boundaryMinus u).den : ZMod p) =
      (((boundaryFactor u).num : ZMod p) / ((boundaryFactor u).den : ZMod p)) *
        ∑ a ∈ Finset.range (u / 2),
          ((boundaryMinusWeight (2 * (a + 1))).num : ZMod p) /
            ((boundaryMinusWeight (2 * (a + 1))).den : ZMod p) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hsum := rational_residue_sum (p := p) (Finset.range (u / 2))
    (fun a => boundaryMinusWeight (2 * (a + 1))) (by
      intro a ha
      have ha' := Finset.mem_range.mp ha
      exact (boundaryMinusWeight_even_block_sum_reduction hp2
        (by omega : 0 < 2 * (a + 1)) (by omega) (by omega)).2.1)
  have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 :=
    (boundaryFactor_even_digit_reduction hp2 huEven
      (by simpa only [Nat.mod_eq_of_lt hu] using huEven)).1
  have hprod := rational_residue_mul (p := p) hH hsum.1
  have hparity : parityBoundarySum boundaryMinusWeight u =
      ∑ a ∈ Finset.range (u / 2), boundaryMinusWeight (2 * (a + 1)) := by
    have h := parityBoundarySum_even_range boundaryMinusWeight (u / 2)
    simpa only [show 2 * (u / 2) = u by omega] using h
  rw [boundaryMinus_explicit, hparity]
  calc
    _ = R (boundaryFactor u) *
        R (∑ a ∈ Finset.range (u / 2), boundaryMinusWeight (2 * (a + 1))) := hprod.2
    _ = _ := by
      congr 1
      exact hsum.2

theorem boundaryMinus_even_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((boundaryMinus (u / p)).num : ZMod p) /
                ((boundaryMinus (u / p)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hP : u / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hu)
  have hr : u % p < p := Nat.mod_lt _ hp.out.pos
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have htarget : ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ hP)
  refine ⟨boundaryMinus_prime_sq_scaled_den_ne_zero hp2 hu, htarget, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryMinus u) =
    (oddPrimeWeight p).coeff (p - 1 - u % p) * R (boundaryMinus (u / p))
  by_cases hrEven : (u % p) % 2 = 0
  · have hPpar := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div u p)
    simp only [Nat.add_mod, Nat.mul_mod, hrEven, hpOdd, zero_add, one_mul,
      Nat.mod_mod, huEven] at hPpar
    have hsupport :
        (∑ z ∈ Finset.range (u + 1),
          if 0 < z ∧ z % 2 = 0 then R ((p : ℚ) ^ 2 * boundaryMinusWeight z) else 0) =
        ∑ z ∈ (Finset.range (u + 1)).filter
          (fun z => 0 < z ∧ z % 2 = 0 ∧ (z % p = 0 ∨ (z % p) % 2 = 1)),
            R ((p : ℚ) ^ 2 * boundaryMinusWeight z) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hz0 : 0 < z
      · by_cases hzEven : z % 2 = 0
        · by_cases hsurvive : z % p = 0 ∨ (z % p) % 2 = 1
          · simp [hz0, hzEven, hsurvive]
          · have hzero := boundaryMinusWeight_even_no_carry_reduction hp2 hz0 hzEven
              (by have := Finset.mem_range.mp hz; omega)
              (fun h => hsurvive (Or.inl h)) (by omega)
            have hzR : R ((p : ℚ) ^ 2 * boundaryMinusWeight z) = 0 := hzero.2
            simp [hz0, hzEven, hsurvive, hzR]
        · simp [hzEven]
      · simp [hz0]
    have hS :
        (∑ z ∈ Finset.range (u + 1),
          if 0 < z ∧ z % 2 = 0 then R ((p : ℚ) ^ 2 * boundaryMinusWeight z) else 0) =
          (-1 : ZMod p) ^ ((p - 1) / 2) *
            ∑ a ∈ Finset.range ((u / p) / 2), R (boundaryMinusWeight (2 * (a + 1))) := by
      rw [hsupport, even_surviving_sum_eq_complete_blocks hpOdd huEven hrEven]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      exact boundaryMinusWeight_even_residue_block hp2 (by omega)
        (by omega) (by omega)
    have hH := boundaryFactor_even_digit_reduction hp2 huEven hrEven
    have hHR : R (boundaryFactor u) =
        R (boundaryFactor (u / p)) * R (centralCoeff ((u % p) / 2)) := hH.2.2.2
    have hc : R (centralCoeff ((u % p) / 2)) = (oddPrimeWeight p).coeff (u % p) := by
      change ((centralCoeff ((u % p) / 2)).num : ZMod p) /
        ((centralCoeff ((u % p) / 2)).den : ZMod p) = _
      rw [(centralCoeff_reduced_residue hp2 ((u % p) / 2)).2]
      symm
      simpa only [show 2 * ((u % p) / 2) = u % p by omega] using
        (oddPrimeWeight_coeff_central hp2 (show 2 * ((u % p) / 2) < p by omega))
    have hB := boundaryMinus_small_even_residue_sum hp2 hPpar hP
    have hBR : R (boundaryMinus (u / p)) =
        R (boundaryFactor (u / p)) *
          ∑ a ∈ Finset.range ((u / p) / 2), R (boundaryMinusWeight (2 * (a + 1))) := hB
    have hbigR : R ((p : ℚ) ^ 2 * boundaryMinus u) =
        R (boundaryFactor u) *
          ∑ z ∈ Finset.range (u + 1),
            if 0 < z ∧ z % 2 = 0 then R ((p : ℚ) ^ 2 * boundaryMinusWeight z) else 0 :=
      (boundaryMinus_even_scaled_residue_sum hp2 huEven hu).2
    rw [hbigR, hS, hHR, oddPrimeWeight_coeff_reverse hp.out hp2 hr, ← hc, hBR]
    ring
  · have hzero := boundaryMinus_even_odd_remainder_zero hp2 huEven hu (by omega)
    have hzeroR : R ((p : ℚ) ^ 2 * boundaryMinus u) = 0 := hzero.2
    have hcoeff : (oddPrimeWeight p).coeff (p - 1 - u % p) = 0 := by
      rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
        oddPrimeWeight_coeff_odd p (u % p) hrEven, mul_zero]
    rw [hzeroR, hcoeff, zero_mul]

end InternalCatalan

end


namespace InternalCatalan

open scoped BigOperators

def momentLowerStrip (u j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range j, momentScalar (u + k) / ((k + 1 : ℕ) : ℚ)

@[simp] theorem momentLowerStrip_zero (u : ℕ) : momentLowerStrip u 0 = 0 := by
  simp [momentLowerStrip]

theorem momentLowerStrip_succ (u j : ℕ) :
    momentLowerStrip u (j + 1) = momentLowerStrip u j +
      momentScalar (u + j) / ((j + 1 : ℕ) : ℚ) := by
  unfold momentLowerStrip
  rw [Finset.sum_range_succ]

theorem momentRat_lower_strip (u j : ℕ) :
    momentRat (u + j) j = boundaryMinus u - momentLowerStrip u j := by
  simpa only [momentLowerStrip, Nat.add_sub_cancel_right] using
    (momentRat_of_le (by omega : j ≤ u + j))

theorem momentLowerStrip_prime_digit_reduction {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : u + j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentLowerStrip u j).den : ZMod p) ≠ 0 ∧
      ((momentLowerStrip (u / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentLowerStrip u j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentLowerStrip u j).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((momentLowerStrip (u / p) (j / p)).num : ZMod p) /
                ((momentLowerStrip (u / p) (j / p)).den : ZMod p)) := by
  revert hbound
  induction j with
  | zero => intro hbound; simp
  | succ j ih =>
    intro hbound
    have hprev := ih (by omega : u + j < p ^ 2)
    have hscale : (p : ℚ) ^ 2 * momentLowerStrip u (j + 1) =
        (p : ℚ) ^ 2 * momentLowerStrip u j +
          (p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ)) := by
      rw [momentLowerStrip_succ, mul_add]
    by_cases hdiv : p ∣ j + 1
    · have ht := momentLowerStrip_term_multiple hp2
        (by omega : u + j + 1 < p ^ 2) hdiv
      have hquot : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hdiv
      have hsmall : momentLowerStrip (u / p) ((j + 1) / p) =
          momentLowerStrip (u / p) (j / p) +
            momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ) := by
        rw [hquot, momentLowerStrip_succ]
      have hl := rational_residue_add hprev.1 ht.1
      have hr := rational_residue_add hprev.2.1 ht.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hsmall]
        exact hr.1
      · rw [hscale, hl.2, hprev.2.2, ht.2.2, hsmall, hr.2]
        ring
    · have ht := momentLowerStrip_term_zero hp2
        (by omega : u + j + 1 < p ^ 2) hdiv
      have hquot : (j + 1) / p = j / p := Nat.succ_div_of_not_dvd hdiv
      have hl := rational_residue_add hprev.1 ht.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, ht.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan



namespace InternalCatalan

theorem boundaryMinus_prime_digit_reduction {p u : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((boundaryMinus (u / p)).num : ZMod p) /
                ((boundaryMinus (u / p)).den : ZMod p)) := by
  by_cases hEven : u % 2 = 0
  · exact boundaryMinus_even_digit_reduction hp2 hEven hu
  · exact boundaryMinus_odd_digit_reduction hp2 (by omega) hu

theorem momentRat_lower_prime_digit_reduction {p u j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : u + j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat (u + j) j).den : ZMod p) ≠ 0 ∧
      ((momentRat (u / p + j / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat (u + j) j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat (u + j) j).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((momentRat (u / p + j / p) (j / p)).num : ZMod p) /
                ((momentRat (u / p + j / p) (j / p)).den : ZMod p)) := by
  have hstart := boundaryMinus_prime_digit_reduction hp2 (show u < p ^ 2 by omega)
  have hstrip := momentLowerStrip_prime_digit_reduction hp2 hbound
  have hl := rational_residue_sub hstart.1 hstrip.1
  have hr := rational_residue_sub hstart.2.1 hstrip.2.1
  have hleft : (p : ℚ) ^ 2 * momentRat (u + j) j =
      (p : ℚ) ^ 2 * boundaryMinus u - (p : ℚ) ^ 2 * momentLowerStrip u j := by
    rw [momentRat_lower_strip, mul_sub]
  have hright : momentRat (u / p + j / p) (j / p) =
      boundaryMinus (u / p) - momentLowerStrip (u / p) (j / p) :=
    momentRat_lower_strip (u / p) (j / p)
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl.1
  · rw [hright]
    exact hr.1
  · rw [hleft, hl.2, hstart.2.2, hstrip.2.2, hright, hr.2]
    ring

theorem momentRat_prime_digit_reduction_of_le {p i j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hji : j ≤ i) (hi : i < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      ((momentRat ((i - j) / p + j / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - (i - j) % p) *
              (((momentRat ((i - j) / p + j / p) (j / p)).num : ZMod p) /
                ((momentRat ((i - j) / p + j / p) (j / p)).den : ZMod p)) := by
  simpa only [Nat.sub_add_cancel hji] using
    momentRat_lower_prime_digit_reduction hp2
      (show i - j + j < p ^ 2 by omega)

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.PalindromicPrimeGeom
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_one_sub_X_sq_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
  intro h
  have hcoeff : (1 : ZMod p) = 0 := by
    simpa [coeff_sub, coeff_one, coeff_X_pow] using
      congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
  exact one_ne_zero hcoeff

theorem palindromic_prime_geometric_identity {p : ℕ} [Fact p.Prime] :
    (∑ j ∈ Finset.range p, (X : (ZMod p)[X]) ^ (2 * j)) =
      (1 - X ^ 2) ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum : (∑ j ∈ Finset.range p, (X : (ZMod p)[X]) ^ (2 * j)) =
      ∑ j ∈ Finset.range p, ((X : (ZMod p)[X]) ^ 2) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact pow_mul (X : (ZMod p)[X]) 2 j
  apply mul_right_cancel₀ (palindromic_one_sub_X_sq_ne_zero (p := p))
  calc
    (∑ j ∈ Finset.range p, (X : (ZMod p)[X]) ^ (2 * j)) * (1 - X ^ 2) =
        1 - (X ^ 2) ^ p := by
      rw [hsum]
      exact geom_sum_mul_neg (X ^ 2 : (ZMod p)[X]) p
    _ = (1 - X ^ 2) ^ p := by rw [sub_pow_char, one_pow]
    _ = (1 - X ^ 2) ^ (p - 1) * (1 - X ^ 2) := by
      rw [← pow_succ, show p - 1 + 1 = p by omega]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.PalindromicStarParameters
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial

def palindromicRatW (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) X

def palindromicRatT (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  2 * palindromicRatW p / (1 + palindromicRatW p ^ 2)

def palindromicRatF (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - palindromicRatW p ^ 2) / (1 + palindromicRatW p ^ 2)

def palindromicRatE (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - palindromicRatT p ^ 2) ^ ((p - 1) / 2)

theorem palindromicRat_map_one_add_X_sq {p : ℕ} [Fact p.Prime] :
    algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (1 + X ^ 2) =
      1 + palindromicRatW p ^ 2 := by
  simp [palindromicRatW]


theorem palindromic_one_add_X_sq_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 + X ^ 2 : (ZMod p)[X]) ≠ 0 := by
  intro h
  have hcoeff : (1 : ZMod p) = 0 := by
    simpa [coeff_one, coeff_X_pow] using
      congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
  exact one_ne_zero hcoeff

theorem palindromicRat_denominator_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 + palindromicRatW p ^ 2 : RatFunc (ZMod p)) ≠ 0 := by
  intro h
  apply palindromic_one_add_X_sq_ne_zero (p := p)
  apply RatFunc.algebraMap_injective (ZMod p)
  simpa only [palindromicRat_map_one_add_X_sq, map_zero] using h

theorem palindromicRat_F_sq {p : ℕ} [Fact p.Prime] :
    palindromicRatF p ^ 2 = 1 - palindromicRatT p ^ 2 := by
  unfold palindromicRatF palindromicRatT
  field_simp [palindromicRat_denominator_ne_zero (p := p)]
  ring

theorem palindromic_prime_pred_twice_half {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : 2 * ((p - 1) / 2) = p - 1 := by
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).even_sub_one hp2
  omega

theorem palindromicRat_E_eq_F_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatE p = palindromicRatF p ^ (p - 1) := by
  unfold palindromicRatE
  rw [← palindromicRat_F_sq, ← pow_mul, palindromic_prime_pred_twice_half hp2]

end InternalCatalan





namespace InternalCatalan

open Polynomial

theorem palindromicRatW_transcendental {p : ℕ} [Fact p.Prime] :
    Transcendental (ZMod p) (palindromicRatW p) := by
  unfold palindromicRatW
  rw [transcendental_algebraMap_iff (RatFunc.algebraMap_injective (ZMod p))]
  exact Polynomial.transcendental_X (ZMod p)


theorem palindromicRatW_inv_transcendental {p : ℕ} [Fact p.Prime] :
    Transcendental (ZMod p) (palindromicRatW p)⁻¹ := by
  intro h
  exact palindromicRatW_transcendental (IsAlgebraic.inv_iff.mp h)

theorem palindromicRatW_inv_eval₂RingHom_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective
      (eval₂RingHom (algebraMap (ZMod p) (RatFunc (ZMod p)))
        (palindromicRatW p)⁻¹) :=
  transcendental_iff_injective.mp palindromicRatW_inv_transcendental

def palindromicRatStar (p : ℕ) [Fact p.Prime] :
    RatFunc (ZMod p) →+* RatFunc (ZMod p) :=
  RatFunc.liftRingHom
    (eval₂RingHom (algebraMap (ZMod p) (RatFunc (ZMod p)))
      (palindromicRatW p)⁻¹)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (palindromicRatW_inv_eval₂RingHom_injective (p := p)))

theorem palindromicRatStar_map_polynomial {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) :
    palindromicRatStar p (algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) P) =
      eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatW p)⁻¹ P := by
  exact RatFunc.liftRingHom_algebraMap _ _ P

@[simp]
theorem palindromicRatStar_W {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatW p) = (palindromicRatW p)⁻¹ := by
  exact (palindromicRatStar_map_polynomial (p := p) X).trans (eval₂_X _ _)

@[simp]
theorem palindromicRatStar_scalar {p : ℕ} [Fact p.Prime] (c : ZMod p) :
    palindromicRatStar p (algebraMap (ZMod p) (RatFunc (ZMod p)) c) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) c := by
  have hc : algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C c) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) c := by
    simpa only [map_one, div_one, Polynomial.algebraMap_eq] using
      (RatFunc.algebraMap_apply (K := ZMod p) (R := ZMod p) c).symm
  calc
    palindromicRatStar p (algebraMap (ZMod p) (RatFunc (ZMod p)) c) =
        palindromicRatStar p
          (algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C c)) :=
      congrArg (palindromicRatStar p) hc.symm
    _ = _ := by rw [palindromicRatStar_map_polynomial, eval₂_C]


end InternalCatalan





namespace InternalCatalan

open Polynomial

theorem palindromicRatT_ne_C {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ ∃ c : ZMod p, palindromicRatT p = algebraMap (ZMod p) (RatFunc (ZMod p)) c := by
  rintro ⟨c, hc⟩
  have hmul : 2 * palindromicRatW p =
      algebraMap (ZMod p) (RatFunc (ZMod p)) c * (1 + palindromicRatW p ^ 2) := by
    exact (div_eq_iff (palindromicRat_denominator_ne_zero (p := p))).mp hc
  have hpoly : C (2 : ZMod p) * X = C c * (1 + X ^ 2) := by
    apply RatFunc.algebraMap_injective (ZMod p)
    have hC (a : ZMod p) :
        algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C a) =
          algebraMap (ZMod p) (RatFunc (ZMod p)) a := rfl
    simpa only [map_mul, map_add, map_one, map_pow, hC, map_ofNat,
      palindromicRatW] using hmul
  have hcoeff : (2 : ZMod p) = 0 := by
    simpa [coeff_C_mul, coeff_one, coeff_X_pow] using
      congrArg (fun P : (ZMod p)[X] => P.coeff 1) hpoly
  exact palindromic_two_ne_zero hp2 hcoeff

theorem palindromicRatT_transcendental {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Transcendental (ZMod p) (palindromicRatT p) := by
  intro ht
  let S : Subalgebra (ZMod p) (RatFunc (ZMod p)) :=
    Subalgebra.algebraicClosure (ZMod p) (RatFunc (ZMod p))
  let t : S := ⟨palindromicRatT p, ht⟩
  have hw : Transcendental (ZMod p) (palindromicRatW p) := by
    unfold palindromicRatW
    rw [transcendental_algebraMap_iff (RatFunc.algebraMap_injective (ZMod p))]
    exact Polynomial.transcendental_X (ZMod p)
  have hwS : Transcendental S (palindromicRatW p) :=
    hw.subalgebraAlgebraicClosure
  apply hwS
  refine ⟨C t * (1 + X ^ 2) - C (2 : S) * X, ?_, ?_⟩
  · intro hpoly
    have ht0 : t = 0 := by
      simpa [coeff_C_mul, coeff_one, coeff_X_pow] using
        congrArg (fun Q : S[X] => Q.coeff 0) hpoly
    have ht0' : palindromicRatT p = 0 :=
      congrArg (fun a : S => (a : RatFunc (ZMod p))) ht0
    exact palindromicRatT_ne_C hp2 ⟨0, by simpa only [map_zero] using ht0'⟩
  · have htcoe : algebraMap S (RatFunc (ZMod p)) t = palindromicRatT p := rfl
    simp only [map_sub, map_mul, map_add, map_one, map_pow, aeval_C, aeval_X,
      htcoe, map_ofNat]
    rw [palindromicRatT,
      div_mul_cancel₀ _ (palindromicRat_denominator_ne_zero (p := p)), sub_self]

theorem palindromicRatT_aeval_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Function.Injective
      (aeval (palindromicRatT p) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)) :=
  transcendental_iff_injective.mp (palindromicRatT_transcendental hp2)

theorem palindromicRatT_eval₂RingHom_injective {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Function.Injective
      (eval₂RingHom (algebraMap (ZMod p) (RatFunc (ZMod p)))
        (palindromicRatT p)) :=
  palindromicRatT_aeval_injective hp2


end InternalCatalan





namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_denominator_cleared_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    (X : (ZMod p)[X]) ^ i.val * (1 - X ^ 2) ^ (p - 1) =
      ∑ l : Fin p, (C (palindromicTransitionMatrix p l i) +
        C (palindromicReversedTransitionMatrix p l i) * X ^ p) *
          palindromicU p l.val := by
  rw [← palindromic_prime_geometric_identity]
  exact palindromicPairing_eq_sum_U hp2 i

theorem palindromicRat_map_C {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (C a) =
      algebraMap (ZMod p) (RatFunc (ZMod p)) a := by
  simpa only [map_one, div_one, Polynomial.algebraMap_eq] using
    (RatFunc.algebraMap_apply (K := ZMod p) (R := ZMod p) a).symm

theorem palindromicRat_map_U {p : ℕ} [Fact p.Prime] (l : Fin p) :
    algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)) (palindromicU p l.val) =
      palindromicRatT p ^ l.val * (1 + palindromicRatW p ^ 2) ^ (p - 1) := by
  have hle : l.val ≤ p - 1 := by have h := l.isLt; omega
  have hpow : (1 + palindromicRatW p ^ 2) ^ l.val *
      (1 + palindromicRatW p ^ 2) ^ (p - 1 - l.val) =
        (1 + palindromicRatW p ^ 2) ^ (p - 1) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  simp only [palindromicU, map_mul, map_pow, map_add, map_one, map_ofNat]
  change (2 * palindromicRatW p) ^ l.val *
      (1 + palindromicRatW p ^ 2) ^ (p - 1 - l.val) = _
  rw [palindromicRatT, div_pow, ← hpow, ← mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero _ (palindromicRat_denominator_ne_zero (p := p)))]

theorem palindromicRat_F_pow_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicRatF p ^ (p - 1) * palindromicRatW p ^ i.val =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) * palindromicRatW p ^ p) := by
  have hmap := congrArg (algebraMap ((ZMod p)[X]) (RatFunc (ZMod p)))
    (palindromic_denominator_cleared_expansion hp2 i)
  simp only [map_mul, map_pow, map_sub, map_one, map_sum, map_add,
    palindromicRat_map_C, palindromicRat_map_U] at hmap
  change palindromicRatW p ^ i.val * (1 - palindromicRatW p ^ 2) ^ (p - 1) =
    ∑ l : Fin p,
      (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) +
        algebraMap (ZMod p) (RatFunc (ZMod p))
          (palindromicReversedTransitionMatrix p l i) * palindromicRatW p ^ p) *
        (palindromicRatT p ^ l.val * (1 + palindromicRatW p ^ 2) ^ (p - 1)) at hmap
  apply mul_right_cancel₀
    (pow_ne_zero (p - 1) (palindromicRat_denominator_ne_zero (p := p)))
  calc
    (palindromicRatF p ^ (p - 1) * palindromicRatW p ^ i.val) *
        (1 + palindromicRatW p ^ 2) ^ (p - 1) =
      palindromicRatW p ^ i.val * (1 - palindromicRatW p ^ 2) ^ (p - 1) := by
        rw [palindromicRatF, div_pow]
        field_simp [palindromicRat_denominator_ne_zero (p := p)]
    _ = _ := hmap
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem palindromicRat_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicRatE p * palindromicRatW p ^ i.val =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) * palindromicRatW p ^ p) := by
  rw [palindromicRat_E_eq_F_pow hp2]
  exact palindromicRat_F_pow_expansion hp2 i

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromicRat_W_ne_zero {p : ℕ} [Fact p.Prime] :
    palindromicRatW p ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_ne_zero (R := ZMod p))




theorem palindromicRat_F_mul_E {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatF p * palindromicRatE p = palindromicRatF p ^ p := by
  have hp : 1 ≤ p := by have h := (Fact.out : p.Prime).pos; omega
  rw [palindromicRat_E_eq_F_pow hp2, ← pow_succ', Nat.sub_add_cancel hp]

def palindromicRatRow (p N r : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - palindromicRatT p) ^ (2 * N) * palindromicRatT p ^ (63 * N) *
    palindromicRatW p ^ ((r : ℤ) - ((4 * N : ℕ) : ℤ))

theorem palindromicRatRow_successor {p : ℕ} [Fact p.Prime] (N r : ℕ) :
    palindromicRatRow p N (r + 1) =
      palindromicRatRow p N r * palindromicRatW p := by
  simp only [palindromicRatRow,
    zpow_natCast_sub_natCast₀ (palindromicRat_W_ne_zero (p := p)), pow_succ]
  ring

theorem palindromicRatRow_scale {p : ℕ} [Fact p.Prime] (r₀ i : ℕ) :
    palindromicRatRow p p (p * r₀ + i) =
      palindromicRatRow p 1 r₀ ^ p * palindromicRatW p ^ i := by
  simp only [palindromicRatRow, mul_one,
    zpow_natCast_sub_natCast₀ (palindromicRat_W_ne_zero (p := p)),
    mul_pow, div_pow, ← pow_mul]
  rw [pow_add, Nat.mul_comm r₀ p]
  ring

theorem palindromicRatRow_expansion {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (r₀ : ℕ) (i : Fin p) :
    palindromicRatRow p p (p * r₀ + i.val) * palindromicRatE p =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) *
            palindromicRatRow p 1 r₀ ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
              palindromicRatRow p 1 (r₀ + 1) ^ p) := by
  rw [palindromicRatRow_scale]
  have he := palindromicRat_expansion hp2 i
  calc
    (palindromicRatRow p 1 r₀ ^ p * palindromicRatW p ^ i.val) *
        palindromicRatE p =
      palindromicRatRow p 1 r₀ ^ p *
        (palindromicRatE p * palindromicRatW p ^ i.val) := by ring
    _ = _ := by
      rw [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [palindromicRatRow_successor, mul_pow]
      ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial

theorem chebyshev_signed_laurent_eval {K : Type*} [Field K]
    (φ : ℤ →+* K) (x y w : K) (hw : w ≠ 0)
    (hxy : x - y = w) (hcurve : y ^ 2 = x ^ 2 - 1) (m : ℤ) :
    (Chebyshev.T ℤ m).eval₂ φ x -
        y * (Chebyshev.U ℤ (m - 1)).eval₂ φ x = w ^ m := by
  let A : ℤ → K := fun n =>
    (Chebyshev.T ℤ n).eval₂ φ x - y * (Chebyshev.U ℤ (n - 1)).eval₂ φ x
  have hT (n : ℤ) : (Chebyshev.T ℤ (n + 1)).eval₂ φ x =
      x * (Chebyshev.T ℤ n).eval₂ φ x -
        (1 - x ^ 2) * (Chebyshev.U ℤ (n - 1)).eval₂ φ x := by
    have h := congrArg (fun P : ℤ[X] => P.eval₂ φ x)
      (Chebyshev.T_eq_X_mul_T_sub_pol_U ℤ (n - 1))
    simpa only [show n - 1 + 2 = n + 1 by omega, sub_add_cancel,
      eval₂_sub, eval₂_mul, eval₂_X, eval₂_one, eval₂_pow] using h
  have hU (n : ℤ) : (Chebyshev.U ℤ n).eval₂ φ x =
      x * (Chebyshev.U ℤ (n - 1)).eval₂ φ x +
        (Chebyshev.T ℤ n).eval₂ φ x := by
    have h := congrArg (fun P : ℤ[X] => P.eval₂ φ x)
      (Chebyshev.U_eq_X_mul_U_add_T ℤ (n - 1))
    simpa only [sub_add_cancel, eval₂_add, eval₂_mul, eval₂_X] using h
  have hstep (n : ℤ) : A (n + 1) = w * A n := by
    simp only [A, show n + 1 - 1 = n by omega, hT n, hU n]
    rw [← hxy]
    linear_combination -((Chebyshev.U ℤ (n - 1)).eval₂ φ x) * hcurve
  change A m = w ^ m
  induction m using Int.induction_on with
  | zero => simp [A]
  | succ n ih =>
    rw [hstep, ih, zpow_add₀ hw, zpow_one]
    exact mul_comm _ _
  | pred n ih =>
    apply mul_left_cancel₀ hw
    calc
      w * A (-(n : ℤ) - 1) = A (-(n : ℤ)) := by
        rw [← hstep, show (-(n : ℤ) - 1) + 1 = -(n : ℤ) by omega]
      _ = w ^ (-(n : ℤ)) := ih
      _ = w * w ^ (-(n : ℤ) - 1) := by
        rw [zpow_sub₀ hw, zpow_one]
        field_simp [hw]

theorem palindromicRat_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : RatFunc (ZMod p)) ≠ 0 := by
  have hpoly : (2 : (ZMod p)[X]) ≠ 0 := by
    intro h
    apply palindromic_two_ne_zero hp2
    simpa using congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
  have hmap := RatFunc.algebraMap_ne_zero hpoly
  simpa only [map_ofNat] using hmap

theorem palindromicRat_T_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatT p ≠ 0 :=
  div_ne_zero (mul_ne_zero (palindromicRat_two_ne_zero hp2)
    palindromicRat_W_ne_zero) palindromicRat_denominator_ne_zero

theorem palindromicRat_invT_sub_F_div_T {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (palindromicRatT p)⁻¹ - palindromicRatF p / palindromicRatT p =
      palindromicRatW p := by
  unfold palindromicRatT palindromicRatF
  field_simp [palindromicRat_W_ne_zero (p := p), palindromicRat_two_ne_zero hp2,
    palindromicRat_denominator_ne_zero (p := p)]
  ring

theorem palindromicRat_F_div_T_sq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (palindromicRatF p / palindromicRatT p) ^ 2 =
      ((palindromicRatT p)⁻¹) ^ 2 - 1 := by
  rw [div_pow, palindromicRat_F_sq]
  field_simp [palindromicRat_T_ne_zero hp2]

theorem palindromicRat_chebyshev_signed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (m : ℤ) :
    palindromicRatT p *
        (Chebyshev.T ℤ m).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p)⁻¹ -
      palindromicRatF p *
        (Chebyshev.U ℤ (m - 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p)⁻¹ =
      palindromicRatT p * palindromicRatW p ^ m := by
  have heval := chebyshev_signed_laurent_eval
    (Int.castRingHom (RatFunc (ZMod p))) ((palindromicRatT p)⁻¹)
    (palindromicRatF p / palindromicRatT p) (palindromicRatW p)
    palindromicRat_W_ne_zero (palindromicRat_invT_sub_F_div_T hp2)
    (palindromicRat_F_div_T_sq hp2) m
  calc
    _ = palindromicRatT p *
        ((Chebyshev.T ℤ m).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
            (palindromicRatT p)⁻¹ -
          (palindromicRatF p / palindromicRatT p) *
            (Chebyshev.U ℤ (m - 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)⁻¹) := by
      field_simp [palindromicRat_T_ne_zero hp2]
    _ = _ := congrArg (fun z => palindromicRatT p * z) heval

end InternalCatalan





namespace InternalCatalan

open Polynomial

theorem palindromicRat_inverse_denominator_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 + ((palindromicRatW p)⁻¹) ^ 2 : RatFunc (ZMod p)) ≠ 0 := by
  have heq : 1 + ((palindromicRatW p)⁻¹) ^ 2 =
      (1 + palindromicRatW p ^ 2) / palindromicRatW p ^ 2 := by
    field_simp [palindromicRat_W_ne_zero (p := p)]
    ring
  rw [heq]
  exact div_ne_zero palindromicRat_denominator_ne_zero
    (pow_ne_zero _ palindromicRat_W_ne_zero)

@[simp] theorem palindromicRatStar_T {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatT p) = palindromicRatT p := by
  simp only [palindromicRatT, map_div₀, map_mul, map_ofNat, map_add,
    map_one, map_pow, palindromicRatStar_W]
  field_simp [palindromicRat_W_ne_zero (p := p),
    palindromicRat_denominator_ne_zero (p := p),
    palindromicRat_inverse_denominator_ne_zero (p := p)]
  linear_combination 2 *
    (mul_inv_cancel₀ (palindromicRat_denominator_ne_zero (p := p)))

@[simp] theorem palindromicRatStar_F {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatF p) = -palindromicRatF p := by
  simp only [palindromicRatF, map_div₀, map_sub, map_add,
    map_one, map_pow, palindromicRatStar_W]
  field_simp [palindromicRat_W_ne_zero (p := p),
    palindromicRat_denominator_ne_zero (p := p),
    palindromicRat_inverse_denominator_ne_zero (p := p)]
  linear_combination (palindromicRatW p ^ 2 - 1) *
    (mul_inv_cancel₀ (palindromicRat_denominator_ne_zero (p := p)))

@[simp] theorem palindromicRatStar_E {p : ℕ} [Fact p.Prime] :
    palindromicRatStar p (palindromicRatE p) = palindromicRatE p := by
  simp only [palindromicRatE, map_pow, map_sub, map_one, palindromicRatStar_T]

@[simp] theorem palindromicRatStar_F_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicRatStar p (palindromicRatF p ^ p) = -palindromicRatF p ^ p := by
  rw [← palindromicRat_F_mul_E hp2, map_mul, palindromicRatStar_F,
    palindromicRatStar_E, neg_mul, palindromicRat_F_mul_E hp2]

@[simp] theorem palindromicRatStar_eval₂ {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) :
    palindromicRatStar p
        (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) =
      P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) := by
  simp only [eval₂_eq_sum, sum_def, map_sum, map_mul, palindromicRatStar_scalar,
    map_pow, palindromicRatStar_T]

@[simp] theorem palindromicRatStar_eval₂_int {p : ℕ} [Fact p.Prime]
    (P : ℤ[X]) :
    palindromicRatStar p
        (P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)) =
      P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) := by
  have hcast (z : ℤ) : palindromicRatStar p
      ((Int.castRingHom (RatFunc (ZMod p))) z) =
      (Int.castRingHom (RatFunc (ZMod p))) z := by
    change palindromicRatStar p (z : RatFunc (ZMod p)) = z
    exact map_intCast (palindromicRatStar p) z
  simp only [eval₂_eq_sum, sum_def, map_sum, map_mul, hcast,
    map_pow, palindromicRatStar_T]

theorem palindromicRat_F_ne_zero {p : ℕ} [Fact p.Prime] :
    palindromicRatF p ≠ 0 := by
  apply div_ne_zero _ palindromicRat_denominator_ne_zero
  simpa only [map_sub, map_one, map_pow, palindromicRatW] using
    RatFunc.algebraMap_ne_zero (palindromic_one_sub_X_sq_ne_zero (p := p))

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.PalindromicPolynomialFrobenius
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromicRat_coefficient_frobenius {p : ℕ} [Fact p.Prime]
    (a : ZMod p) :
    (algebraMap (ZMod p) (RatFunc (ZMod p)) a) ^ p =
      algebraMap (ZMod p) (RatFunc (ZMod p)) a := by
  rw [← map_pow, ZMod.pow_card]

theorem palindromicRat_polynomial_eval₂_pow {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) (x : RatFunc (ZMod p)) :
    (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x) ^ p =
      P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (x ^ p) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [eval₂_add, add_pow_char, hP, hQ, eval₂_add]
  | monomial n a =>
    simp only [eval₂_monomial, mul_pow, palindromicRat_coefficient_frobenius]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n p]


theorem palindromicRat_polynomial_comp_X_pow_eval₂ {p : ℕ} [Fact p.Prime]
    (P : (ZMod p)[X]) (x : RatFunc (ZMod p)) :
    (P.comp (X ^ p)).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      (P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) x) ^ p := by
  rw [eval₂_comp, eval₂_X_pow]
  exact (palindromicRat_polynomial_eval₂_pow P x).symm


theorem palindromicRat_int_map_eval₂ {p : ℕ} [Fact p.Prime]
    (P : ℤ[X]) (x : RatFunc (ZMod p)) :
    (P.map (Int.castRingHom (ZMod p))).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
      P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) x := by
  have hmap : (algebraMap (ZMod p) (RatFunc (ZMod p))).comp
      (Int.castRingHom (ZMod p)) = Int.castRingHom (RatFunc (ZMod p)) := by
    ext z
    simp
  rw [eval₂_map, hmap]




theorem palindromicRat_PResidueSum_eval₂ {p : ℕ} [Fact p.Prime]
    (r0 : ℕ) (i : Fin p) :
    (palindromicPResidueSum p r0 i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      ∑ l : Fin p, palindromicRatT p ^ l.val * palindromicRatT p ^ p *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicTransitionMatrix p l i) *
            ((rowP 1 r0).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
            ((rowP 1 (r0 + 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p) := by
  simp only [palindromicPResidueSum, eval₂_finsetSum, eval₂_mul,
    eval₂_X_pow, eval₂_add, eval₂_C, palindromicRat_polynomial_comp_X_pow_eval₂,
    palindromicPBase, palindromicRat_int_map_eval₂]

theorem palindromicRat_DResidueSum_eval₂ {p : ℕ} [Fact p.Prime]
    (r0 : ℕ) (i : Fin p) :
    (palindromicDResidueSum p r0 i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicTransitionMatrix p l i) *
            ((rowD 1 r0).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
            ((rowD 1 (r0 + 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p) := by
  simp only [palindromicDResidueSum, eval₂_finsetSum, eval₂_mul,
    eval₂_X_pow, eval₂_add, eval₂_C, palindromicRat_polynomial_comp_X_pow_eval₂,
    palindromicDBase, palindromicRat_int_map_eval₂]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.PalindromicRowFrobenius
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial

theorem chebyshev_U_sign_natAbs_eval {K : Type*} [Field K]
    (φ : ℤ →+* K) (x : K) (m : ℤ) :
    φ (Int.sign m) * (Chebyshev.U ℤ ((m.natAbs : ℤ) - 1)).eval₂ φ x =
      (Chebyshev.U ℤ (m - 1)).eval₂ φ x := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [Int.ofNat_natAbs_of_nonpos hm.le, Int.sign_eq_neg_one_of_neg hm,
      map_neg, map_one, neg_one_mul, Chebyshev.U_neg_sub_one, eval₂_neg, neg_neg]
  · subst m
    simp
  · rw [Int.natAbs_of_nonneg hm.le, Int.sign_eq_one_of_pos hm, map_one, one_mul]

theorem rowP_eval₂_of_distance_lt {K : Type*} [Field K] (φ : ℤ →+* K)
    {N r : ℕ} (hd : rowDistance N r < Cdegree N) {x : K} (hx : x ≠ 0) :
    (rowP N r).eval₂ φ x =
      (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.T ℤ (rowDistance N r : ℤ)).eval₂ φ x⁻¹ := by
  have hT : (Chebyshev.T ℤ (rowDistance N r : ℤ)).natDegree < Cdegree N := by
    simpa [Chebyshev.natDegree_T] using hd
  unfold rowP
  rw [eval₂_mul, reversedRow_eval₂ φ hT hx]
  simp only [eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  exact (mul_assoc _ _ _).symm

theorem rowD_eval₂_of_distance_lt {K : Type*} [Field K] (φ : ℤ →+* K)
    {N r : ℕ} (hd : rowDistance N r < Cdegree N) {x : K} (hx : x ≠ 0) :
    (rowD N r).eval₂ φ x =
      φ (Int.sign (rowOffset N r)) * (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂ φ x⁻¹ := by
  have hU : (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).natDegree <
      Cdegree N := by
    rw [Chebyshev.natDegree_U]
    simp only [sub_add_cancel, Int.natAbs_natCast]
    omega
  unfold rowD
  rw [eval₂_mul, eval₂_mul, reversedRow_eval₂ φ hU hx]
  simp only [eval₂_C, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  ring

theorem palindromicRat_row_identity_of_distance_lt {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {N r : ℕ} (hN : 0 < N)
    (hd : rowDistance N r < Cdegree N) :
    palindromicRatT p * (rowP N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) -
      palindromicRatF p * (rowD N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (1 - palindromicRatT p) ^ (2 * N) * palindromicRatT p ^ (63 * N) *
        palindromicRatW p ^ ((r : ℤ) - 4 * (N : ℤ)) := by
  have heval := palindromicRat_chebyshev_signed hp2 (rowOffset N r)
  rw [← Chebyshev.T_natAbs ℤ (rowOffset N r),
    ← chebyshev_U_sign_natAbs_eval (Int.castRingHom (RatFunc (ZMod p)))
      ((palindromicRatT p)⁻¹) (rowOffset N r)] at heval
  have hpow : palindromicRatT p ^ (Cdegree N - 1) * palindromicRatT p =
      palindromicRatT p ^ Cdegree N := by
    rw [← pow_succ, show Cdegree N - 1 + 1 = Cdegree N by
      have hC := Cdegree_pos hN
      omega]
  rw [rowP_eval₂_of_distance_lt _ hd (palindromicRat_T_ne_zero hp2),
    rowD_eval₂_of_distance_lt _ hd (palindromicRat_T_ne_zero hp2)]
  calc
    _ = (1 - palindromicRatT p) ^ h N * palindromicRatT p ^ (Cdegree N - 1) *
        (palindromicRatT p *
          (Chebyshev.T ℤ (rowDistance N r : ℤ)).eval₂
            (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)⁻¹ -
        palindromicRatF p *
          ((Int.castRingHom (RatFunc (ZMod p))) (Int.sign (rowOffset N r)) *
            (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂
              (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)⁻¹)) := by ring
    _ = (1 - palindromicRatT p) ^ h N * palindromicRatT p ^ (Cdegree N - 1) *
        (palindromicRatT p * palindromicRatW p ^ rowOffset N r) := by
      exact congrArg (fun z : RatFunc (ZMod p) =>
        (1 - palindromicRatT p) ^ h N *
          palindromicRatT p ^ (Cdegree N - 1) * z) heval
    _ = (1 - palindromicRatT p) ^ h N *
        (palindromicRatT p ^ (Cdegree N - 1) * palindromicRatT p) *
          palindromicRatW p ^ rowOffset N r := by ring
    _ = _ := by
      rw [hpow]
      simp only [h, Cdegree, rowOffset, g, Nat.cast_mul, Nat.cast_ofNat]



end InternalCatalan





namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_base_distance_lt {j : ℕ} (hj : j ≤ 48) :
    rowDistance 1 j < Cdegree 1 := by
  unfold rowDistance rowOffset g Cdegree
  omega

theorem palindromic_block_row_lt {p r₀ : ℕ} [Fact p.Prime]
    (hr : r₀ < 48) (i : Fin p) : p * r₀ + i.val < n p := by
  have hm := Nat.mul_le_mul_left p (show r₀ + 1 ≤ 48 by omega)
  have hi := i.isLt
  simp only [Nat.mul_add, Nat.mul_one] at hm
  unfold n
  nlinarith

theorem palindromicRatRow_eq_actual_rows {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {N r : ℕ} (hN : 0 < N)
    (hd : rowDistance N r < Cdegree N) :
    palindromicRatRow p N r =
      palindromicRatT p * (rowP N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) -
        palindromicRatF p * (rowD N r).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) := by
  symm
  simpa only [palindromicRatRow, Nat.cast_mul, Nat.cast_ofNat] using
    palindromicRat_row_identity_of_distance_lt hp2 hN hd

theorem palindromicRat_rows_separated {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < 48) (i : Fin p) :
    (palindromicRatT p *
        (rowP p (p * r₀ + i.val)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) * palindromicRatE p =
      (palindromicPResidueSum p r₀ i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) ∧
    ((rowD p (p * r₀ + i.val)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (palindromicDResidueSum p r₀ i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) := by
  let ev : ℤ[X] → RatFunc (ZMod p) := fun P =>
    P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)
  let evp : (ZMod p)[X] → RatFunc (ZMod p) := fun P =>
    P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmain := palindromicRatRow_eq_actual_rows hp2 hp
    (rowDistance_lt_Cdegree hp (palindromic_block_row_lt hr i))
  have hbase := palindromicRatRow_eq_actual_rows hp2 (N := 1) (r := r₀)
    (by decide) (palindromic_base_distance_lt (by omega))
  have hnext := palindromicRatRow_eq_actual_rows hp2 (N := 1) (r := r₀ + 1)
    (by decide) (palindromic_base_distance_lt (by omega))
  have hraw := palindromicRatRow_expansion hp2 r₀ i
  rw [hmain, hbase, hnext] at hraw
  have hleft :
      (palindromicRatT p * ev (rowP p (p * r₀ + i.val)) -
        palindromicRatF p * ev (rowD p (p * r₀ + i.val))) * palindromicRatE p =
      palindromicRatT p * ev (rowP p (p * r₀ + i.val)) * palindromicRatE p -
        palindromicRatF p ^ p * ev (rowD p (p * r₀ + i.val)) := by
    rw [← palindromicRat_F_mul_E hp2]
    ring
  have hright :
      (∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) *
            (palindromicRatT p * ev (rowP 1 r₀) - palindromicRatF p * ev (rowD 1 r₀)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
              (palindromicRatT p * ev (rowP 1 (r₀ + 1)) -
                palindromicRatF p * ev (rowD 1 (r₀ + 1))) ^ p)) =
        evp (palindromicPResidueSum p r₀ i) -
          palindromicRatF p ^ p * evp (palindromicDResidueSum p r₀ i) := by
    dsimp only [evp]
    rw [palindromicRat_PResidueSum_eval₂, palindromicRat_DResidueSum_eval₂,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [sub_pow_char, mul_pow]
    dsimp only [ev]
    ring
  change (palindromicRatT p * ev (rowP p (p * r₀ + i.val)) -
      palindromicRatF p * ev (rowD p (p * r₀ + i.val))) * palindromicRatE p = _ at hraw
  rw [hleft, hright] at hraw
  have hstar := congrArg (palindromicRatStar p) hraw
  dsimp only [ev, evp] at hstar
  simp only [map_sub, map_mul, palindromicRatStar_T, palindromicRatStar_E,
    palindromicRatStar_eval₂_int, palindromicRatStar_F_pow hp2,
    palindromicRatStar_eval₂] at hstar
  have hP : palindromicRatT p * ev (rowP p (p * r₀ + i.val)) * palindromicRatE p =
      evp (palindromicPResidueSum p r₀ i) := by
    apply mul_left_cancel₀ (palindromicRat_two_ne_zero hp2)
    dsimp only [ev, evp] at *
    linear_combination hraw + hstar
  have hD : ev (rowD p (p * r₀ + i.val)) = evp (palindromicDResidueSum p r₀ i) := by
    apply mul_left_cancel₀ (pow_ne_zero p (palindromicRat_F_ne_zero (p := p)))
    linear_combination hP - hraw
  exact ⟨hP, hD⟩

theorem palindromic_rowP_frobenius {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < 48) (i : Fin p) :
    X * (rowP p (p * r₀ + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2) = palindromicPResidueSum p r₀ i := by
  apply palindromicRatT_eval₂RingHom_injective hp2
  change eval₂ _ _ _ = eval₂ _ _ _
  simp only [eval₂_mul, eval₂_X, eval₂_pow, eval₂_sub, eval₂_one,
    palindromicRat_int_map_eval₂]
  exact (palindromicRat_rows_separated hp2 hr i).1

theorem palindromic_rowD_frobenius {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < 48) (i : Fin p) :
    (rowD p (p * r₀ + i.val)).map (Int.castRingHom (ZMod p)) =
      palindromicDResidueSum p r₀ i := by
  apply palindromicRatT_eval₂RingHom_injective hp2
  change eval₂ _ _ _ = eval₂ _ _ _
  rw [palindromicRat_int_map_eval₂]
  exact (palindromicRat_rows_separated hp2 hr i).2

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.PalindromicExtractedEntries
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial

theorem palindromicZModIntCast_apply (p : ℕ) (z : ℤ) :
    (Int.castRingHom (ZMod p)) z = (z : ZMod p) := rfl

theorem palindromic_actual_P_extraction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (u : ℕ) :
    (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val) =
      palindromicTransitionMatrix p ell i * ((rowP 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowP 1 (r0 + 1)).coeff u : ZMod p) := by
  have h := palindromicPResidueSum_coeff p r0 u i ell
  rw [← palindromic_rowP_frobenius hp2 hr i] at h
  simpa only [palindromicPBase, coeff_map, palindromicZModIntCast_apply] using h

theorem palindromic_actual_D_extraction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (u : ℕ) :
    ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) =
      palindromicTransitionMatrix p ell i * ((rowD 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowD 1 (r0 + 1)).coeff u : ZMod p) := by
  have h := palindromicDResidueSum_coeff p r0 u i ell
  rw [← palindromic_rowD_frobenius hp2 hr i] at h
  simpa only [palindromicDBase, coeff_map, palindromicZModIntCast_apply] using h

theorem palindromic_actual_P_extraction_below {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) :
    (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ell.val = 0 := by
  rw [palindromic_rowP_frobenius hp2 hr i]
  exact palindromicPResidueSum_coeff_below p r0 i ell


end InternalCatalan





namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicBaseRawContraction (p : ℕ) [Fact p.Prime] (r k : ℕ) : ZMod p :=
  (∑ u ∈ Finset.range 65, ((rowP 1 r).coeff u : ZMod p) *
    palindromicRatResidue p (momentRat u k)) -
  (3 / 2 : ZMod p) *
    ∑ u ∈ Finset.range 65, ((rowD 1 r).coeff u : ZMod p) *
      palindromicRatResidue p (zetaRat u k)

def palindromicExtractedRawContraction (p : ℕ) [Fact p.Prime] (r0 : ℕ)
    (i ell : Fin p) (k : ℕ) :
    ZMod p :=
  (∑ u ∈ Finset.range 65,
    (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val) *
      palindromicRatResidue p (momentRat u k)) -
  (3 / 2 : ZMod p) *
    ∑ u ∈ Finset.range 65,
      ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) *
        palindromicRatResidue p (zetaRat u k)

theorem palindromicExtractedRawContraction_factor {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (k : ℕ) :
    palindromicExtractedRawContraction p r0 i ell k =
      palindromicTransitionMatrix p ell i * palindromicBaseRawContraction p r0 k +
        palindromicReversedTransitionMatrix p ell i *
          palindromicBaseRawContraction p (r0 + 1) k := by
  simp only [palindromicExtractedRawContraction, palindromicBaseRawContraction]
  simp_rw [palindromic_actual_P_extraction hp2 hr i ell,
    palindromic_actual_D_extraction hp2 hr i ell,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

def palindromicBaseFilterWeight (p v : ℕ) : ZMod p :=
  (-1 : ZMod p) ^ v * (Nat.choose 4 v : ZMod p)

def palindromicBaseFilteredContraction (p : ℕ) [Fact p.Prime] (r : ℕ)
    (k0 : Fin 48) : ZMod p :=
  ∑ v ∈ Finset.range 5, palindromicBaseFilterWeight p v *
    palindromicBaseRawContraction p r (7 + k0.val + v)

def palindromicExtractedFilteredEntry (p : ℕ) [Fact p.Prime] (r0 : Fin 48)
    (i ell : Fin p) (k0 : Fin 48) : ZMod p :=
  ∑ v ∈ Finset.range 5, palindromicBaseFilterWeight p v *
    palindromicExtractedRawContraction p r0.val i ell (7 + k0.val + v)

theorem palindromicExtractedFilteredEntry_factor {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (r0 : Fin 48) (i ell : Fin p) (k0 : Fin 48) :
    palindromicExtractedFilteredEntry p r0 i ell k0 =
      palindromicTransitionMatrix p ell i *
          palindromicBaseFilteredContraction p r0.val k0 +
        palindromicReversedTransitionMatrix p ell i *
          palindromicBaseFilteredContraction p (r0.val + 1) k0 := by
  unfold palindromicExtractedFilteredEntry palindromicBaseFilteredContraction
  simp_rw [palindromicExtractedRawContraction_factor hp2 r0.isLt i ell,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    ring
  · apply Finset.sum_congr rfl
    intro v hv
    ring

theorem palindromicBaseRawContraction_eq_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : ℕ) (hk : k < p) :
    palindromicBaseRawContraction p r k =
      palindromicRatResidue p (rawEntryRat 0 1 r k) := by
  simpa only [palindromicBaseRawContraction, H, mul_one] using
    (fixed_rawEntryRat_residue hp r k hk).symm

theorem palindromicBaseFilteredContraction_eq_fixedBase {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r : Fin 49) (k0 : Fin 48) :
    palindromicBaseFilteredContraction p r.val k0 =
      palindromicRatResidue p (fixedBaseEntryRat r k0) := by
  rw [fixedBaseEntryRat_residue hp r k0]
  simp only [palindromicBaseFilteredContraction, palindromicBaseFilterWeight,
    q, b, mul_one]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' : v < 5 := Finset.mem_range.mp hv
  have hk := k0.isLt
  rw [palindromicBaseRawContraction_eq_residue hp r.val (7 + k0.val + v) (by omega)]

theorem palindromicBaseFilteredContraction_eq_fixedB0 {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r0 k0 : Fin 48) :
    palindromicBaseFilteredContraction p r0.val k0 = fixedB0Residue p r0 k0 := by
  rw [fixedB0Residue_apply]
  exact palindromicBaseFilteredContraction_eq_fixedBase hp r0.castSucc k0

theorem palindromicBaseFilteredContraction_eq_fixedB1 {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r0 k0 : Fin 48) :
    palindromicBaseFilteredContraction p (r0.val + 1) k0 = fixedB1Residue p r0 k0 := by
  rw [fixedB1Residue_apply]
  exact palindromicBaseFilteredContraction_eq_fixedBase hp r0.succ k0

theorem palindromicExtractedFilteredEntry_eq_fixedB {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r0 : Fin 48) (i ell : Fin p) (k0 : Fin 48) :
    palindromicExtractedFilteredEntry p r0 i ell k0 =
      palindromicTransitionMatrix p ell i * fixedB0Residue p r0 k0 +
        palindromicReversedTransitionMatrix p ell i * fixedB1Residue p r0 k0 := by
  have hp2 : p ≠ 2 := by omega
  rw [palindromicExtractedFilteredEntry_factor hp2,
    palindromicBaseFilteredContraction_eq_fixedB0 hp,
    palindromicBaseFilteredContraction_eq_fixedB1 hp]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeCentralZetaContraction
namespace OAI

section

open scoped BigOperators

namespace InternalCatalan

theorem centralCoeffKernel_odd_prime_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (d : ℤ) :
    ((centralCoeffKernel d).den : ZMod p) ≠ 0 := by
  unfold centralCoeffKernel
  split_ifs with hd
  · exact (centralCoeff_reduced_residue hp2 (d.toNat / 2)).1
  · simp

theorem rawCatalanCoeffRat_odd_prime_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (N r j : ℕ) :
    ((rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 := by
  unfold rawCatalanCoeffRat
  apply (rational_residue_sum (p := p) (Finset.range (H N))
    (fun i => ((rowP N r).coeff i : ℚ) *
      (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) ?_).1
  intro i hi
  have hkernel := centralCoeffKernel_odd_prime_den_ne_zero hp2 ((i : ℤ) - (j : ℤ))
  have hfour := rational_residue_mul (a := (4 : ℚ)) (by norm_num) hkernel
  exact (rational_residue_mul (a := ((rowP N r).coeff i : ℚ)) (by simp) hfour.1).1

theorem rawCatalanTerm_prime_sq_reduction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0 := by
  have hpz := rational_residue_mul (a := ((p ^ 2 : ℕ) : ℚ)) (b := z) (by simp) hz
  have hfull := rational_residue_mul hpz.1
    (rawCatalanCoeffRat_odd_prime_den_ne_zero hp2 N r j)
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_pow] using hfull.1
  · have hzero :
        ((((p ^ 2 : ℕ) : ℚ) * z * rawCatalanCoeffRat N r j).num : ZMod p) /
          ((((p ^ 2 : ℕ) : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0 := by
      rw [hfull.2, hpz.2]
      simp
    simpa only [Nat.cast_pow] using hzero

end InternalCatalan

end


namespace InternalCatalan

theorem momentUpperStrip_term_zero {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : j + 1 < p ^ 2) (hnd : ¬p ∣ j + 1) :
    (((p : ℚ) ^ 2 *
      (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 *
        (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
        (((p : ℚ) ^ 2 *
          (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) = 0 := by
  have hz : (j + 1) - (u + 1) < p ^ 2 :=
    lt_of_le_of_lt (Nat.sub_le (j + 1) (u + 1)) hb
  have hs := momentScalarPred_prime_digit_reduction hp2 hz
  have hj : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hnd ((ZMod.natCast_eq_zero_iff (j + 1) p).mp hzero)
  have hf := nat_fraction_reduced_residue p (j + 1) hj
  have hm := rational_residue_mul hs.1 hf.1
  have heq : (p : ℚ) ^ 2 *
      (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred ((j + 1) - (u + 1))) *
        ((p : ℚ) / ((j + 1 : ℕ) : ℚ)) := by ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hm.1
  · rw [heq, hm.2, hf.2]
    simp

theorem momentUpperStrip_term_multiple {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : j + 1 < p ^ 2) (hd : p ∣ j + 1) :
    (((p : ℚ) ^ 2 *
      (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      ((momentScalarPred ((j / p + 1) - (u / p + 1)) /
        ((j / p + 1 : ℕ) : ℚ)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 *
          (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
          (((p : ℚ) ^ 2 *
            (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((momentScalarPred ((j / p + 1) - (u / p + 1)) /
                ((j / p + 1 : ℕ) : ℚ)).num : ZMod p) /
                ((momentScalarPred ((j / p + 1) - (u / p + 1)) /
                  ((j / p + 1 : ℕ) : ℚ)).den : ZMod p)) := by
  have hsucc : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hd
  have hjmul : j + 1 = p * (j / p + 1) := by
    rw [← hsucc]
    exact (Nat.mul_div_cancel' hd).symm
  by_cases hzero : j + 1 ≤ u + 1
  · have huquot : (u + 1) / p ≤ u / p + 1 := by
      rw [Nat.succ_div]
      split_ifs <;> omega
    have hqle : j / p + 1 ≤ u / p + 1 := by
      have hmono : (j + 1) / p ≤ (u + 1) / p := Nat.div_le_div_right hzero
      rw [hsucc] at hmono
      exact hmono.trans huquot
    simp [Nat.sub_eq_zero_of_le hzero, Nat.sub_eq_zero_of_le hqle]
  · have hactive : u < p * (j / p + 1) := by
      rw [← hjmul]
      omega
    have hquot : ((j + 1) - (u + 1)) / p = (j / p + 1) - (u / p + 1) := by
      rw [hjmul]
      exact Nat.mul_sub_div u p (j / p + 1) hactive
    have hrem : ((j + 1) - (u + 1)) % p = p - (u % p + 1) := by
      rw [hjmul]
      exact Nat.mul_sub_mod hactive
    have hindex : p - 1 - (((j + 1) - (u + 1)) % p) = u % p := by
      rw [hrem]
      have hr : u % p < p := Nat.mod_lt u hp.out.pos
      omega
    have hz : (j + 1) - (u + 1) < p ^ 2 :=
      lt_of_le_of_lt (Nat.sub_le (j + 1) (u + 1)) hb
    have hqsmall : j / p + 1 < p := by
      rw [← hsucc]
      exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hb)
    have hqnot : ¬p ∣ j / p + 1 :=
      Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (j / p)) hqsmall
    have hqden : ((j / p + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hden
      exact hqnot ((ZMod.natCast_eq_zero_iff (j / p + 1) p).mp hden)
    have hf := nat_fraction_reduced_residue 1 (j / p + 1) hqden
    simp only [Nat.cast_one] at hf
    have hs := momentScalarPred_prime_digit_reduction hp2 hz
    have hl := rational_residue_mul hs.1 hf.1
    have hr := rational_residue_mul hs.2.1 hf.1
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hqq : ((j / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hjcast : ((j + 1 : ℕ) : ℚ) =
        (p : ℚ) * ((j / p + 1 : ℕ) : ℚ) := by exact_mod_cast hjmul
    have hleft : (p : ℚ) ^ 2 *
        (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ)) =
        ((p : ℚ) * momentScalarPred ((j + 1) - (u + 1))) *
          (1 / ((j / p + 1 : ℕ) : ℚ)) := by
      rw [hjcast]
      field_simp [hpq, hqq]
    have hright : momentScalarPred ((j / p + 1) - (u / p + 1)) /
        ((j / p + 1 : ℕ) : ℚ) =
        momentScalarPred (((j + 1) - (u + 1)) / p) *
          (1 / ((j / p + 1 : ℕ) : ℚ)) := by
      rw [hquot]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hleft]
      exact hl.1
    · rw [hright]
      exact hr.1
    · rw [hleft, hl.2, hs.2.2, hindex, hright, hr.2]
      ring





open scoped BigOperators

def momentUpperPrefix (u j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range j,
    momentScalarPred ((k + 1) - (u + 1)) / ((k + 1 : ℕ) : ℚ)

@[simp] theorem momentUpperPrefix_zero (u : ℕ) : momentUpperPrefix u 0 = 0 := by
  simp [momentUpperPrefix]

theorem momentUpperPrefix_succ (u j : ℕ) :
    momentUpperPrefix u (j + 1) = momentUpperPrefix u j +
      momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ) := by
  unfold momentUpperPrefix
  rw [Finset.sum_range_succ]

theorem momentUpperPrefix_of_le {u j : ℕ} (hj : j ≤ u + 1) :
    momentUpperPrefix u j = 0 := by
  unfold momentUpperPrefix
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [Nat.sub_eq_zero_of_le (by omega : k + 1 ≤ u + 1), momentScalarPred_zero, zero_div]

theorem momentRat_upper_prefix (u i : ℕ) :
    momentRat i (u + i + 1) = boundaryPlus (u + 1) - momentUpperPrefix u (u + i + 1) := by
  induction i with
  | zero => simp [momentUpperPrefix_of_le (le_refl (u + 1))]
  | succ i ih =>
    have hrec := momentRat_step i (u + i + 1)
    rw [ih] at hrec
    have hpred : momentScalarPred ((u + i + 1 + 1) - (u + 1)) = momentScalar i := by
      rw [show (u + i + 1 + 1) - (u + 1) = i + 1 by omega]
      simp [momentScalarPred]
    rw [show u + (i + 1) + 1 = (u + i + 1) + 1 by omega,
      momentUpperPrefix_succ, hpred]
    linarith only [hrec]

theorem momentUpperPrefix_prime_digit_reduction {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentUpperPrefix u j).den : ZMod p) ≠ 0 ∧
      ((momentUpperPrefix (u / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentUpperPrefix u j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentUpperPrefix u j).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((momentUpperPrefix (u / p) (j / p)).num : ZMod p) /
                ((momentUpperPrefix (u / p) (j / p)).den : ZMod p)) := by
  revert hbound
  induction j with
  | zero => intro hbound; simp
  | succ j ih =>
    intro hbound
    have hprev := ih (by omega : j < p ^ 2)
    have hscale : (p : ℚ) ^ 2 * momentUpperPrefix u (j + 1) =
        (p : ℚ) ^ 2 * momentUpperPrefix u j +
          (p : ℚ) ^ 2 *
            (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ)) := by
      rw [momentUpperPrefix_succ, mul_add]
    by_cases hdiv : p ∣ j + 1
    · have ht := momentUpperStrip_term_multiple (u := u) hp2 hbound hdiv
      have hquot : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hdiv
      have hsmall : momentUpperPrefix (u / p) ((j + 1) / p) =
          momentUpperPrefix (u / p) (j / p) +
            momentScalarPred ((j / p + 1) - (u / p + 1)) /
              ((j / p + 1 : ℕ) : ℚ) := by
        rw [hquot, momentUpperPrefix_succ]
      have hl := rational_residue_add hprev.1 ht.1
      have hr := rational_residue_add hprev.2.1 ht.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hsmall]
        exact hr.1
      · rw [hscale, hl.2, hprev.2.2, ht.2.2, hsmall, hr.2]
        ring
    · have ht := momentUpperStrip_term_zero (u := u) hp2 hbound hdiv
      have hquot : (j + 1) / p = j / p := Nat.succ_div_of_not_dvd hdiv
      have hl := rational_residue_add hprev.1 ht.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, ht.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan



namespace InternalCatalan

def momentRatSigned (i : ℤ) (j : ℕ) : ℚ :=
  if 0 ≤ i then momentRat i.toNat j else
    if i = -1 then momentRatNegOne j else 0

@[simp] theorem momentRatSigned_natCast (i j : ℕ) :
    momentRatSigned (i : ℤ) j = momentRat i j := by
  simp [momentRatSigned]

@[simp] theorem momentRatSigned_neg_one (j : ℕ) :
    momentRatSigned (-1) j = momentRatNegOne j := by
  norm_num [momentRatSigned]

theorem momentRatSigned_upper_prefix {P q : ℕ} (hPq : P ≤ q) :
    momentRatSigned ((q : ℤ) - (P : ℤ) - 1) q =
      boundaryPlus (P + 1) - momentUpperPrefix P q := by
  by_cases heq : P = q
  · subst q
    simp only [sub_self, zero_sub, momentRatSigned_neg_one, momentRatNegOne_eq,
      momentUpperPrefix_of_le (Nat.le_succ P), sub_zero]
  · have hlt : P < q := by omega
    have hcast : ((q - P - 1 : ℕ) : ℤ) = (q : ℤ) - (P : ℤ) - 1 := by omega
    have hindex : P + (q - P - 1) + 1 = q := by omega
    rw [← hcast, momentRatSigned_natCast]
    simpa only [hindex] using momentRat_upper_prefix P (q - P - 1)

theorem momentRat_upper_prime_digit_reduction {p u i : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : u + i + 1 < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i (u + i + 1)).den : ZMod p) ≠ 0 ∧
      ((momentRatSigned ((((u + i + 1) / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) - 1)
        ((u + i + 1) / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i (u + i + 1)).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i (u + i + 1)).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((momentRatSigned ((((u + i + 1) / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) - 1)
                ((u + i + 1) / p)).num : ZMod p) /
                  ((momentRatSigned ((((u + i + 1) / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) - 1)
                    ((u + i + 1) / p)).den : ZMod p)) := by
  have hstart := boundaryPlus_prime_digit_reduction hp2 (show u < p ^ 2 by omega)
  have hstrip := momentUpperPrefix_prime_digit_reduction (u := u) hp2 hbound
  have hl := rational_residue_sub hstart.1 hstrip.1
  have hr := rational_residue_sub hstart.2.1 hstrip.2.1
  have hleft : (p : ℚ) ^ 2 * momentRat i (u + i + 1) =
      (p : ℚ) ^ 2 * boundaryPlus (u + 1) -
        (p : ℚ) ^ 2 * momentUpperPrefix u (u + i + 1) := by
    rw [momentRat_upper_prefix, mul_sub]
  have hright := momentRatSigned_upper_prefix
    (Nat.div_le_div_right (by omega : u ≤ u + i + 1) : u / p ≤ (u + i + 1) / p)
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl.1
  · rw [hright]
    exact hr.1
  · rw [hleft, hl.2, hstart.2.2, hstrip.2.2, hright, hr.2]
    ring

theorem momentRat_prime_digit_reduction_of_lt {p i j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hij : i < j) (hj : j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      ((momentRatSigned (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) =
            (oddPrimeWeight p).coeff ((j - i - 1) % p) *
              (((momentRatSigned (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1)
                (j / p)).num : ZMod p) /
                  ((momentRatSigned (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1)
                    (j / p)).den : ZMod p)) := by
  have hindex : j - i - 1 + i + 1 = j := by omega
  simpa only [hindex] using momentRat_upper_prime_digit_reduction hp2
    (show j - i - 1 + i + 1 < p ^ 2 by omega)





theorem momentRat_prime_digit_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hi : i < p ^ 2) (hj : j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) =
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p)) := by
  by_cases hji : j ≤ i
  · have hd := oddPrimeDigitRemainder_of_le hp.out.pos hji
    have hrow : oddPrimeDigitRow p i j = (((i - j) / p + j / p : ℕ) : ℤ) := by
      rw [oddPrimeDigitRow_of_le hp.out.pos hji, Nat.cast_add]
    simpa only [hd, hrow, momentRatSigned_natCast] using
      momentRat_prime_digit_reduction_of_le hp2 hji hi
  · have hij : i < j := by omega
    simpa only [oddPrimeDigitRemainder_of_lt hp.out.pos hij,
      oddPrimeDigitRow_of_lt hp.out.pos hij] using
        momentRat_prime_digit_reduction_of_lt hp2 hij hj





open scoped BigOperators

theorem rawEntryRat_zero_prime_digit_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hH : H N < p ^ 2) (hj : j < H N) :
    (((p : ℚ) ^ 2 * rawEntryRat 0 N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * rawEntryRat 0 N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * rawEntryRat 0 N r j).den : ZMod p) =
          (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ZMod p) *
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p))) -
            (3 / 2 : ZMod p) *
              ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ZMod p) *
                (if i % p = j % p then
                  ((zetaRat (i / p) (j / p)).num : ZMod p) /
                    ((zetaRat (i / p) (j / p)).den : ZMod p) else 0) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let fM : ℕ → ℚ := fun i => ((rowP N r).coeff i : ℚ) * ((p : ℚ) ^ 2 * momentRat i j)
  let fZ : ℕ → ℚ := fun i => ((rowD N r).coeff i : ℚ) * ((p : ℚ) ^ 2 * zetaRat i j)
  let A : ℚ := ∑ i ∈ Finset.range (H N), fM i
  let B : ℚ := ∑ i ∈ Finset.range (H N), fZ i
  have hj2 : j < p ^ 2 := hj.trans hH
  have hM (i : ℕ) (hi : i ∈ Finset.range (H N)) :
      ((fM i).den : ZMod p) ≠ 0 ∧
        R (fM i) = ((rowP N r).coeff i : ZMod p) *
          (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
            R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := by
    have hd := momentRat_prime_digit_reduction hp2
      ((Finset.mem_range.mp hi).trans hH) hj2
    have hm := rational_residue_mul (a := ((rowP N r).coeff i : ℚ)) (by simp) hd.1
    refine ⟨hm.1, ?_⟩
    have hmr : R (fM i) = ((rowP N r).coeff i : ZMod p) *
        R ((p : ℚ) ^ 2 * momentRat i j) := by
      simpa [R, fM] using hm.2
    have hdr : R ((p : ℚ) ^ 2 * momentRat i j) =
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
          R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := hd.2.2
    rw [hmr, hdr]
    ring
  have hZ (i : ℕ) (hi : i ∈ Finset.range (H N)) :
      ((fZ i).den : ZMod p) ≠ 0 ∧
        R (fZ i) = ((rowD N r).coeff i : ZMod p) *
          (if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0) := by
    have hd := zetaRat_prime_digit_reduction
      ((Finset.mem_range.mp hi).trans hH) hj2
    have hm := rational_residue_mul (a := ((rowD N r).coeff i : ℚ)) (by simp) hd.1
    refine ⟨hm.1, ?_⟩
    have hmr : R (fZ i) = ((rowD N r).coeff i : ZMod p) *
        R ((p : ℚ) ^ 2 * zetaRat i j) := by
      simpa [R, fZ] using hm.2
    have hdr : R ((p : ℚ) ^ 2 * zetaRat i j) =
        if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0 := hd.2
    rw [hmr, hdr]
  have hA := rational_residue_sum (Finset.range (H N)) fM (fun i hi => (hM i hi).1)
  have hB := rational_residue_sum (Finset.range (H N)) fZ (fun i hi => (hZ i hi).1)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hlt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hAeq : A = (p : ℚ) ^ 2 *
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) * momentRat i j) := by
    dsimp only [A, fM]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B = (p : ℚ) ^ 2 *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j) := by
    dsimp only [B, fZ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit : (p : ℚ) ^ 2 * rawEntryRat 0 N r j = A - (3 / 2 : ℚ) * B := by
    rw [rawEntryRat_zero, hAeq, hBeq]
    ring
  have hAres : R A =
      ∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
          R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := by
    calc
      R A = ∑ i ∈ Finset.range (H N), R (fM i) := hA.2
      _ = _ := Finset.sum_congr rfl (fun i hi => (hM i hi).2)
  have hBres : R B =
      ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ZMod p) *
        (if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0) := by
    calc
      R B = ∑ i ∈ Finset.range (H N), R (fZ i) := hB.2
      _ = _ := Finset.sum_congr rfl (fun i hi => (hZ i hi).2)
  have h32R : R (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hBprodR : R ((3 / 2 : ℚ) * B) = R (3 / 2 : ℚ) * R B := hBprod.2
  have hdiffR : R (A - (3 / 2 : ℚ) * B) = R A - R ((3 / 2 : ℚ) * B) := hdiff.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hdiff.1
  · change R ((p : ℚ) ^ 2 * rawEntryRat 0 N r j) = _
    rw [hsplit, hdiffR, hBprodR, h32R, hAres, hBres]

theorem rawEntryRat_prime_digit_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hH : H N < p ^ 2) (hj : j < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * rawEntryRat z N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * rawEntryRat z N r j).den : ZMod p) =
          (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ZMod p) *
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p))) -
            (3 / 2 : ZMod p) *
              ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ZMod p) *
                (if i % p = j % p then
                  ((zetaRat (i / p) (j / p)).num : ZMod p) /
                    ((zetaRat (i / p) (j / p)).den : ZMod p) else 0) := by
  have hzero := rawEntryRat_zero_prime_digit_reduction (p := p) (N := N) (r := r) hp2 hH hj
  have hcat := rawCatalanTerm_prime_sq_reduction hp2 z hz N r j
  have hadd := rational_residue_add hzero.1 hcat.1
  have heq : (p : ℚ) ^ 2 * rawEntryRat z N r j =
      (p : ℚ) ^ 2 * rawEntryRat 0 N r j +
        (p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j := by
    rw [rawEntryRat_affine]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hadd.1
  · rw [heq, hadd.2, hcat.2, add_zero]
    exact hzero.2

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem filterCoeffRat_prime_den_ne_zero {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat N v).den : ZMod p) ≠ 0 := by
  have heq : filterCoeffRat N v =
      (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) := by
    simp [filterCoeffRat]
  rw [heq, Rat.den_intCast, Nat.cast_one]
  exact one_ne_zero

theorem filteredEntryRat_prime_scaled_residue_sum {p r k : ℕ} [hp : Fact p.Prime]
    (hp260 : 260 < p) (hk : k < n p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * filteredEntryRat z p r k).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * filteredEntryRat z p r k).num : ZMod p) /
        (((p : ℚ) ^ 2 * filteredEntryRat z p r k).den : ZMod p) =
          ∑ v ∈ Finset.range (q p + 1),
            (((filterCoeffRat p v).num : ZMod p) / ((filterCoeffRat p v).den : ZMod p)) *
              ((((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v)).num : ZMod p) /
                (((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun x => (x.num : ZMod p) / (x.den : ZMod p)
  let f : ℕ → ℚ := fun v =>
    filterCoeffRat p v * ((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v))
  have hp2 : p ≠ 2 := by omega
  have hH : H p < p ^ 2 := by
    unfold H
    nlinarith
  have hterm (v : ℕ) (hv : v ∈ Finset.range (q p + 1)) :
      ((f v).den : ZMod p) ≠ 0 ∧
        R (f v) = R (filterCoeffRat p v) *
          R ((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v)) := by
    have hv' : v ≤ q p := by have := Finset.mem_range.mp hv; omega
    have hj : b p + k + v < H p := by
      have hjL := rawColumn_lt_L hk hv'
      unfold L H at *
      omega
    have hraw := (rawEntryRat_prime_digit_reduction (p := p) (N := p) (r := r)
      hp2 hH hj z hz).1
    exact rational_residue_mul (p := p) (filterCoeffRat_prime_den_ne_zero (p := p) p v) hraw
  have hsum := rational_residue_sum (p := p) (Finset.range (q p + 1)) f
    (fun v hv => (hterm v hv).1)
  have hscale : (p : ℚ) ^ 2 * filteredEntryRat z p r k =
      ∑ v ∈ Finset.range (q p + 1), f v := by
    rw [filteredEntryRat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [f]
    ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hsum.1
  · change R ((p : ℚ) ^ 2 * filteredEntryRat z p r k) = _
    rw [hscale]
    calc
      _ = ∑ v ∈ Finset.range (q p + 1), R (f v) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun v hv => (hterm v hv).2)

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators




end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_P_digit_contraction {p r0 : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hr : r0 < 48) (i ell : Fin p) (k : ℕ) :
    (∑ t ∈ Finset.range (65 * p), ((rowP p (p * r0 + i.val)).coeff t : ZMod p) *
      (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
      palindromicRatResidue p
        (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) =
    ∑ u ∈ Finset.range 65,
      (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        oddPrimeWeight p).coeff ((u + 1) * p + ell.val) *
          palindromicRatResidue p (momentRat u k) := by
  let P : (ZMod p)[X] := (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p))
  let Q : (ZMod p)[X] := X * P * oddPrimeWeight p
  have hP : ∀ t, 65 * p ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, palindromicZModIntCast_apply,
      rowP_coeff_eq_zero_of_ge hp.out.pos (show H p ≤ t from ht), Int.cast_zero]
  have h := oddPrime_P_coefficient_contraction (B := 65) (k := k)
    hp.out.pos ell.isLt P hP (fun v => palindromicRatResidue p (momentRatSigned v k))
  have hzero : Q.coeff ell.val = 0 :=
    palindromic_actual_P_extraction_below hp2 hr i ell
  have hshift :
      (∑ v ∈ Finset.range (65 + 1), Q.coeff (v * p + ell.val) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k)) =
      ∑ u ∈ Finset.range 65, Q.coeff ((u + 1) * p + ell.val) *
        palindromicRatResidue p (momentRat u k) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      momentRatSigned_natCast, zero_mul, zero_add, hzero, add_zero]
  have hh :
      (∑ t ∈ Finset.range (65 * p), ((rowP p (p * r0 + i.val)).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
        palindromicRatResidue p
          (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) =
      ∑ v ∈ Finset.range (65 + 1), Q.coeff (v * p + ell.val) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k) := by
    simpa only [P, Q, coeff_map, palindromicZModIntCast_apply] using h
  exact hh.trans hshift

theorem palindromic_D_digit_contraction {p r0 : ℕ} [hp : Fact p.Prime]
    (i ell : Fin p) (k : ℕ) :
    (∑ t ∈ Finset.range (65 * p), ((rowD p (p * r0 + i.val)).coeff t : ZMod p) *
      (if t % p = ell.val then palindromicRatResidue p (zetaRat (t / p) k) else 0)) =
    ∑ u ∈ Finset.range 65,
      ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) *
        palindromicRatResidue p (zetaRat u k) := by
  simpa only [mul_ite, mul_zero] using
    (oddPrime_block_residue_sum_gather (B := 65) hp.out.pos ell.isLt
      (fun t => ((rowD p (p * r0 + i.val)).coeff t : ZMod p))
      (fun u => palindromicRatResidue p (zetaRat u k)))

theorem palindromic_rawEntryRat_prime_digit_reduction {p r0 k : ℕ}
    [hp : Fact p.Prime] (hp260 : 260 < p) (hr : r0 < 48)
    (i ell : Fin p) (hk : k < 65) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z p (p * r0 + i.val) (k * p + ell.val)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * rawEntryRat z p (p * r0 + i.val) (k * p + ell.val)) =
      palindromicExtractedRawContraction p r0 i ell k := by
  have hp2 : p ≠ 2 := by omega
  have hH : H p < p ^ 2 := by unfold H; nlinarith
  have hbound : (k + 1) * p ≤ 65 * p := Nat.mul_le_mul_right p hk
  have hj : k * p + ell.val < H p := by
    unfold H
    have hell := ell.isLt
    nlinarith
  have hquot : (k * p + ell.val) / p = k := by
    rw [Nat.mul_comm k p, Nat.mul_add_div hp.out.pos,
      Nat.div_eq_of_lt ell.isLt, add_zero]
  have hmod : (k * p + ell.val) % p = ell.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt ell.isLt]
  have hraw := rawEntryRat_prime_digit_reduction (p := p) (r := p * r0 + i.val)
    hp2 hH hj z hz
  refine ⟨hraw.1, ?_⟩
  have hres :
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * rawEntryRat z p (p * r0 + i.val) (k * p + ell.val)) =
      (∑ t ∈ Finset.range (65 * p), ((rowP p (p * r0 + i.val)).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
        palindromicRatResidue p
          (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) -
      (3 / 2 : ZMod p) *
        ∑ t ∈ Finset.range (65 * p), ((rowD p (p * r0 + i.val)).coeff t : ZMod p) *
          (if t % p = ell.val then palindromicRatResidue p (zetaRat (t / p) k) else 0) := by
    simpa only [H, palindromicRatResidue, hquot, hmod] using hraw.2
  rw [hres, palindromic_P_digit_contraction hp2 hr i ell k,
    palindromic_D_digit_contraction i ell k]
  rfl

end InternalCatalan

end



namespace InternalCatalan

open Polynomial
open scoped BigOperators


end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.PalindromicExtractedMatrix
namespace OAI

section

noncomputable section

namespace InternalCatalan

def palindromicExtractedResidueMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicExtractedFilteredEntry p r.2 r.1 k.1 k.2

theorem palindromicExtractedResidueMatrix_eq_blocks {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) :
    palindromicExtractedResidueMatrix p = palindromicResidueBlockMatrix p := by
  ext r k
  exact palindromicExtractedFilteredEntry_eq_fixedB hp r.2 r.1 k.1 k.2


theorem det_palindromicExtractedResidueMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp : 260 < p)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicExtractedResidueMatrix p).det ≠ 0 := by
  rw [palindromicExtractedResidueMatrix_eq_blocks hp]
  exact det_palindromicResidueBlockMatrix_ne_zero_of_fixed (by omega) h0 hplus hminus

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedDeterminantGoodPrimes
namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem palindromicRatResidue_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    ((∏ i ∈ s, f i).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (∏ i ∈ s, f i) =
        ∏ i ∈ s, palindromicRatResidue p (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp [palindromicRatResidue]
  | @insert a s ha ih =>
    intro hf
    have hfa := hf a (Finset.mem_insert_self a s)
    have hs := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    simp only [Finset.prod_insert ha]
    refine ⟨(rational_residue_mul hfa hs.1).1, ?_⟩
    rw [palindromicRatResidue_mul hfa hs.1, hs.2]

theorem palindromicRatResidue_det {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hentry : ∀ i j, ((A i j).den : ZMod p) ≠ 0) :
    (A.det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p A.det =
        Matrix.det (fun i j => palindromicRatResidue p (A i j)) := by
  have hprod (σ : Equiv.Perm ι) :=
    palindromicRatResidue_prod (p := p) Finset.univ
      (fun i => A (σ i) i) (fun i _ => hentry (σ i) i)
  have hsum := palindromicRatResidue_int_sum (p := p) Finset.univ
    (fun σ : Equiv.Perm ι => (Equiv.Perm.sign σ : ℤ))
    (fun σ => ∏ i, A (σ i) i) (fun σ _ => (hprod σ).1)
  constructor
  · rw [Matrix.det_apply']
    exact hsum.1
  · calc
      palindromicRatResidue p A.det = palindromicRatResidue p
          (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, A (σ i) i) :=
        congrArg (palindromicRatResidue p) (Matrix.det_apply' A)
      _ =
          ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
            palindromicRatResidue p (∏ i, A (σ i) i) := hsum.2
      _ = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
          ∏ i, palindromicRatResidue p (A (σ i) i) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [(hprod σ).2]
      _ = Matrix.det (fun i j => palindromicRatResidue p (A i j)) :=
        (Matrix.det_apply' (fun i j => palindromicRatResidue p (A i j))).symm

theorem fixedB0_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    (fixedB0.det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p fixedB0.det = (fixedB0Residue p).det := by
  exact palindromicRatResidue_det fixedB0 (fixedB0_den_ne_zero hp)


theorem fixedMatrix_one_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    ((fixedMatrix 1).det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix 1).det =
        (fixedB0Residue p + fixedB1Residue p).det := by
  have hentry (r k : Fin 48) : ((fixedMatrix 1 r k).den : ZMod p) ≠ 0 := by
    rw [fixedMatrix_one]
    exact (rational_residue_add (fixedB0_den_ne_zero hp r k)
      (fixedB1_den_ne_zero hp r k)).1
  have hdet := palindromicRatResidue_det (fixedMatrix 1) hentry
  have hmatrix : (fun r k => palindromicRatResidue p (fixedMatrix 1 r k) :
      Matrix (Fin 48) (Fin 48) (ZMod p)) = fixedB0Residue p + fixedB1Residue p := by
    ext r k
    exact fixedMatrix_one_residue hp r k
  exact ⟨hdet.1, hdet.2.trans (congrArg Matrix.det hmatrix)⟩

theorem fixedMatrix_neg_one_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    ((fixedMatrix (-1)).det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix (-1)).det =
        (fixedB0Residue p - fixedB1Residue p).det := by
  have hentry (r k : Fin 48) : ((fixedMatrix (-1) r k).den : ZMod p) ≠ 0 := by
    rw [fixedMatrix_neg_one]
    exact (rational_residue_sub (fixedB0_den_ne_zero hp r k)
      (fixedB1_den_ne_zero hp r k)).1
  have hdet := palindromicRatResidue_det (fixedMatrix (-1)) hentry
  have hmatrix : (fun r k => palindromicRatResidue p (fixedMatrix (-1) r k) :
      Matrix (Fin 48) (Fin 48) (ZMod p)) = fixedB0Residue p - fixedB1Residue p := by
    ext r k
    exact fixedMatrix_neg_one_residue hp r k
  exact ⟨hdet.1, hdet.2.trans (congrArg Matrix.det hmatrix)⟩

theorem rational_det_ne_zero_of_residue_det_ne_zero {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hentry : ∀ i j, ((A i j).den : ZMod p) ≠ 0)
    (hcertificate :
      Matrix.det (fun i j => palindromicRatResidue p (A i j)) ≠ 0) :
    A.det ≠ 0 := by
  intro hzero
  apply hcertificate
  rw [← (palindromicRatResidue_det A hentry).2, hzero]
  simp [palindromicRatResidue]

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem palindromicRatResidue_ne_zero_of_bounds {p : ℕ} [Fact p.Prime]
    (x : ℚ) (hx : x ≠ 0) (hn : x.num.natAbs < p) (hd : x.den < p) :
    palindromicRatResidue p x ≠ 0 := by
  unfold palindromicRatResidue
  apply div_ne_zero
  · intro hz
    have hdiv : p ∣ x.num.natAbs :=
      Int.natCast_dvd.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp hz)
    exact (Nat.not_dvd_of_pos_of_lt
      (Nat.pos_of_ne_zero
        (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx))) hn) hdiv
  · intro hz
    exact (Nat.not_dvd_of_pos_of_lt x.den_pos hd)
      ((ZMod.natCast_eq_zero_iff x.den p).mp hz)


theorem fixedDeterminantPrimeCutoff_ge_260 : 260 ≤ fixedDeterminantPrimeCutoff := by
  unfold fixedDeterminantPrimeCutoff
  omega

theorem fixedDeterminants_residue_ne_zero_of_lt {p : ℕ} [Fact p.Prime]
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (hp : fixedDeterminantPrimeCutoff < p) :
    palindromicRatResidue p (fixedMatrix 0).det ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix 1).det ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix (-1)).det ≠ 0 := by
  unfold fixedDeterminantPrimeCutoff at hp
  exact ⟨palindromicRatResidue_ne_zero_of_bounds _ hzero (by omega) (by omega),
    palindromicRatResidue_ne_zero_of_bounds _ hplus (by omega) (by omega),
    palindromicRatResidue_ne_zero_of_bounds _ hminus (by omega) (by omega)⟩

theorem fixedDeterminants_mod_prime_ne_zero_of_lt {p : ℕ} [Fact p.Prime]
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (hp : fixedDeterminantPrimeCutoff < p) :
    (fixedB0Residue p).det ≠ 0 ∧
      (fixedB0Residue p + fixedB1Residue p).det ≠ 0 ∧
      (fixedB0Residue p - fixedB1Residue p).det ≠ 0 := by
  have hp260 : 260 < p := lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hp
  have h := fixedDeterminants_residue_ne_zero_of_lt hzero hplus hminus hp
  constructor
  · rw [← (fixedB0_det_residue hp260).2]
    simpa only [fixedMatrix_zero] using h.1
  constructor
  · rw [← (fixedMatrix_one_det_residue hp260).2]
    exact h.2.1
  · rw [← (fixedMatrix_neg_one_det_residue hp260).2]
    exact h.2.2



end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.PalindromicResidueDeterminant
namespace OAI

section

noncomputable section

namespace InternalCatalan

def palindromicResidueIndexEquiv (p : ℕ) : Fin p × Fin 48 ≃ Fin (n p) :=
  (Equiv.prodComm (Fin p) (Fin 48)).trans finProdFinEquiv


def palindromicScaledRatMatrix (z : ℚ) (p : ℕ) :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) ℚ :=
  fun r k => (p : ℚ) ^ 2 * filteredEntryRat z p
    (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)

theorem palindromicScaledRatMatrix_eq_submatrix (z : ℚ) (p : ℕ) :
    palindromicScaledRatMatrix z p =
      (((p : ℚ) ^ 2) •
        Matrix.of (fun r k : Fin (n p) => filteredEntryRat z p r.val k.val)).submatrix
          (palindromicResidueIndexEquiv p) (palindromicResidueIndexEquiv p) := by
  ext r k
  change (p : ℚ) ^ 2 * filteredEntryRat z p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val) =
    (p : ℚ) ^ 2 * filteredEntryRat z p
      (r.1.val + p * r.2.val) (k.1.val + p * k.2.val)
  rw [Nat.add_comm (p * r.2.val) r.1.val]

theorem det_palindromicScaledRatMatrix (z : ℚ) (p : ℕ) :
    (palindromicScaledRatMatrix z p).det =
      (p : ℚ) ^ (2 * n p) * determinantRat z p := by
  rw [palindromicScaledRatMatrix_eq_submatrix,
    Matrix.det_submatrix_equiv_self, Matrix.det_smul]
  simp only [Fintype.card_fin, ← pow_mul, determinantRat]
  rfl

theorem det_palindromicScaledRatMatrix_ne_zero_iff (z : ℚ) {p : ℕ}
    (hp : p ≠ 0) :
    (palindromicScaledRatMatrix z p).det ≠ 0 ↔ determinantRat z p ≠ 0 := by
  rw [det_palindromicScaledRatMatrix]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  exact mul_ne_zero_iff.trans (and_iff_right (pow_ne_zero (2 * n p) hpq))

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan



theorem determinantRat_ne_zero_of_scaledResidueMatrix (z : ℚ) {p : ℕ}
    [Fact p.Prime]
    (hentry : ∀ r k : Fin p × Fin 48,
      ((palindromicScaledRatMatrix z p r k).den : ZMod p) ≠ 0)
    (hcertificate : (palindromicScaledResidueMatrix z p).det ≠ 0) :
    determinantRat z p ≠ 0 := by
  apply (det_palindromicScaledRatMatrix_ne_zero_iff z
    (Nat.Prime.ne_zero (Fact.out : p.Prime))).mp
  exact rational_det_ne_zero_of_residue_det_ne_zero
    (palindromicScaledRatMatrix z p) hentry hcertificate

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RowMomentExpansion
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

@[simp] theorem realPoly_coeff (F : ℤ[X]) (i : ℕ) :
    (realPoly F).coeff i = (F.coeff i : ℝ) := by
  rw [realPoly, Polynomial.coeff_map]
  rfl






end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.PrimeNonvanishing
namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem oddPrime_multiple_sum_gather {R : Type*} [Semiring R] {p B : ℕ}
    (hp : 0 < p) (f : ℕ → R) :
    (∑ v ∈ Finset.range (B * p + 1), if v % p = 0 then f v else 0) =
      ∑ u ∈ Finset.range (B + 1), f (u * p) := by
  classical
  refine Finset.sum_bij_ne_zero (fun v _ _ => v / p) ?_ ?_ ?_ ?_
  · intro v hv hfv
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    have hv' := Finset.mem_range.mp hv
    nlinarith
  · intro v hv hfv w hw hfw hquot
    have hvr : v % p = 0 := by
      by_contra h
      exact hfv (if_neg h)
    have hwr : w % p = 0 := by
      by_contra h
      exact hfw (if_neg h)
    have hdv := Nat.mod_add_div v p
    have hdw := Nat.mod_add_div w p
    rw [hvr, hquot, zero_add] at hdv
    rw [hwr, zero_add] at hdw
    omega
  · intro u hu hfu
    have hu' : u ≤ B := by have := Finset.mem_range.mp hu; omega
    have hbound := Nat.mul_le_mul_right p hu'
    refine ⟨u * p, Finset.mem_range.mpr (by omega), ?_, Nat.mul_div_cancel u hp⟩
    simpa only [Nat.mul_mod_left, if_pos rfl, ite_true] using hfu
  · intro v hv hfv
    have hvr : v % p = 0 := by
      by_contra h
      exact hfv (if_neg h)
    have heq : v / p * p = v := by
      have h := Nat.mod_add_div v p
      rw [hvr, zero_add] at h
      simpa only [Nat.mul_comm] using h
    rw [if_pos hvr, heq]

theorem palindromic_filteredEntryRat_prime_digit_reduction {p : ℕ}
    [hp : Fact p.Prime] (hp260 : 260 < p) (r0 : Fin 48) (i ell : Fin p)
    (k0 : Fin 48) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * filteredEntryRat z p (p * r0.val + i.val)
      (ell.val + p * k0.val)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat z p
        (p * r0.val + i.val) (ell.val + p * k0.val)) =
      palindromicExtractedFilteredEntry p r0 i ell k0 := by
  have hcol : ell.val + p * k0.val < n p := by
    unfold n
    have hb := Nat.mul_le_mul_left p k0.isLt
    have hell := ell.isLt
    nlinarith
  have hs := filteredEntryRat_prime_scaled_residue_sum (r := p * r0.val + i.val)
    hp260 hcol z hz
  refine ⟨hs.1, ?_⟩
  let f : ℕ → ZMod p := fun v =>
    palindromicBaseFilterWeight p (v / p) *
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z p
        (p * r0.val + i.val) (b p + (ell.val + p * k0.val) + v))
  have hsum :
      palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat z p
        (p * r0.val + i.val) (ell.val + p * k0.val)) =
      ∑ v ∈ Finset.range (4 * p + 1), if v % p = 0 then f v else 0 := by
    calc
      _ = ∑ v ∈ Finset.range (q p + 1), palindromicRatResidue p (filterCoeffRat p v) *
          palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z p
            (p * r0.val + i.val) (b p + (ell.val + p * k0.val) + v)) := hs.2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have hd := (filterCoeffRat_prime_digit_reduction (p := p) (v := v)).2
        change palindromicRatResidue p (filterCoeffRat p v) = _ at hd
        rw [hd]
        split_ifs <;> simp only [f, palindromicBaseFilterWeight, zero_mul]
  rw [hsum, oddPrime_multiple_sum_gather hp.out.pos]
  unfold palindromicExtractedFilteredEntry
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u < 5 := Finset.mem_range.mp hu
  have hk : 7 + k0.val + u < 65 := by have := k0.isLt; omega
  have hindex : b p + (ell.val + p * k0.val) + u * p =
      (7 + k0.val + u) * p + ell.val := by unfold b; ring
  dsimp only [f]
  rw [Nat.mul_div_cancel u hp.out.pos, hindex,
    (palindromic_rawEntryRat_prime_digit_reduction hp260 r0.isLt i ell hk z hz).2]

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem palindromicScaledRatMatrix_entry_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (r k : Fin p × Fin 48) :
    ((palindromicScaledRatMatrix z p r k).den : ZMod p) ≠ 0 :=
  (palindromic_filteredEntryRat_prime_digit_reduction hp r.2 r.1 k.1 k.2 z hz).1

theorem palindromicScaledResidueMatrix_eq_extracted {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    palindromicScaledResidueMatrix z p = palindromicExtractedResidueMatrix p := by
  ext r k
  exact (palindromic_filteredEntryRat_prime_digit_reduction hp r.2 r.1 k.1 k.2 z hz).2



theorem determinantRat_prime_ne_zero_of_fixed
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (z : ℚ) {p : ℕ} [Fact p.Prime] (hp : palindromicPrimeCutoff z < p) :
    determinantRat z p ≠ 0 := by
  have hfixed : fixedDeterminantPrimeCutoff < p :=
    lt_of_le_of_lt (le_max_left _ _) hp
  have hp260 : 260 < p :=
    lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hfixed
  have hzbound : z.den < p := lt_of_le_of_lt (le_max_right _ _) hp
  have hz : (z.den : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt z.den_pos hzbound)
      ((ZMod.natCast_eq_zero_iff z.den p).mp hzero)
  have hdet := fixedDeterminants_mod_prime_ne_zero_of_lt hzero hplus hminus hfixed
  apply determinantRat_ne_zero_of_scaledResidueMatrix z
    (palindromicScaledRatMatrix_entry_den_ne_zero hp260 z hz)
  rw [palindromicScaledResidueMatrix_eq_extracted hp260 z hz]
  exact det_palindromicExtractedResidueMatrix_ne_zero_of_fixed
    hp260 hdet.1 hdet.2.1 hdet.2.2



end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan




end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan











end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Split.PrimeNonvanishing
namespace OAI

namespace InternalCatalan

theorem determinantRat_prime_ne_zero_of_large_prime (z : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : palindromicPrimeCutoff z < p) : determinantRat z p ≠ 0 :=
  determinantRat_prime_ne_zero_of_fixed fixedMatrix_det_ne_zero_sigma_zero
    fixedMatrix_det_ne_zero_sigma_one fixedMatrix_det_ne_zero_sigma_neg_one z hp

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (z : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : palindromicPrimeCutoff z < p) : determinantRat z p ≠ 0 := by
  first
  | exact @OAI.InternalCatalan.determinantRat_prime_ne_zero_of_large_prime
  | (apply OAI.InternalCatalan.determinantRat_prime_ne_zero_of_large_prime <;> assumption)

end
