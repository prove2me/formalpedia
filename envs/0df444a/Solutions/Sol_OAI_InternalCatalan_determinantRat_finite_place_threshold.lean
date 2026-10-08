-- Prove2me | solution 1 for OAI.InternalCatalan.determinantRat_finite_place_threshold
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:08:04.233887+00:00
-- url     : https://prove2.me/submissions/99511301-8ca2-4bf9-8b81-a5cefc86cf4f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Union
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAICatalanIrrationality
import Theorems.Thm_ZetaNine_HarmonicStability_psi_pnt_rate

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

theorem centralCoeffKernel_of_neg {d : ℤ} (hd : d < 0) :
    centralCoeffKernel d = 0 := by
  simp [centralCoeffKernel, not_le.mpr hd]

theorem centralCoeffKernel_of_odd {d : ℤ} (hd : d % 2 ≠ 0) :
    centralCoeffKernel d = 0 := by
  simp [centralCoeffKernel, hd]

theorem centralCoeffKernel_two_mul (l : ℕ) :
    centralCoeffKernel (2 * (l : ℤ)) = centralCoeff l := by
  have hn : 0 ≤ 2 * (l : ℤ) := by positivity
  have he : (2 * (l : ℤ)) % 2 = 0 := by omega
  have ht : (2 * (l : ℤ)).toNat = 2 * l := by omega
  simp [centralCoeffKernel, hn, he, ht]


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

theorem boundaryMinus_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ) * boundaryMinus (d + 2) =
      ((d + 1 : ℕ) : ℚ) * boundaryMinus d + momentScalar d + momentScalar (d + 1) := by
  have hd : ((d + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [boundaryMinus]
  field_simp

theorem boundaryPlus_step (d : ℕ) :
    ((d + 1 : ℕ) : ℚ) * boundaryPlus (d + 2) =
      (d : ℚ) * boundaryPlus d + 2 / ((d + 1 : ℕ) : ℚ) := by
  have hd : ((d + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [boundaryPlus]
  field_simp




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
-- module Solutions.OAICatalan.Catalan.Analysis.ContactSeries
namespace OAI

noncomputable section

namespace InternalCatalan

open PowerSeries

def centralKernelSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun d => centralCoeffKernel (d : ℤ))

@[simp] theorem coeff_centralKernelSeries (d : ℕ) :
    PowerSeries.coeff d centralKernelSeries = centralCoeffKernel (d : ℤ) :=
  PowerSeries.coeff_mk d _

@[simp] theorem constantCoeff_centralKernelSeries :
    PowerSeries.constantCoeff centralKernelSeries = 1 := by
  simp [centralKernelSeries]

theorem centralCoeffKernel_nat_even (l : ℕ) :
    centralCoeffKernel ((2 * l : ℕ) : ℤ) = centralCoeff l := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using centralCoeffKernel_two_mul l

theorem centralCoeffKernel_nat_odd (l : ℕ) :
    centralCoeffKernel ((2 * l + 1 : ℕ) : ℤ) = 0 := by
  apply centralCoeffKernel_of_odd
  omega

theorem centralCoeffKernel_nat_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ) * centralCoeffKernel ((d + 2 : ℕ) : ℤ) =
      ((d + 1 : ℕ) : ℚ) * centralCoeffKernel (d : ℤ) := by
  by_cases hd : d % 2 = 0
  · obtain ⟨l, rfl⟩ : ∃ l : ℕ, d = 2 * l := ⟨d / 2, by omega⟩
    rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      centralCoeffKernel_nat_even, centralCoeffKernel_nat_even]
    convert centralCoeff_step l using 1 <;> push_cast <;> ring
  · obtain ⟨l, rfl⟩ : ∃ l : ℕ, d = 2 * l + 1 := ⟨d / 2, by omega⟩
    rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      centralCoeffKernel_nat_odd, centralCoeffKernel_nat_odd]
    simp



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.FinitePlaceNumerics
namespace OAI


namespace InternalCatalan

open scoped BigOperators

theorem finitePlace_log_two_lt : Real.log 2 < (693149 / 1000000 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 693149 / 1000000) 8
  have hs : (2 : ℝ) < ∑ i ∈ Finset.range 8,
      (693149 / 1000000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hs.trans_le h

theorem finitePlace_constant_gt_threshold :
    -(229084 / 100000 : ℝ) <
      -(8609 / 4608 : ℝ) -
        ((1 / 2 : ℝ) + (505 / 4608 : ℝ)) * Real.log 2 := by
  linarith [finitePlace_log_two_lt]


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeLoss
namespace OAI


noncomputable section
open MeasureTheory Set
open scoped Interval

namespace InternalCatalan

def oddPrimeLoss (x : ℝ) : ℝ :=
  96 - 2 * max (x - 25) 0 + 2 * max (x - 29) 0 -
    2 * max (x - 65 / 2) 0 - 2 * max (x - 69 / 2) 0 +
    max (x - 40) 0 + max (x - 58) 0 + max (x - 59) 0 + max (x - 65) 0

theorem continuous_oddPrimeLoss : Continuous oddPrimeLoss := by
  unfold oddPrimeLoss
  fun_prop

theorem oddPrimeLoss_of_le_25 (x : ℝ) (hhi : x ≤ 25) :
    oddPrimeLoss x = 96 := by
  simp only [oddPrimeLoss,
    max_eq_right (show x - 25 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 29 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_25_29 (x : ℝ) (hlo : 25 ≤ x) (hhi : x ≤ 29) :
    oddPrimeLoss x = 146 - 2 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_right (show x - 29 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_29_65div2 (x : ℝ) (hlo : 29 ≤ x) (hhi : x ≤ 65 / 2) :
    oddPrimeLoss x = 88 := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_right (show x - 65 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_65div2_69div2 (x : ℝ) (hlo : 65 / 2 ≤ x) (hhi : x ≤ 69 / 2) :
    oddPrimeLoss x = 153 - 2 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_right (show x - 69 / 2 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_69div2_40 (x : ℝ) (hlo : 69 / 2 ≤ x) (hhi : x ≤ 40) :
    oddPrimeLoss x = 222 - 4 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_right (show x - 40 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_40_58 (x : ℝ) (hlo : 40 ≤ x) (hhi : x ≤ 58) :
    oddPrimeLoss x = 182 - 3 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_right (show x - 58 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_58_59 (x : ℝ) (hlo : 58 ≤ x) (hhi : x ≤ 59) :
    oddPrimeLoss x = 124 - 2 * x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 58 by linarith),
    max_eq_right (show x - 59 ≤ (0 : ℝ) by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_59_65 (x : ℝ) (hlo : 59 ≤ x) (hhi : x ≤ 65) :
    oddPrimeLoss x = 65 - x := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 58 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 59 by linarith),
    max_eq_right (show x - 65 ≤ (0 : ℝ) by linarith)]
  ring

theorem oddPrimeLoss_of_ge_65 (x : ℝ) (hlo : 65 ≤ x) :
    oddPrimeLoss x = 0 := by
  simp only [oddPrimeLoss,
    max_eq_left (show (0 : ℝ) ≤ x - 25 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 29 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 69 / 2 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 40 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 58 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 59 by linarith),
    max_eq_left (show (0 : ℝ) ≤ x - 65 by linarith)]
  ring

theorem oddPrimeLoss_mem_Icc (x : ℝ) : oddPrimeLoss x ∈ Icc (0 : ℝ) 96 := by
  by_cases h0 : x ≤ 25
  · rw [oddPrimeLoss_of_le_25 x h0]
    constructor <;> linarith
  by_cases h1 : x ≤ 29
  · rw [oddPrimeLoss_25_29 x (by linarith) h1]
    constructor <;> linarith
  by_cases h2 : x ≤ 65 / 2
  · rw [oddPrimeLoss_29_65div2 x (by linarith) h2]
    constructor <;> linarith
  by_cases h3 : x ≤ 69 / 2
  · rw [oddPrimeLoss_65div2_69div2 x (by linarith) h3]
    constructor <;> linarith
  by_cases h4 : x ≤ 40
  · rw [oddPrimeLoss_69div2_40 x (by linarith) h4]
    constructor <;> linarith
  by_cases h5 : x ≤ 58
  · rw [oddPrimeLoss_40_58 x (by linarith) h5]
    constructor <;> linarith
  by_cases h6 : x ≤ 59
  · rw [oddPrimeLoss_58_59 x (by linarith) h6]
    constructor <;> linarith
  by_cases h7 : x ≤ 65
  · rw [oddPrimeLoss_59_65 x (by linarith) h7]
    constructor <;> linarith
  rw [oddPrimeLoss_of_ge_65 x (by linarith)]
  constructor <;> norm_num



private theorem loss_integral_affine (a b c m : ℝ) :
    (∫ x in a..b, c - m * x) = c * (b - a) - m * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_sub
    (f := fun _ : ℝ => c) (g := fun x : ℝ => m * x)
    (continuous_const.intervalIntegrable a b)
    ((continuous_const.mul continuous_id).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul m (fun x : ℝ => x)]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

theorem integral_oddPrimeLoss_0_25 :
    (∫ x in (0 : ℝ)..(25), oddPrimeLoss x) = 2400 := by
  calc
    (∫ x in (0 : ℝ)..(25), oddPrimeLoss x) =
        ∫ x in (0 : ℝ)..(25), 96 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_of_le_25 x hx.2
    _ = 2400 := by norm_num [intervalIntegral.integral_const]

theorem integral_oddPrimeLoss_25_29 :
    (∫ x in (25 : ℝ)..(29), oddPrimeLoss x) = 368 := by
  calc
    (∫ x in (25 : ℝ)..(29), oddPrimeLoss x) =
        ∫ x in (25 : ℝ)..(29), 146 - 2 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_25_29 x hx.1 hx.2
    _ = 368 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_29_65div2 :
    (∫ x in (29 : ℝ)..(65 / 2), oddPrimeLoss x) = 308 := by
  calc
    (∫ x in (29 : ℝ)..(65 / 2), oddPrimeLoss x) =
        ∫ x in (29 : ℝ)..(65 / 2), 88 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_29_65div2 x hx.1 hx.2
    _ = 308 := by norm_num [intervalIntegral.integral_const]

theorem integral_oddPrimeLoss_65div2_69div2 :
    (∫ x in (65 / 2 : ℝ)..(69 / 2), oddPrimeLoss x) = 172 := by
  calc
    (∫ x in (65 / 2 : ℝ)..(69 / 2), oddPrimeLoss x) =
        ∫ x in (65 / 2 : ℝ)..(69 / 2), 153 - 2 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_65div2_69div2 x hx.1 hx.2
    _ = 172 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_69div2_40 :
    (∫ x in (69 / 2 : ℝ)..(40), oddPrimeLoss x) = 803 / 2 := by
  calc
    (∫ x in (69 / 2 : ℝ)..(40), oddPrimeLoss x) =
        ∫ x in (69 / 2 : ℝ)..(40), 222 - 4 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_69div2_40 x hx.1 hx.2
    _ = 803 / 2 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_40_58 :
    (∫ x in (40 : ℝ)..(58), oddPrimeLoss x) = 630 := by
  calc
    (∫ x in (40 : ℝ)..(58), oddPrimeLoss x) =
        ∫ x in (40 : ℝ)..(58), 182 - 3 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_40_58 x hx.1 hx.2
    _ = 630 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_58_59 :
    (∫ x in (58 : ℝ)..(59), oddPrimeLoss x) = 7 := by
  calc
    (∫ x in (58 : ℝ)..(59), oddPrimeLoss x) =
        ∫ x in (58 : ℝ)..(59), 124 - 2 * x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_58_59 x hx.1 hx.2
    _ = 7 := by rw [loss_integral_affine]; norm_num

theorem integral_oddPrimeLoss_59_65 :
    (∫ x in (59 : ℝ)..(65), oddPrimeLoss x) = 18 := by
  calc
    (∫ x in (59 : ℝ)..(65), oddPrimeLoss x) =
        ∫ x in (59 : ℝ)..(65), 65 - x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      exact oddPrimeLoss_59_65 x hx.1 hx.2
    _ = 18 := by
      simpa only [one_mul] using
        (show (∫ x in (59 : ℝ)..65, 65 - 1 * x) = 18 by
          rw [loss_integral_affine]; norm_num)

theorem integral_oddPrimeLoss :
    (∫ x in (0 : ℝ)..65, oddPrimeLoss x) = 8609 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (0) (25))
    (continuous_oddPrimeLoss.intervalIntegrable (25) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (25) (29))
    (continuous_oddPrimeLoss.intervalIntegrable (29) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (29) (65 / 2))
    (continuous_oddPrimeLoss.intervalIntegrable (65 / 2) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (65 / 2) (69 / 2))
    (continuous_oddPrimeLoss.intervalIntegrable (69 / 2) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (69 / 2) (40))
    (continuous_oddPrimeLoss.intervalIntegrable (40) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (40) (58))
    (continuous_oddPrimeLoss.intervalIntegrable (58) 65)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_oddPrimeLoss.intervalIntegrable (58) (59))
    (continuous_oddPrimeLoss.intervalIntegrable (59) 65)]
  rw [integral_oddPrimeLoss_0_25,
    integral_oddPrimeLoss_25_29,
    integral_oddPrimeLoss_29_65div2,
    integral_oddPrimeLoss_65div2_69div2,
    integral_oddPrimeLoss_69div2_40,
    integral_oddPrimeLoss_40_58,
    integral_oddPrimeLoss_58_59,
    integral_oddPrimeLoss_59_65]
  norm_num

theorem integral_oddPrimeLoss_25_65 :
    (∫ x in (25 : ℝ)..65, oddPrimeLoss x) = 3809 / 2 := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_oddPrimeLoss.intervalIntegrable 0 25)
    (continuous_oddPrimeLoss.intervalIntegrable 25 65)
  rw [integral_oddPrimeLoss_0_25, integral_oddPrimeLoss] at h
  linarith

end InternalCatalan

end

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

theorem centralCoeff_odd_prime_nonneg (p l : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    0 ≤ padicValRat p (centralCoeff l) := by
  rw [centralCoeff_odd_prime_valuation p l hp hp2]
  exact Int.natCast_nonneg _

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

theorem prime_sum_valuation_lower {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (B : ℤ) (hB : B ≤ 0)
    (hf : ∀ x ∈ s, B ≤ padicValRat p (f x)) :
    B ≤ padicValRat p (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases hz : f a + ∑ x ∈ s, f x = 0
    · simpa [hz] using hB
    · apply le_trans _ (padicValRat.min_le_padicValRat_add hz)
      exact le_min (hf a (Finset.mem_insert_self a s))
        (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

theorem prime_sub_valuation_lower {p : ℕ} [Fact p.Prime]
    (a b : ℚ) (B : ℤ) (hB : B ≤ 0)
    (ha : B ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    B ≤ padicValRat p (a - b) := by
  by_cases hz : a - b = 0
  · simpa [hz] using hB
  · have h := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa only [sub_eq_add_neg] using hz)
    rw [← sub_eq_add_neg, padicValRat.neg] at h
    exact (le_min ha hb).trans h

theorem prime_mul_valuation_lower {p : ℕ} [Fact p.Prime]
    (a b : ℚ) (A B : ℤ) (hAB : A + B ≤ 0)
    (ha : A ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    A + B ≤ padicValRat p (a * b) := by
  by_cases haz : a = 0
  · simpa [haz] using hAB
  by_cases hbz : b = 0
  · simpa [hbz] using hAB
  rw [padicValRat.mul haz hbz]
  exact add_le_add ha hb

theorem prime_div_nat_valuation_lower {p : ℕ} [Fact p.Prime]
    (a : ℚ) (z H : ℕ) (A : ℤ) (hA : A ≤ 0) (hz : z ≤ H)
    (ha : A ≤ padicValRat p a) :
    A - (Nat.log p H : ℤ) ≤ padicValRat p (a / (z : ℚ)) := by
  by_cases haz : a = 0
  · simp only [haz, zero_div, padicValRat.zero]
    have : 0 ≤ (Nat.log p H : ℤ) := by positivity
    omega
  by_cases hzz : z = 0
  · simp only [hzz, Nat.cast_zero, div_zero, padicValRat.zero]
    have : 0 ≤ (Nat.log p H : ℤ) := by positivity
    omega
  have hval := (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hzz
  rw [padicValRat.div haz hzq, padicValRat.of_nat]
  omega

theorem centralBinom_prime_valuation_le_log {p : ℕ} [Fact p.Prime] (l : ℕ) :
    padicValNat p ((2 * l).choose l) ≤ Nat.log p (2 * l) := by
  rw [padicValNat_choose (p := p) (by omega : l ≤ 2 * l)
    (by omega : Nat.log p (2 * l) < Nat.log p (2 * l) + 1)]
  calc
    _ ≤ (Finset.Ico 1 (Nat.log p (2 * l) + 1)).card := Finset.card_filter_le _ _
    _ = Nat.log p (2 * l) := by simp

theorem centralCoeff_odd_prime_log_bounds {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (l H : ℕ) (hl : 2 * l ≤ H) :
    0 ≤ padicValRat p (centralCoeff l) ∧
      padicValRat p (centralCoeff l) ≤ (Nat.log p H : ℤ) := by
  rw [centralCoeff_odd_prime_valuation p l hp.out hp2]
  constructor
  · positivity
  · exact_mod_cast (centralBinom_prime_valuation_le_log (p := p) l).trans
      (Nat.log_mono_right hl)

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

theorem two_odd_prime_valuation {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    padicValRat p (2 : ℚ) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
    padicValRat.of_nat, padicValNat_primes hp2]
  norm_num

theorem boundaryFactor_odd_prime_log_bounds {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (z H : ℕ) (hz : z ≤ H) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryFactor z) ∧
      padicValRat p (boundaryFactor z) ≤ (Nat.log p H : ℤ) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  by_cases he : z % 2 = 0
  · have hpair : z = 2 * (z / 2) := by omega
    rw [boundaryFactor, if_pos he]
    have hc := centralCoeff_odd_prime_log_bounds hp2 (z / 2) H (by omega)
    constructor <;> omega
  · have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
    have hc := centralCoeff_odd_prime_log_bounds hp2 ((z - 1) / 2) H (by omega)
    have hzval : (padicValNat p z : ℤ) ≤ (Nat.log p H : ℤ) := by
      exact_mod_cast (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
    rw [boundaryFactor, if_neg he, one_div, padicValRat.inv,
      padicValRat.mul hz0 (centralCoeff_ne_zero _), padicValRat.of_nat]
    constructor <;> omega

theorem momentScalar_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i H : ℕ) (hi : i < H) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (momentScalar i) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  by_cases he : i % 2 = 0
  · have hi0 : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hc := centralCoeff_odd_prime_log_bounds hp2 (i / 2) H (by omega)
    have hiv : (padicValNat p (i + 1) : ℤ) ≤ (Nat.log p H : ℤ) := by
      exact_mod_cast (padicValNat_le_nat_log (p := p) (i + 1)).trans
        (Nat.log_mono_right (by omega : i + 1 ≤ H))
    rw [momentScalar, if_pos he,
      padicValRat.div (by norm_num) (mul_ne_zero hi0 (centralCoeff_ne_zero _)),
      padicValRat.mul hi0 (centralCoeff_ne_zero _),
      two_odd_prime_valuation hp2, padicValRat.of_nat]
    omega
  · simp only [momentScalar, if_neg he, padicValRat.zero]
    omega

theorem boundaryPlusWeight_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z H : ℕ) (hz0 : 0 < z) (hz : z ≤ H) :
    -3 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryPlusWeight z) := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hfv := (boundaryFactor_odd_prime_log_bounds hp2 z H hz).2
  have hzv : (padicValNat p z : ℤ) ≤ (Nat.log p H : ℤ) := by
    exact_mod_cast (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
  rw [boundaryPlusWeight,
    padicValRat.div (by norm_num) (mul_ne_zero (pow_ne_zero _ hzq) (boundaryFactor_ne_zero _)),
    padicValRat.mul (pow_ne_zero _ hzq) (boundaryFactor_ne_zero _),
    padicValRat.pow, padicValRat.of_nat, two_odd_prime_valuation hp2]
  norm_num
  omega

theorem boundaryMinusWeight_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z H : ℕ) (hz0 : 0 < z) (hz : z ≤ H) :
    -4 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryMinusWeight z) := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  have hfv := (boundaryFactor_odd_prime_log_bounds hp2 z H hz).2
  have hzv : (padicValNat p z : ℤ) ≤ (Nat.log p H : ℤ) := by
    exact_mod_cast (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
  unfold boundaryMinusWeight
  split_ifs
  · rw [padicValRat.div (by norm_num)
      (mul_ne_zero (pow_ne_zero _ hzq) (pow_ne_zero _ (boundaryFactor_ne_zero _))),
      padicValRat.mul (pow_ne_zero _ hzq) (pow_ne_zero _ (boundaryFactor_ne_zero _)),
      padicValRat.pow, padicValRat.pow, padicValRat.of_nat, two_odd_prime_valuation hp2]
    norm_num
    omega
  · rw [padicValRat.div (by norm_num) hzq, two_odd_prime_valuation hp2, padicValRat.of_nat]
    omega





open scoped BigOperators

theorem harmonicRat_prime_log_lower {p : ℕ} [Fact p.Prime] (d n H : ℕ) (hn : n ≤ H) :
    -((d : ℤ) * (Nat.log p H : ℤ)) ≤ padicValRat p (harmonicRat d n) := by
  unfold harmonicRat
  apply prime_sum_valuation_lower
  · have : 0 ≤ (d : ℤ) * (Nat.log p H : ℤ) := by positivity
    omega
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hval : padicValNat p (k + 1) ≤ Nat.log p H :=
      (padicValNat_le_nat_log (p := p) (k + 1)).trans
        (Nat.log_mono_right (by omega : k + 1 ≤ H))
    have hval' : (padicValNat p (k + 1) : ℤ) ≤ (Nat.log p H : ℤ) := by
      exact_mod_cast hval
    simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hval' (by positivity))

private theorem zetaRat_prime_log_lower_of_le {p : ℕ} [Fact p.Prime] (H i j : ℕ)
    (hi : i < H) (hji : j ≤ i) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (zetaRat i j) := by
  have hj : j < H := lt_of_le_of_lt hji hi
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, padicValRat.neg]
    simpa using harmonicRat_prime_log_lower 2 i H (Nat.le_of_lt hi)
  · have hden : ((i - j : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show i - j ≠ 0 by omega)
    have heq : (i : ℚ) - (j : ℚ) = ((i - j : ℕ) : ℚ) :=
      (Nat.cast_sub hji).symm
    by_cases hnum : harmonicRat 1 i - harmonicRat 1 j = 0
    · rw [zetaRat_of_ne hij, hnum, zero_div, padicValRat.zero]
      have : 0 ≤ (Nat.log p H : ℤ) := by positivity
      omega
    · have hival : -(Nat.log p H : ℤ) ≤ padicValRat p (harmonicRat 1 i) := by
        simpa using harmonicRat_prime_log_lower 1 i H (Nat.le_of_lt hi)
      have hjval : -(Nat.log p H : ℤ) ≤ padicValRat p (harmonicRat 1 j) := by
        simpa using harmonicRat_prime_log_lower 1 j H (Nat.le_of_lt hj)
      have hsum := padicValRat.min_le_padicValRat_add (p := p)
        (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
        (by simpa only [sub_eq_add_neg] using hnum)
      rw [← sub_eq_add_neg, padicValRat.neg] at hsum
      have hnval : -(Nat.log p H : ℤ) ≤
          padicValRat p (harmonicRat 1 i - harmonicRat 1 j) :=
        (le_min hival hjval).trans hsum
      have hdval : padicValNat p (i - j) ≤ Nat.log p H :=
        (padicValNat_le_nat_log (p := p) (i - j)).trans
          (Nat.log_mono_right (by omega : i - j ≤ H))
      rw [zetaRat_of_ne hij, heq, padicValRat.div hnum hden, padicValRat.of_nat]
      omega

theorem zetaRat_prime_log_lower {p : ℕ} [Fact p.Prime] (H i j : ℕ) (hi : i < H) (hj : j < H) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (zetaRat i j) := by
  rcases le_total j i with hji | hij
  · exact zetaRat_prime_log_lower_of_le H i j hi hji
  · rw [zetaRat_symm]
    exact zetaRat_prime_log_lower_of_le H j i hj hij

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

theorem Cdegree_eq_L_add_g (N : ℕ) : Cdegree N = L N + g N := by
  unfold Cdegree L g
  omega

theorem H_eq_Cdegree_add_h (N : ℕ) : H N = Cdegree N + h N := by
  unfold H Cdegree h
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

theorem A_le_reversed_T_min {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    A N ≤ Cdegree N - 1 - rowDistance N r := by
  have hd := rowDistance_le hN hr
  unfold n g A Cdegree at *
  omega

theorem A_add_one_le_reversed_U_min {N r : ℕ} (hN : 0 < N)
    (hr : r < n N) (hd : 0 < rowDistance N r) :
    A N + 1 ≤ Cdegree N - 1 - (rowDistance N r - 1) := by
  have hdist := rowDistance_le hN hr
  unfold n g A Cdegree at *
  omega









end

noncomputable section
open Set
open scoped BigOperators



end

theorem twoAdicQuadratic_lower (N : ℕ) (m l : ℝ)
    (hm : 0 ≤ m) (hl : 0 ≤ l) (hml : m + l ≤ (n N : ℝ)) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 ≤
      -((H N : ℝ) - (b N : ℝ)) * m + (3 / 2 : ℝ) * m ^ 2 +
        (1 / 2 : ℝ) * l ^ 2 + (Cdegree N : ℝ) * ((n N : ℝ) - m - l) := by
  simp only [n, Nat.cast_mul, Nat.cast_ofNat] at hml
  simp only [n, H, b, Cdegree, Nat.cast_mul, Nat.cast_ofNat]
  have hN : 0 ≤ (N : ℝ) :=
    nonneg_of_mul_nonneg_right ((add_nonneg hm hl).trans hml) (by norm_num : (0 : ℝ) < 48)
  have hl_bound : l ≤ 48 * (N : ℝ) := by linarith only [hm, hml]
  have hgap : 0 ≤ 48 * (N : ℝ) - m - l := by linarith only [hml]
  have hfactor : 0 ≤ 63 * (N : ℝ) - (48 * (N : ℝ) - m + l) / 2 := by
    linarith only [hN, hm, hl, hl_bound]
  have hproduct := mul_nonneg hgap hfactor
  have hsquare := sq_nonneg (m - (53 / 2 : ℝ) * (N : ℝ))
  nlinarith only [hproduct, hsquare]

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

theorem reversedRow_coeff_eq_zero_of_lt (C d : ℕ) (F : ℤ[X])
    (hF : F.natDegree ≤ d) (hd : d < C) {i : ℕ} (hi : i < C - 1 - d) :
    (reversedRow C F).coeff i = 0 := by
  rw [reversedRow_coeff, if_pos (by omega)]
  apply coeff_eq_zero_of_natDegree_lt
  omega

theorem coeff_mul_eq_zero_below_right (P Q : ℤ[X]) (B : ℕ)
    (hQ : ∀ i < B, Q.coeff i = 0) {k : ℕ} (hk : k < B) :
    (P * Q).coeff k = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hQ j (by omega), mul_zero]

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

theorem rowD_natDegree_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (rowD N r).natDegree ≤ H N - 1 := by
  unfold rowD
  rw [mul_assoc]
  calc
    _ ≤ (((1 - X : ℤ[X]) ^ h N) *
        reversedRow (Cdegree N) (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((1 - X : ℤ[X]) ^ h N).natDegree +
        (reversedRow (Cdegree N)
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ h N + (Cdegree N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le N) (reversedRow_natDegree_le _ _)
    _ ≤ H N - 1 := by unfold h Cdegree H; omega

theorem rowP_coeff_eq_zero_of_lt {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hi : i < A N) : (rowP N r).coeff i = 0 := by
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (A N) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r) _
  · simp [Chebyshev.natDegree_T]
  · exact rowDistance_lt_Cdegree hN hr
  · exact lt_of_lt_of_le hj (A_le_reversed_T_min hN hr)

theorem rowD_eq_zero_of_distance_zero {N r : ℕ} (hd : rowDistance N r = 0) :
    rowD N r = 0 := by
  simp [rowD, hd]

theorem rowD_coeff_eq_zero_of_lt {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hi : i < A N + 1) : (rowD N r).coeff i = 0 := by
  by_cases hd : rowDistance N r = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ (A N + 1) _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r - 1) _
    · simp [Chebyshev.natDegree_U]
    · have hdist := rowDistance_lt_Cdegree hN hr
      omega
    · exact lt_of_lt_of_le hj (A_add_one_le_reversed_U_min hN hr (by omega))

theorem rowP_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowP N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowP_natDegree_le hN r
  have hH : 0 < H N := by unfold H; omega
  omega

theorem rowD_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowD N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowD_natDegree_le hN r
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

theorem rowDistance_of_le_g {N r : ℕ} (hrg : r ≤ g N) :
    rowDistance N r = g N - r := by
  unfold rowDistance rowOffset
  omega

theorem rowP_coeff_eq_zero_of_lt_left_contact {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hi : i < L N - 1) :
    (rowP N r).coeff i = 0 := by
  have hdist := rowDistance_of_le_g hrg
  have hmin : L N - 1 ≤ Cdegree N - 1 - rowDistance N r := by
    rw [hdist]
    unfold L Cdegree g
    omega
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (L N - 1) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r) _
  · simp [Chebyshev.natDegree_T]
  · exact rowDistance_lt_Cdegree hN hr
  · exact lt_of_lt_of_le hj hmin

theorem rowD_coeff_eq_zero_of_lt_left_contact {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hi : i < L N) :
    (rowD N r).coeff i = 0 := by
  by_cases hd : rowDistance N r = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · have hdist := rowDistance_of_le_g hrg
    have hmin : L N ≤ Cdegree N - 1 - (rowDistance N r - 1) := by
      rw [hdist]
      rw [hdist] at hd
      unfold L Cdegree g at *
      omega
    unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ (L N) _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r - 1) _
    · simp [Chebyshev.natDegree_U]
    · have hdc := rowDistance_lt_Cdegree hN hr
      omega
    · exact lt_of_lt_of_le hj hmin

theorem row_contact_of_le_g {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  rw [rowD_coeff_eq_zero_of_lt_left_contact hN hr hrg hj, Int.cast_zero]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hil : i < L N - 1
  · rw [rowP_coeff_eq_zero_of_lt_left_contact hN hr hrg hil, Int.cast_zero, zero_mul]
  · rw [centralCoeffKernel_of_neg (by omega : (j : ℤ) - i - 1 < 0), mul_zero]



variable {K : Type*} [Field K]




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



















open scoped BigOperators

def palindromicRatResidue (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p :=
  (x.num : ZMod p) / (x.den : ZMod p)





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













end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker













end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker








end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeCentralZeta
namespace OAI


noncomputable section

namespace InternalCatalan

theorem harmonicRat_prime_scaled_reduction {p n : ℕ} [hp : Fact p.Prime]
    (hn : n < p ^ 2) :
    (((p : ℚ) * harmonicRat 1 n).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * harmonicRat 1 n) =
        palindromicRatResidue p (harmonicRat 1 (n / p)) := by
  have hquot : n / p < p := by
    apply (Nat.div_lt_iff_lt_mul hp.out.pos).mpr
    simpa only [pow_two] using hn
  have hb := harmonicRat_small_den_ne_zero (p := p) hquot 1
  have he :
      (((p : ℚ) * harmonicRat 1 n - harmonicRat 1 (n / p)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * harmonicRat 1 n - harmonicRat 1 (n / p)) = 0 := by
    have h := harmonicRat_prime_digit_error_valuation (n := n) hp.out (by decide : 0 < 1)
    simp only [pow_one] at h
    rcases h with hzero | hpos
    · rw [hzero]
      norm_num [palindromicRatResidue]
    · exact rational_residue_zero_of_positive_valuation (by omega)
  have hadd := rational_residue_add he.1 hb
  have hsplit : (p : ℚ) * harmonicRat 1 n =
      ((p : ℚ) * harmonicRat 1 n - harmonicRat 1 (n / p)) + harmonicRat 1 (n / p) := by ring
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hadd.1
  · rw [hsplit, palindromicRatResidue_add he.1 hb, he.2, zero_add]

theorem zetaRat_central_low_reduction {p i j : ℕ} [Fact p.Prime]
    (hi : i < p) (hj : j < p) :
    (((p : ℚ) * zetaRat i j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * zetaRat i j) = 0 := by
  have h := rational_residue_mul (p := p) (a := (p : ℚ)) (by simp)
    (zetaRat_small_den_ne_zero hi hj)
  refine ⟨h.1, ?_⟩
  change (((p : ℚ) * zetaRat i j).num : ZMod p) /
    (((p : ℚ) * zetaRat i j).den : ZMod p) = 0
  rw [h.2]
  simp

theorem zetaRat_central_high_reduction {p ell j : ℕ} [hp : Fact p.Prime]
    (hellj : ell < j) (hj : j < p) :
    (((p : ℚ) * zetaRat (p + ell) j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * zetaRat (p + ell) j) =
        1 / ((ell : ZMod p) - (j : ZMod p)) := by
  have hell : ell < p := hellj.trans hj
  have hi2 : p + ell < p ^ 2 := by nlinarith [hp.out.two_le]
  have hj2 : j < p ^ 2 := by nlinarith [hp.out.two_le]
  have hi := harmonicRat_prime_scaled_reduction (p := p) hi2
  have hjh := harmonicRat_prime_scaled_reduction (p := p) hj2
  have hiquot : (p + ell) / p = 1 := by
    simpa only [Nat.mul_one, Nat.div_eq_of_lt hell, add_zero] using
      (Nat.mul_add_div hp.out.pos 1 ell)
  have hirst : palindromicRatResidue p ((p : ℚ) * harmonicRat 1 (p + ell)) = 1 := by
    rw [hi.2, hiquot]
    norm_num [harmonicRat, palindromicRatResidue]
  have hjrst : palindromicRatResidue p ((p : ℚ) * harmonicRat 1 j) = 0 := by
    rw [hjh.2, Nat.div_eq_of_lt hj]
    norm_num [palindromicRatResidue]
  have hsub := rational_residue_sub hi.1 hjh.1
  have hsubres : palindromicRatResidue p
      ((p : ℚ) * harmonicRat 1 (p + ell) - (p : ℚ) * harmonicRat 1 j) = 1 := by
    rw [palindromicRatResidue_sub hi.1 hjh.1, hirst, hjrst, sub_zero]
  have hdenpos : 0 < p + ell - j := by omega
  have hdenlt : p + ell - j < p := by omega
  have hden : ((p + ell - j : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdenpos hdenlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hf := nat_fraction_reduced_residue (p := p) 1 (p + ell - j) hden
  simp only [Nat.cast_one] at hf
  have hm := rational_residue_mul hsub.1 hf.1
  have hsplit : (p : ℚ) * zetaRat (p + ell) j =
      ((p : ℚ) * harmonicRat 1 (p + ell) - (p : ℚ) * harmonicRat 1 j) *
        (1 / ((p + ell - j : ℕ) : ℚ)) := by
    rw [zetaRat_of_ne (by omega : p + ell ≠ j), Nat.cast_sub (by omega : j ≤ p + ell)]
    ring
  have hdenres : ((p + ell - j : ℕ) : ZMod p) = (ell : ZMod p) - (j : ZMod p) := by
    rw [Nat.cast_sub (by omega : j ≤ p + ell), Nat.cast_add]
    simp
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hm.1
  · rw [hsplit, palindromicRatResidue_mul hsub.1 hf.1, hsubres]
    change 1 * (((1 / ((p + ell - j : ℕ) : ℚ)).num : ZMod p) /
      ((1 / ((p + ell - j : ℕ) : ℚ)).den : ZMod p)) = _
    rw [hf.2, hdenres, one_mul]

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

theorem oddPrime_P_coefficient_contraction_support {p H k ell : ℕ}
    (hp : 0 < p) (hell : ell < p) (P : (ZMod p)[X])
    (hP : ∀ i, H ≤ i → P.coeff i = 0) (f : ℤ → ZMod p) :
    (∑ i ∈ Finset.range H,
      P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
        f (oddPrimeDigitRow p i (k * p + ell))) =
      ∑ v ∈ Finset.range (H + 1),
        (X * P * oddPrimeWeight p).coeff (v * p + ell) * f ((v : ℤ) - 1) := by
  classical
  have hbound : H ≤ H * p := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left H (show 1 ≤ p from hp)
  have hpad : ∀ i, H * p ≤ i → P.coeff i = 0 :=
    fun i hi => hP i (hbound.trans hi)
  calc
    _ = ∑ i ∈ Finset.range (H * p),
        P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
          f (oddPrimeDigitRow p i (k * p + ell)) := by
      apply Finset.sum_subset (Finset.range_mono hbound)
      intro i hi hnot
      have hiH : H ≤ i := by simpa only [Finset.mem_range, not_lt] using hnot
      rw [hP i hiH, zero_mul, zero_mul]
    _ = _ := oddPrime_P_coefficient_contraction hp hell P hpad f

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
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeResidueGathering
namespace OAI


open scoped BigOperators

namespace InternalCatalan

theorem oddPrime_residue_sum_gather {R : Type*} [Semiring R]
    {p ell H : ℕ} (hp : 0 < p) (hell : ell < p)
    (a g : ℕ → R) (ha : ∀ i, H ≤ i → a i = 0) :
    (∑ i ∈ Finset.range H, if i % p = ell then a i * g (i / p) else 0) =
      ∑ u ∈ Finset.range H, a (u * p + ell) * g u := by
  classical
  have hmod (u : ℕ) : (u * p + ell) % p = ell := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hell]
  have hquot (u : ℕ) : (u * p + ell) / p = u := by
    rw [Nat.mul_comm u p, Nat.mul_add_div hp, Nat.div_eq_of_lt hell, add_zero]
  refine Finset.sum_bij_ne_zero (fun i _ _ => i / p) ?_ ?_ ?_ ?_
  · intro i hi hfi
    exact Finset.mem_range.mpr ((Nat.div_le_self i p).trans_lt (Finset.mem_range.mp hi))
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
    have hlt : u * p + ell < H := by
      by_contra h
      have hz := ha (u * p + ell) (by omega)
      exact hgu (by rw [hz, zero_mul])
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



end InternalCatalan



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def oddPrimeExtractedP (p N r ell v : ℕ) : ZMod p :=
  (X * (rowP N r).map (Int.castRingHom (ZMod p)) * oddPrimeWeight p).coeff (v * p + ell)

def oddPrimeExtractedD (p N r ell u : ℕ) : ZMod p :=
  ((rowD N r).coeff (u * p + ell) : ZMod p)

theorem rawEntryRat_general_column_layer {p N r k ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hH : H N < p ^ 2) (hell : ell < p)
    (hj : k * p + ell < H N) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r (k * p + ell)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (k * p + ell)) =
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k)) -
      (3 / 2 : ZMod p) * ∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u k) := by
  let P : (ZMod p)[X] := (rowP N r).map (Int.castRingHom (ZMod p))
  have hP : ∀ t, H N ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, rowP_coeff_eq_zero_of_ge hN ht, map_zero]
  have hquot : (k * p + ell) / p = k := by
    rw [Nat.mul_comm k p, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hell, add_zero]
  have hmod : (k * p + ell) % p = ell := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hell]
  have hraw := rawEntryRat_prime_digit_reduction (p := p) (N := N) (r := r)
    hp2 hH hj z hz
  have hpg := oddPrime_P_coefficient_contraction_support (H := H N) (k := k)
    hp.out.pos hell P hP (fun v => palindromicRatResidue p (momentRatSigned v k))
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a = (a : ZMod p) := rfl
  have hpg' :
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell)) *
        palindromicRatResidue p (momentRatSigned (oddPrimeDigitRow p t (k * p + ell)) k)) =
      ∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k) := by
    simpa only [P, coeff_map, oddPrimeExtractedP, hcast] using hpg
  have hdg := oddPrime_residue_sum_gather hp.out.pos hell
    (fun t => ((rowD N r).coeff t : ZMod p))
    (fun u => palindromicRatResidue p (zetaRat u k))
    (fun t ht => by rw [rowD_coeff_eq_zero_of_ge hN ht, Int.cast_zero])
  have hdg' :
      (∑ t ∈ Finset.range (H N), ((rowD N r).coeff t : ZMod p) *
        (if t % p = ell then palindromicRatResidue p (zetaRat (t / p) k) else 0)) =
      ∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u k) := by
    simpa only [mul_ite, mul_zero, oddPrimeExtractedD] using hdg
  refine ⟨hraw.1, ?_⟩
  have hres :
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (k * p + ell)) =
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell)) *
        palindromicRatResidue p (momentRatSigned (oddPrimeDigitRow p t (k * p + ell)) k)) -
      (3 / 2 : ZMod p) *
        ∑ t ∈ Finset.range (H N), ((rowD N r).coeff t : ZMod p) *
          (if t % p = ell then palindromicRatResidue p (zetaRat (t / p) k) else 0) := by
    simpa only [palindromicRatResidue, hquot, hmod] using hraw.2
  rw [hres, hpg', hdg']

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators




end InternalCatalan

end



namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrime_central_P_coefficient {p H ell : ℕ} (hp : 0 < p)
    (hH : H ≤ 2 * p) (P : (ZMod p)[X]) (hP : ∀ i, H ≤ i → P.coeff i = 0) :
    (∑ i ∈ Finset.range H, P.coeff i *
      (if p + ell ≤ i then 2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i) else 0)) =
      2 * (X * P * oddPrimeWeight p).coeff (2 * p + ell) := by
  rw [oddPrimeExtraction_coeff hp P hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < H := Finset.mem_range.mp hi
  by_cases hactive : p + ell ≤ i
  · have hd : 2 * p + ell - 1 - i < p := by omega
    have hindex : 2 * p + ell = i + 1 + (2 * p + ell - 1 - i) := by omega
    rw [if_pos hactive, Finset.sum_eq_single (2 * p + ell - 1 - i)]
    · rw [if_pos hindex]
      ring
    · intro d hd' hne
      have hneq : 2 * p + ell ≠ i + 1 + d := by omega
      rw [if_neg hneq]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hd)).elim
  · rw [if_neg hactive, mul_zero]
    have hz : (∑ d ∈ Finset.range p,
        if 2 * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hd' : d < p := Finset.mem_range.mp hd
      have hneq : 2 * p + ell ≠ i + 1 + d := by omega
      rw [if_neg hneq]
    rw [hz, mul_zero]

end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rowD_zetaRat_central_reduction_coeff {p N r j : ℕ} [hp : Fact p.Prime]
    (_hN : 0 < N) (hpH : p ≤ H N) (_hH : H N ≤ 2 * p)
    (hJ : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) *
        (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)) =
          -(∑ ell ∈ Finset.range (H N - p),
            ((rowD N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun i => ((rowD N r).coeff i : ℚ) * ((p : ℚ) * zetaRat i j)
  have hlow (i : ℕ) (hi : i < p) :
      ((f i).den : ZMod p) ≠ 0 ∧ palindromicRatResidue p (f i) = 0 := by
    have hzeta := zetaRat_central_low_reduction hi hj
    have hmul := rational_residue_mul (a := ((rowD N r).coeff i : ℚ))
      (by simp) hzeta.1
    refine ⟨hmul.1, ?_⟩
    change palindromicRatResidue p
      (((rowD N r).coeff i : ℚ) * ((p : ℚ) * zetaRat i j)) = 0
    rw [palindromicRatResidue_mul (by simp) hzeta.1, hzeta.2, mul_zero]
  have hhigh (ell : ℕ) (hell : ell < H N - p) :
      ((f (p + ell)).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f (p + ell)) =
          -(((rowD N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
    have hellj : ell < j := hell.trans_le hJ
    have hzeta := zetaRat_central_high_reduction (p := p) hellj hj
    have hmul := rational_residue_mul (a := ((rowD N r).coeff (p + ell) : ℚ))
      (by simp) hzeta.1
    have hden : (ell : ZMod p) - (j : ZMod p) = -((j - ell : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_lt hellj)]
      ring
    refine ⟨hmul.1, ?_⟩
    change palindromicRatResidue p
      (((rowD N r).coeff (p + ell) : ℚ) * ((p : ℚ) * zetaRat (p + ell) j)) = _
    rw [palindromicRatResidue_mul (by simp) hzeta.1,
      palindromicRatResidue_intCast, hzeta.2, hden, div_neg]
    ring
  have hden (i : ℕ) (hi : i ∈ Finset.range (H N)) : ((f i).den : ZMod p) ≠ 0 := by
    have hiH := Finset.mem_range.mp hi
    by_cases hip : i < p
    · exact (hlow i hip).1
    · have heq : p + (i - p) = i := by omega
      have h := (hhigh (i - p) (by omega)).1
      simpa only [heq] using h
  have hsum := rational_residue_sum (Finset.range (H N)) f hden
  have hscale : (p : ℚ) *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j) =
        ∑ i ∈ Finset.range (H N), f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    ring
  have hsplit :
      (∑ i ∈ Finset.range (H N), palindromicRatResidue p (f i)) =
        (∑ i ∈ Finset.range p, palindromicRatResidue p (f i)) +
        ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f (p + ell)) := by
    conv_lhs => rw [show H N = p + (H N - p) by omega, Finset.sum_range_add]
  have hlowSum : (∑ i ∈ Finset.range p, palindromicRatResidue p (f i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact (hlow i (Finset.mem_range.mp hi)).2
  have hhighSum :
      (∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f (p + ell))) =
        -(∑ ell ∈ Finset.range (H N - p),
          ((rowD N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ell hell => (hhigh ell (Finset.mem_range.mp hell)).2)
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hsum.1
  · rw [hscale]
    change (( (∑ i ∈ Finset.range (H N), f i).num : ZMod p) /
      ((∑ i ∈ Finset.range (H N), f i).den : ZMod p)) = _
    rw [hsum.2]
    change (∑ i ∈ Finset.range (H N), palindromicRatResidue p (f i)) = _
    rw [hsplit, hlowSum, zero_add, hhighSum]

theorem rowD_zetaRat_central_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) *
        (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)) =
          -(∑ ell ∈ Finset.range (H N - p),
            oddPrimeExtractedD p N r ell 1 / ((j - ell : ℕ) : ZMod p)) := by
  simpa only [oddPrimeExtractedD, Nat.one_mul] using
    rowD_zetaRat_central_reduction_coeff (p := p) (N := N) (r := r) (j := j)
      hN hpH hH hjlo hj

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimePairedColumnIntegrality
namespace OAI


namespace InternalCatalan

theorem rational_valuation_nonneg_of_den_ne_zero {p : ℕ} [Fact p.Prime]
    {q : ℚ} (hd : (q.den : ZMod p) ≠ 0) : 0 ≤ padicValRat p q := by
  have hnot : ¬p ∣ q.den := fun h =>
    hd ((ZMod.natCast_eq_zero_iff q.den p).mpr h)
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hnot]
  simp only [Nat.cast_zero, sub_zero]
  exact_mod_cast (Nat.zero_le (padicValInt p q.num))

theorem rational_zero_or_valuation_pos_of_residue_zero {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hd : (q.den : ZMod p) ≠ 0)
    (hr : (q.num : ZMod p) / (q.den : ZMod p) = 0) :
    q = 0 ∨ 1 ≤ padicValRat p q := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · apply Or.inr
    have hn : (q.num : ZMod p) = 0 := by
      have h := congrArg (fun x : ZMod p => x * (q.den : ZMod p)) hr
      simpa only [div_mul_cancel₀ _ hd, zero_mul] using h
    have hdiv : (p : ℤ) ∣ q.num :=
      (CharP.intCast_eq_zero_iff (ZMod p) p q.num).mp hn
    have hnval : padicValInt p q.num ≠ 0 := by
      intro hz
      rcases padicValInt.eq_zero_iff.mp hz with hp1 | hnum | hnot
      · exact hp.out.ne_one hp1
      · exact hq (Rat.num_eq_zero.mp hnum)
      · exact hnot hdiv
    have hden : ¬p ∣ q.den := fun h =>
      hd ((ZMod.natCast_eq_zero_iff q.den p).mpr h)
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden]
    simp only [Nat.cast_zero, sub_zero]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnval)

theorem rational_div_prime_den_ne_zero_of_residue_zero {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hd : (q.den : ZMod p) ≠ 0)
    (hr : (q.num : ZMod p) / (q.den : ZMod p) = 0) :
    ((q / (p : ℚ)).den : ZMod p) ≠ 0 := by
  rcases rational_zero_or_valuation_pos_of_residue_zero hd hr with hq | hv
  · simp [hq]
  · have hq : q ≠ 0 := by
      intro hz
      rw [hz, padicValRat.zero] at hv
      omega
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [padicValRat.div hq hpq, padicValRat.self hp.out.one_lt]
    omega

theorem rational_den_ne_zero_of_prime_mul_residue_zero {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hd : (((p : ℚ) * q).den : ZMod p) ≠ 0)
    (hr : (((p : ℚ) * q).num : ZMod p) /
      (((p : ℚ) * q).den : ZMod p) = 0) : (q.den : ZMod p) ≠ 0 := by
  have h := rational_div_prime_den_ne_zero_of_residue_zero hd hr
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have heq : (p : ℚ) * q / p = q := by field_simp [hpq]
  rwa [heq] at h

theorem rational_prime_scaled_den_ne_zero_of_prime_sq_residue_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hd : (((p : ℚ) ^ 2 * q).den : ZMod p) ≠ 0)
    (hr : (((p : ℚ) ^ 2 * q).num : ZMod p) /
      (((p : ℚ) ^ 2 * q).den : ZMod p) = 0) :
    (((p : ℚ) * q).den : ZMod p) ≠ 0 := by
  have heq : (p : ℚ) * ((p : ℚ) * q) = (p : ℚ) ^ 2 * q := by ring
  apply rational_den_ne_zero_of_prime_mul_residue_zero
  · rw [heq]
    exact hd
  · rw [heq]
    exact hr





theorem zmod_val_rat_reduction {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    (((x.val : ℚ).den : ZMod p) ≠ 0) ∧
      palindromicRatResidue p (x.val : ℚ) = x := by
  constructor
  · rw [Rat.den_natCast, Nat.cast_one]
    exact one_ne_zero
  · simp only [palindromicRatResidue, Rat.num_natCast, Rat.den_natCast,
      Nat.cast_one, div_one, Int.cast_natCast]
    simp

theorem rational_remainder_den_ne_zero_of_scaled_residue_eq
    {p : ℕ} [hp : Fact p.Prime] {q s : ℚ}
    (hq : (((p : ℚ) * q).den : ZMod p) ≠ 0)
    (hs : (s.den : ZMod p) ≠ 0)
    (he : palindromicRatResidue p ((p : ℚ) * q) = palindromicRatResidue p s) :
    ((q - s / (p : ℚ)).den : ZMod p) ≠ 0 := by
  have hsub := rational_residue_sub hq hs
  have hzero : (((p : ℚ) * q - s).num : ZMod p) /
      (((p : ℚ) * q - s).den : ZMod p) = 0 := by
    change palindromicRatResidue p ((p : ℚ) * q - s) = 0
    rw [palindromicRatResidue_sub hq hs, he, sub_self]
  have hdiv := rational_div_prime_den_ne_zero_of_residue_zero hsub.1 hzero
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have halgebra : ((p : ℚ) * q - s) / p = q - s / p := by
    field_simp [hpq]
  rwa [halgebra] at hdiv

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrimeExtractedP_eq_zero_of_ge_three {p N r ell v : ℕ}
    (hp : 0 < p) (hN : 0 < N) (hwidth : H N ≤ ell + 2 * p) (hv : 3 ≤ v) :
    oddPrimeExtractedP p N r ell v = 0 := by
  have hP : ∀ i, H N ≤ i →
      ((rowP N r).map (Int.castRingHom (ZMod p))).coeff i = 0 := by
    intro i hi
    simp only [coeff_map, rowP_coeff_eq_zero_of_ge hN hi, map_zero]
  unfold oddPrimeExtractedP
  rw [oddPrimeExtraction_coeff hp _ hP]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro d hd
  have hi' := Finset.mem_range.mp hi
  have hd' := Finset.mem_range.mp hd
  have hmul := Nat.mul_le_mul_right p hv
  have hneq : v * p + ell ≠ i + 1 + d := by omega
  simp only [if_neg hneq]

theorem oddPrimeExtractedD_eq_zero_of_ge_two {p N r ell u : ℕ}
    (hN : 0 < N) (hwidth : H N ≤ ell + 2 * p) (hu : 2 ≤ u) :
    oddPrimeExtractedD p N r ell u = 0 := by
  have hmul := Nat.mul_le_mul_right p hu
  have hindex : H N ≤ u * p + ell := by omega
  unfold oddPrimeExtractedD
  rw [rowD_coeff_eq_zero_of_ge hN hindex, Int.cast_zero]

theorem oddPrimeExtractedP_zero_of_le_A {p N r ell : ℕ}
    (hp : 0 < p) (hN : 0 < N) (hr : r < n N) (hell : ell ≤ A N) :
    oddPrimeExtractedP p N r ell 0 = 0 := by
  have hP : ∀ i, H N ≤ i →
      ((rowP N r).map (Int.castRingHom (ZMod p))).coeff i = 0 := by
    intro i hi
    simp only [coeff_map, rowP_coeff_eq_zero_of_ge hN hi, map_zero]
  unfold oddPrimeExtractedP
  simp only [Nat.zero_mul, zero_add]
  rw [oddPrimeExtraction_coeff hp _ hP]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro d hd
  by_cases heq : ell = i + 1 + d
  · have hicoeff : (rowP N r).coeff i = 0 :=
      rowP_coeff_eq_zero_of_lt hN hr (by omega)
    simp only [if_pos heq, coeff_map, hicoeff, map_zero, zero_mul]
  · simp only [if_neg heq]

theorem oddPrimeExtractedD_zero_of_le_A {p N r ell : ℕ}
    (hN : 0 < N) (hr : r < n N) (hell : ell ≤ A N) :
    oddPrimeExtractedD p N r ell 0 = 0 := by
  unfold oddPrimeExtractedD
  simp only [Nat.zero_mul, zero_add,
    rowD_coeff_eq_zero_of_lt hN hr (show ell < A N + 1 by omega), Int.cast_zero]

def oddPrimeLeadingU (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2 * oddPrimeExtractedP p N r ell 0 - (3 / 2 : ZMod p) * oddPrimeExtractedD p N r ell 0

theorem oddPrimeLeadingU_eq_zero {p N r ell : ℕ} [Fact p.Prime]
    (hp : 0 < p) (hN : 0 < N) (hr : r < n N) (hell : ell ≤ A N) :
    oddPrimeLeadingU p N r ell = 0 := by
  unfold oddPrimeLeadingU
  rw [oddPrimeExtractedP_zero_of_le_A hp hN hr hell,
    oddPrimeExtractedD_zero_of_le_A hN hr hell]
  ring

private theorem paired_moment_values {p : ℕ} [Fact p.Prime] (v : ℕ) (hv : v < 3) :
    palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0) +
      palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1) =
        if v = 0 then 2 else 0 := by
  have hcases : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    norm_num [palindromicRatResidue, momentRatSigned, momentRatNegOne,
      momentRat, boundaryPlus, boundaryMinus, momentScalar, centralCoeff,
      Finset.sum_range_succ]

private theorem paired_zeta_values {p : ℕ} [Fact p.Prime] (u : ℕ) (hu : u < 2) :
    palindromicRatResidue p (zetaRat u 0) + palindromicRatResidue p (zetaRat u 1) =
      if u = 0 then 1 else 0 := by
  have hcases : u = 0 ∨ u = 1 := by omega
  rcases hcases with rfl | rfl <;>
    norm_num [palindromicRatResidue, zetaRat, harmonicRat, Finset.sum_range_succ]

theorem rawEntryRat_pair_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))) =
          oddPrimeLeadingU p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hH2 : 2 ≤ H N := by unfold H; omega
  have hlo := rawEntryRat_general_column_layer (k := 0) (N := N) (r := r)
    hp2 hN hH hell (by simpa using (show ell < H N by omega)) z hz
  have hhi := rawEntryRat_general_column_layer (k := 1) (N := N) (r := r)
    hp2 hN hH hell (by simpa using hhigh) z hz
  simp only [Nat.zero_mul, zero_add] at hlo
  simp only [Nat.one_mul] at hhi
  have hMsum :
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) +
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1)) =
          2 * oddPrimeExtractedP p N r ell 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ v ∈ Finset.range 3,
          (oddPrimeExtractedP p N r ell v *
            palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0) +
           oddPrimeExtractedP p N r ell v *
            palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1)) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (show 3 ≤ H N + 1 by omega))
        intro v hv hnot
        have hv3 : 3 ≤ v := by simpa only [Finset.mem_range, not_lt] using hnot
        rw [oddPrimeExtractedP_eq_zero_of_ge_three hp.out.pos hN hwidth hv3]
        ring
      _ = ∑ v ∈ Finset.range 3,
          oddPrimeExtractedP p N r ell v * (if v = 0 then 2 else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← mul_add, paired_moment_values v (Finset.mem_range.mp hv)]
      _ = _ := by
        norm_num [Finset.sum_range_succ]
        ring
  have hZsum :
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 0)) +
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 1)) = oddPrimeExtractedD p N r ell 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ u ∈ Finset.range 2,
          (oddPrimeExtractedD p N r ell u * palindromicRatResidue p (zetaRat u 0) +
           oddPrimeExtractedD p N r ell u * palindromicRatResidue p (zetaRat u 1)) := by
        symm
        apply Finset.sum_subset (Finset.range_mono hH2)
        intro u hu hnot
        have hu2 : 2 ≤ u := by simpa only [Finset.mem_range, not_lt] using hnot
        rw [oddPrimeExtractedD_eq_zero_of_ge_two hN hwidth hu2]
        ring
      _ = ∑ u ∈ Finset.range 2,
          oddPrimeExtractedD p N r ell u * (if u = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [← mul_add, paired_zeta_values u (Finset.mem_range.mp hu)]
      _ = _ := by simp
  have hres :
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r ell) +
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
          oddPrimeLeadingU p N r ell := by
    rw [hlo.2, hhi.2]
    calc
      _ =
        ((∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
          palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) +
         (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
          palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1))) -
        (3 / 2 : ZMod p) *
        ((∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
          palindromicRatResidue p (zetaRat u 0)) +
         (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
          palindromicRatResidue p (zetaRat u 1))) := by ring
      _ = _ := by rw [hMsum, hZsum]; rfl
  have hadd := rational_residue_add hlo.1 hhi.1
  refine ⟨?_, ?_⟩
  · rw [mul_add]
    exact hadd.1
  · rw [mul_add, palindromicRatResidue_add hlo.1 hhi.1]
    exact hres

theorem rawEntryRat_pair_scaled_reduction {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N) (hellA : ell ≤ A N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))) = 0 := by
  have hpair := rawEntryRat_pair_leading (r := r) hp2 hN hell hwidth hhigh z hz
  exact ⟨hpair.1, hpair.2.trans (oddPrimeLeadingU_eq_zero hp.out.pos hN hr hellA)⟩

end InternalCatalan

end



namespace InternalCatalan

theorem rawEntryRat_pair_prime_scaled_den_ne_zero {p N r ell : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hell : ell < p)
    (hH : H N ≤ ell + 2 * p) (hhigh : p + ell < H N) (hA : ell ≤ A N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))).den :
      ZMod p) ≠ 0 := by
  have hpair := rawEntryRat_pair_scaled_reduction hp2 hN hr hell hH hhigh hA z hz
  apply rational_prime_scaled_den_ne_zero_of_prime_sq_residue_zero hpair.1
  simpa only [palindromicRatResidue] using hpair.2


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.OddPhysicalMinorCounts
namespace OAI


noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddPhysicalIndex (R B C : ℕ) := Fin R ⊕ (Fin B ⊕ Fin C)

def oddPhysicalChoice {R B C : ℕ} (e : ℕ) : oddPhysicalIndex R B C → Type
  | Sum.inl _ => Unit
  | Sum.inr (Sum.inl _) => Unit
  | Sum.inr (Sum.inr _) => Option (Fin e)

instance oddPhysicalChoice_fintype {R B C e : ℕ} (j : oddPhysicalIndex R B C) :
    Fintype (oddPhysicalChoice e j) := by
  rcases j with j | (j | j) <;> dsimp [oddPhysicalChoice] <;> infer_instance

def oddPhysicalExceptionalTag {R B C e : ℕ} (j : oddPhysicalIndex R B C)
    (u : oddPhysicalChoice e j) : Option (Fin e) :=
  match j with
  | Sum.inl _ => none
  | Sum.inr (Sum.inl _) => none
  | Sum.inr (Sum.inr _) => u

def oddPhysicalVector {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) : Fin n → ℚ :=
  match j with
  | Sum.inl r => U r
  | Sum.inr (Sum.inl b) => W b
  | Sum.inr (Sum.inr c) => match u with | none => I c | some l => V l

def oddPhysicalScalar {R B C e : ℕ} (p : ℕ) (a : Fin C → Fin e → ℚ)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) : ℚ :=
  match j with
  | Sum.inl _ => ((p : ℚ) ^ 2)⁻¹
  | Sum.inr (Sum.inl _) => (p : ℚ)⁻¹
  | Sum.inr (Sum.inr c) => match u with | none => 1 | some l => (p : ℚ)⁻¹ * a c l

def oddPhysicalColumn {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (j : oddPhysicalIndex R B C) (r : Fin n) : ℚ :=
  match j with
  | Sum.inl l => ((p : ℚ) ^ 2)⁻¹ * U l r
  | Sum.inr (Sum.inl l) => (p : ℚ)⁻¹ * W l r
  | Sum.inr (Sum.inr l) => I l r + (p : ℚ)⁻¹ * ∑ v, a l v * V v r

theorem oddPhysicalColumn_expansion {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (j : oddPhysicalIndex R B C) (r : Fin n) :
    oddPhysicalColumn p U W I V a j r =
      ∑ u : oddPhysicalChoice e j,
        oddPhysicalVector U W I V j u r * oddPhysicalScalar p a j u := by
  rcases j with j | (j | j)
  · change ((p : ℚ) ^ 2)⁻¹ * U j r = ∑ _u : Unit, U j r * ((p : ℚ) ^ 2)⁻¹
    have hunit : (Finset.univ : Finset Unit) = {()} := by ext u; simp
    rw [hunit, Finset.sum_singleton]
    ring
  · change (p : ℚ)⁻¹ * W j r = ∑ _u : Unit, W j r * (p : ℚ)⁻¹
    have hunit : (Finset.univ : Finset Unit) = {()} := by ext u; simp
    rw [hunit, Finset.sum_singleton]
    ring
  · simp only [oddPhysicalColumn, oddPhysicalChoice, Fintype.sum_option,
      oddPhysicalVector, oddPhysicalScalar, mul_one]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    ring

def oddPhysicalVectorMinor {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) : ℚ :=
  Matrix.det (Matrix.of fun r k => oddPhysicalVector U W I V (c k) (u k) r)

theorem oddPhysicalMinor_expansion {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (c : Fin n → oddPhysicalIndex R B C) :
    Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) =
      ∑ u : ∀ k, oddPhysicalChoice e (c k),
        (∏ k, oddPhysicalScalar p a (c k) (u k)) * oddPhysicalVectorMinor U W I V c u := by
  have hmatrix :
      (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) =
        (Matrix.of fun r k => ∑ u : oddPhysicalChoice e (c k),
          oddPhysicalVector U W I V (c k) u r * oddPhysicalScalar p a (c k) u) := by
    ext r k
    exact oddPhysicalColumn_expansion p U W I V a (c k) r
  rw [hmatrix]
  calc
    _ = ∑ u : ∀ k, oddPhysicalChoice e (c k),
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k, oddPhysicalVector U W I V (c k) (u k) (σ k) *
            oddPhysicalScalar p a (c k) (u k) := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [oddPhysicalVectorMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem oddPhysicalVector_of_exceptional {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) (l : Fin e)
    (h : oddPhysicalExceptionalTag j u = some l) :
    oddPhysicalVector U W I V j u = V l := by
  rcases j with j | (j | j)
  · simp [oddPhysicalExceptionalTag] at h
  · simp [oddPhysicalExceptionalTag] at h
  · change u = some l at h
    subst u
    rfl

theorem oddPhysicalVectorMinor_eq_zero_of_repeat {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) {i j : Fin n} (hij : i ≠ j)
    (l : Fin e) (hi : oddPhysicalExceptionalTag (c i) (u i) = some l)
    (hj : oddPhysicalExceptionalTag (c j) (u j) = some l) :
    oddPhysicalVectorMinor U W I V c u = 0 := by
  apply Matrix.det_zero_of_column_eq hij
  intro r
  change oddPhysicalVector U W I V (c i) (u i) r =
    oddPhysicalVector U W I V (c j) (u j) r
  rw [oddPhysicalVector_of_exceptional U W I V (c i) (u i) l hi,
    oddPhysicalVector_of_exceptional U W I V (c j) (u j) l hj]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

def oddPhysicalIsRetained {R B C : ℕ} : oddPhysicalIndex R B C → Bool
  | Sum.inl _ => true
  | _ => false

def oddPhysicalIsPaired {R B C : ℕ} : oddPhysicalIndex R B C → Bool
  | Sum.inr (Sum.inl _) => true
  | _ => false

def oddPhysicalRetainedSet {n R B C : ℕ} (c : Fin n → oddPhysicalIndex R B C) :=
  Finset.univ.filter (fun k => oddPhysicalIsRetained (c k) = true)

def oddPhysicalPairedSet {n R B C : ℕ} (c : Fin n → oddPhysicalIndex R B C) :=
  Finset.univ.filter (fun k => oddPhysicalIsPaired (c k) = true)

def oddPhysicalExceptionalSet {n R B C e : ℕ} (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) :=
  Finset.univ.filter (fun k => (oddPhysicalExceptionalTag (c k) (u k)).isSome = true)

def oddPhysicalLoss {R B C e : ℕ} (j : oddPhysicalIndex R B C)
    (u : oddPhysicalChoice e j) : ℕ :=
  (if oddPhysicalIsRetained j = true then 2 else 0) +
    (if oddPhysicalIsPaired j = true then 1 else 0) +
      (if (oddPhysicalExceptionalTag j u).isSome = true then 1 else 0)

theorem oddPhysical_one_tag {R B C e : ℕ} (j : oddPhysicalIndex R B C)
    (u : oddPhysicalChoice e j) :
    (if oddPhysicalIsRetained j = true then 1 else 0) +
      (if oddPhysicalIsPaired j = true then 1 else 0) +
        (if (oddPhysicalExceptionalTag j u).isSome = true then 1 else 0) ≤ (1 : ℕ) := by
  rcases j with j | (j | j)
  · simp [oddPhysicalIsRetained, oddPhysicalIsPaired, oddPhysicalExceptionalTag]
  · simp [oddPhysicalIsRetained, oddPhysicalIsPaired, oddPhysicalExceptionalTag]
  · cases u <;> simp [oddPhysicalIsRetained, oddPhysicalIsPaired, oddPhysicalExceptionalTag]

theorem oddPhysical_counts_le_size {n R B C e : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (u : ∀ k, oddPhysicalChoice e (c k)) :
    (oddPhysicalRetainedSet c).card + (oddPhysicalPairedSet c).card +
      (oddPhysicalExceptionalSet c u).card ≤ n := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun k _ => oddPhysical_one_tag (c k) (u k))
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Nat.cast_id,
    oddPhysicalRetainedSet, oddPhysicalPairedSet, oddPhysicalExceptionalSet] using hs

theorem oddPhysical_retained_count_le {n R B C : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c) :
    (oddPhysicalRetainedSet c).card ≤ R := by
  have h := Finset.card_le_card_of_injOn c
    (s := oddPhysicalRetainedSet c)
    (t := Finset.univ.image (Sum.inl : Fin R → oddPhysicalIndex R B C))
    (by
      intro k hk
      have hk' : oddPhysicalIsRetained (c k) = true := (Finset.mem_filter.mp hk).2
      cases hck : c k with
      | inl r => exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      | inr j => simp [hck, oddPhysicalIsRetained] at hk')
    (fun i _ j _ h => hc h)
  simpa only [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_univ, Fintype.card_fin] using h

theorem oddPhysical_paired_count_le {n R B C : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c) :
    (oddPhysicalPairedSet c).card ≤ B := by
  let f : Fin B → oddPhysicalIndex R B C := fun b => Sum.inr (Sum.inl b)
  have hf : Function.Injective f := by intro i j h; exact Sum.inl.inj (Sum.inr.inj h)
  have h := Finset.card_le_card_of_injOn c
    (s := oddPhysicalPairedSet c) (t := Finset.univ.image f)
    (by
      intro k hk
      have hk' : oddPhysicalIsPaired (c k) = true := (Finset.mem_filter.mp hk).2
      rcases hck : c k with j | (j | j)
      · simp [hck, oddPhysicalIsPaired] at hk'
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      · simp [hck, oddPhysicalIsPaired] at hk')
    (fun i _ j _ h => hc h)
  simpa only [Finset.card_image_of_injective _ hf,
    Finset.card_univ, Fintype.card_fin] using h

theorem oddPhysical_exceptional_count_le {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C) (u : ∀ k, oddPhysicalChoice e (c k))
    (hdet : oddPhysicalVectorMinor U W I V c u ≠ 0) :
    (oddPhysicalExceptionalSet c u).card ≤ e := by
  let f : Fin n → Option (Fin e) := fun k => oddPhysicalExceptionalTag (c k) (u k)
  have h := Finset.card_le_card_of_injOn f
    (s := oddPhysicalExceptionalSet c u)
    (t := Finset.univ.image (some : Fin e → Option (Fin e)))
    (by
      intro k hk
      have hk' : (f k).isSome = true := (Finset.mem_filter.mp hk).2
      cases hfk : f k with
      | none => simp [hfk] at hk'
      | some l => exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)
    (by
      intro i hi j hj hij
      have hi' : (f i).isSome = true := (Finset.mem_filter.mp hi).2
      cases hfi : f i with
      | none => simp [hfi] at hi'
      | some l =>
        by_contra hne
        exact hdet (oddPhysicalVectorMinor_eq_zero_of_repeat U W I V c u
          hne l hfi (hij.symm.trans hfi)))
  simpa only [Finset.card_image_of_injective _ (Option.some_injective (Fin e)),
    Finset.card_univ, Fintype.card_fin] using h

theorem oddPhysical_total_loss_eq {n R B C e : ℕ}
    (c : Fin n → oddPhysicalIndex R B C) (u : ∀ k, oddPhysicalChoice e (c k)) :
    ∑ k, oddPhysicalLoss (c k) (u k) =
      2 * (oddPhysicalRetainedSet c).card + (oddPhysicalPairedSet c).card +
        (oddPhysicalExceptionalSet c u).card := by
  simp only [oddPhysicalLoss, Finset.sum_add_distrib,
    oddPhysicalRetainedSet, oddPhysicalPairedSet, oddPhysicalExceptionalSet]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  simp
  omega

theorem oddPhysical_total_loss_le_min {n R B C e : ℕ}
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c)
    (u : ∀ k, oddPhysicalChoice e (c k))
    (hdet : oddPhysicalVectorMinor U W I V c u ≠ 0) :
    ∑ k, oddPhysicalLoss (c k) (u k) ≤ min (2 * n) (min (n + R) (2 * R + B + e)) := by
  rw [oddPhysical_total_loss_eq]
  have hs := oddPhysical_counts_le_size c u
  have hr := oddPhysical_retained_count_le c hc
  have hb := oddPhysical_paired_count_le c hc
  have he := oddPhysical_exceptional_count_le U W I V c u hdet
  omega

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.RationalProductFormula
namespace OAI


namespace InternalCatalan

open scoped BigOperators

def rationalPrimeSupport (q : ℚ) : Finset ℕ :=
  q.num.natAbs.primeFactors ∪ q.den.primeFactors

theorem prime_of_mem_rationalPrimeSupport (q : ℚ) {p : ℕ}
    (hp : p ∈ rationalPrimeSupport q) : p.Prime := by
  rcases Finset.mem_union.mp hp with hn | hd
  · exact Nat.prime_of_mem_primeFactors hn
  · exact Nat.prime_of_mem_primeFactors hd

theorem valuation_zero_outside_rationalPrimeSupport (q : ℚ) {p : ℕ}
    (hp : p.Prime) (hs : p ∉ rationalPrimeSupport q) : padicValRat p q = 0 := by
  have hn : p ∉ q.num.natAbs.factorization.support := by
    intro hn
    apply hs
    exact Finset.mem_union_left _ hn
  have hd : p ∉ q.den.factorization.support := by
    intro hd
    apply hs
    exact Finset.mem_union_right _ hd
  have hn0 := Finsupp.notMem_support_iff.mp hn
  have hd0 := Finsupp.notMem_support_iff.mp hd
  rw [Nat.factorization_def _ hp] at hn0
  rw [Nat.factorization_def _ hp] at hd0
  simp only [padicValRat, padicValInt, hn0, hd0, Nat.cast_zero, sub_self]

theorem log_nat_eq_sum_factorization_on (n : ℕ) (s : Finset ℕ)
    (hs : n.primeFactors ⊆ s) :
    Real.log (n : ℝ) = ∑ p ∈ s, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset hs
  intro p _ hp
  have hzero : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
  simp only [hzero, Nat.cast_zero, zero_mul]

theorem positive_rational_cast_eq_natAbs_num_div_den (q : ℚ) (hq : 0 < q) :
    (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
  have hn : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hnreal : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    calc
      (q.num.natAbs : ℝ) = ((q.num.natAbs : ℤ) : ℝ) := (Int.cast_natCast _).symm
      _ = (q.num : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hn
  rw [hnreal, Rat.cast_def]

theorem log_positive_rational_eq_sum_valuations (q : ℚ) (hq : 0 < q) :
    Real.log (q : ℝ) =
      ∑ p ∈ rationalPrimeSupport q, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  have hn : q.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq.ne')
  have hden : q.den ≠ 0 := q.den_ne_zero
  have hns : q.num.natAbs.primeFactors ⊆ rationalPrimeSupport q :=
    Finset.subset_union_left
  have hds : q.den.primeFactors ⊆ rationalPrimeSupport q :=
    Finset.subset_union_right
  rw [positive_rational_cast_eq_natAbs_num_div_den q hq,
    Real.log_div (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hden),
    log_nat_eq_sum_factorization_on _ _ hns,
    log_nat_eq_sum_factorization_on _ _ hds, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := prime_of_mem_rationalPrimeSupport q hp
  rw [Nat.factorization_def _ hprime, Nat.factorization_def _ hprime]
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast, sub_mul]


@[simp] theorem rationalPrimeSupport_neg (q : ℚ) :
    rationalPrimeSupport (-q) = rationalPrimeSupport q := by
  simp [rationalPrimeSupport]

theorem log_abs_rational_eq_sum_valuations (q : ℚ) (hq : q ≠ 0) :
    Real.log |(q : ℝ)| =
      ∑ p ∈ rationalPrimeSupport q, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  by_cases hpos : 0 < q
  · have hreal : 0 < (q : ℝ) := by exact_mod_cast hpos
    rw [abs_of_pos hreal]
    exact log_positive_rational_eq_sum_valuations q hpos
  · have hneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hq
    have hreal : (q : ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hreal]
    have hformula := log_positive_rational_eq_sum_valuations (-q) (neg_pos.mpr hneg)
    simpa only [Rat.cast_neg, rationalPrimeSupport_neg, padicValRat.neg] using hformula

theorem log_abs_rational_eq_sum_valuations_on (q : ℚ) (hq : q ≠ 0)
    (s : Finset ℕ) (hs : rationalPrimeSupport q ⊆ s)
    (hprime : ∀ p ∈ s, p.Prime) :
    Real.log |(q : ℝ)| = ∑ p ∈ s, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  rw [log_abs_rational_eq_sum_valuations q hq]
  apply Finset.sum_subset hs
  intro p hp hps
  rw [valuation_zero_outside_rationalPrimeSupport q (hprime p hp) hps]
  simp only [Int.cast_zero, zero_mul]


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.SmallOddPrimePartition
namespace OAI


namespace InternalCatalan

theorem parityBoundarySum_prime_log_lower {p : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (u H : ℕ) (hu : u ≤ H) (B : ℤ) (hB : B ≤ 0)
    (hf : ∀ z, 0 < z → z ≤ H → B ≤ padicValRat p (f z)) :
    B ≤ padicValRat p (parityBoundarySum f u) := by
  unfold parityBoundarySum
  apply prime_sum_valuation_lower _ _ B hB
  intro z hz
  split_ifs with he
  · exact hf z he.1 (by have := Finset.mem_range.mp hz; omega)
  · simpa using hB

theorem boundaryPlus_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (d H : ℕ) (hd : d ≤ H) :
    -5 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryPlus d) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  cases d with
  | zero => simp
  | succ u =>
    rw [boundaryPlus_explicit]
    have hu : u ≤ H := by omega
    have hsum := parityBoundarySum_prime_log_lower boundaryPlusWeight u H hu
      (-3 * (Nat.log p H : ℤ)) (by omega)
      (fun z hz0 hz => boundaryPlusWeight_odd_prime_log_lower hp2 z H hz0 hz)
    have hm := prime_mul_valuation_lower (boundaryFactor u)
      (parityBoundarySum boundaryPlusWeight u)
      (-2 * (Nat.log p H : ℤ)) (-3 * (Nat.log p H : ℤ)) (by omega)
      (boundaryFactor_odd_prime_log_bounds hp2 u H hu).1 hsum
    convert hm using 1
    ring

theorem boundaryMinus_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (d H : ℕ) (hd : d ≤ H) :
    -6 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryMinus d) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  rw [boundaryMinus_explicit]
  have hsum := parityBoundarySum_prime_log_lower boundaryMinusWeight d H hd
    (-4 * (Nat.log p H : ℤ)) (by omega)
    (fun z hz0 hz => boundaryMinusWeight_odd_prime_log_lower hp2 z H hz0 hz)
  have hm := prime_mul_valuation_lower (boundaryFactor d)
    (parityBoundarySum boundaryMinusWeight d)
    (-2 * (Nat.log p H : ℤ)) (-4 * (Nat.log p H : ℤ)) (by omega)
    (boundaryFactor_odd_prime_log_bounds hp2 d H hd).1 hsum
  convert hm using 1
  ring

theorem momentRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i j H : ℕ) (hi : i < H) (hj : j < H) :
    -6 * (Nat.log p H : ℤ) ≤ padicValRat p (momentRat i j) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji]
    apply prime_sub_valuation_lower _ _ _ (by omega)
    · exact boundaryMinus_odd_prime_log_lower hp2 (i - j) H (by omega)
    · apply prime_sum_valuation_lower _ _ _ (by omega)
      intro k hk
      have hk' : k < j := Finset.mem_range.mp hk
      have hm := prime_div_nat_valuation_lower (p := p)
        (momentScalar (i - j + k)) (k + 1) H (-2 * (Nat.log p H : ℤ))
        (by omega) (by omega) (momentScalar_odd_prime_log_lower hp2 _ H (by omega))
      omega
  · rw [momentRat_of_lt (by omega : i < j)]
    apply prime_sub_valuation_lower _ _ _ (by omega)
    · have hm := boundaryPlus_odd_prime_log_lower (p := p) hp2 (j - i) H (by omega)
      omega
    · apply prime_sum_valuation_lower _ _ _ (by omega)
      intro k hk
      have hk' : k < i := Finset.mem_range.mp hk
      have hm := prime_div_nat_valuation_lower (p := p)
        (momentScalar k) (j - i + k + 1) H (-2 * (Nat.log p H : ℤ))
        (by omega) (by omega) (momentScalar_odd_prime_log_lower hp2 k H (by omega))
      omega





open scoped BigOperators

theorem int_prime_valuation_nonneg (p : ℕ) (m : ℤ) :
    0 ≤ padicValRat p (m : ℚ) := by
  rw [padicValRat.of_int]
  unfold padicValInt
  positivity

theorem rational_prime_valuation_den_lower (p : ℕ) (z : ℚ) :
    -(padicValNat p z.den : ℤ) ≤ padicValRat p z := by
  rw [padicValRat_def]
  have : 0 ≤ (padicValInt p z.num : ℤ) := by unfold padicValInt; positivity
  omega

theorem centralCoeffKernel_odd_prime_nonneg {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (d : ℤ) : 0 ≤ padicValRat p (centralCoeffKernel d) := by
  unfold centralCoeffKernel
  split_ifs
  · exact centralCoeff_odd_prime_nonneg p _ hp.out hp2
  · simp

private theorem prime_add_lower {p : ℕ} [Fact p.Prime] (a b : ℚ) (B : ℤ)
    (hB : B ≤ 0) (ha : B ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    B ≤ padicValRat p (a + b) := by
  simpa using prime_sub_valuation_lower a (-b) B hB ha (by simpa using hb)

theorem rawEntryRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N r j : ℕ) (hj : j < H N) :
    -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ) ≤
      padicValRat p (rawEntryRat z N r j) := by
  let B : ℤ := -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ)
  have hl : 0 ≤ (Nat.log p (H N) : ℤ) := by positivity
  have hd : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
  have hB : B ≤ 0 := by dsimp [B]; omega
  have hfour : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow,
      two_odd_prime_valuation hp2]
    norm_num
  have hfourz : -(padicValNat p z.den : ℤ) ≤ padicValRat p (4 * z) := by
    simpa using prime_mul_valuation_lower (4 : ℚ) z 0
      (-(padicValNat p z.den : ℤ)) (by omega) (by rw [hfour])
      (rational_prime_valuation_den_lower p z)
  have h32 : 0 ≤ padicValRat p (3 / 2 : ℚ) := by
    rw [padicValRat.div (by norm_num) (by norm_num), two_odd_prime_valuation hp2]
    simpa using int_prime_valuation_nonneg p 3
  unfold rawEntryRat
  apply prime_sub_valuation_lower _ _ B hB
  · apply prime_sum_valuation_lower _ _ B hB
    intro i hi
    have hi' : i < H N := Finset.mem_range.mp hi
    have hm := momentRat_odd_prime_log_lower hp2 i j (H N) hi' hj
    have he := prime_mul_valuation_lower (4 * z)
      (centralCoeffKernel ((i : ℤ) - j)) (-(padicValNat p z.den : ℤ)) 0
      (by omega) hfourz (centralCoeffKernel_odd_prime_nonneg hp2 _)
    have hs : B ≤ padicValRat p
        (momentRat i j + 4 * z * centralCoeffKernel ((i : ℤ) - j)) :=
      prime_add_lower _ _ B hB (by dsimp [B]; omega) (by dsimp [B]; omega)
    simpa using prime_mul_valuation_lower ((rowP N r).coeff i : ℚ) _ 0 B
      (by simpa using hB) (int_prime_valuation_nonneg p _) hs
  · have hs : B ≤ padicValRat p
        (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j) := by
      apply prime_sum_valuation_lower _ _ B hB
      intro i hi
      have hz := zetaRat_prime_log_lower (p := p) (H N) i j (Finset.mem_range.mp hi) hj
      have hzB : B ≤ padicValRat p (zetaRat i j) := by dsimp [B]; omega
      simpa using prime_mul_valuation_lower ((rowD N r).coeff i : ℚ) _ 0 B
        (by simpa using hB) (int_prime_valuation_nonneg p _) hzB
    simpa using prime_mul_valuation_lower (3 / 2 : ℚ) _ 0 B
      (by simpa using hB) h32 hs

theorem filteredEntryRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N r k : ℕ) (hk : k < n N) :
    -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ) ≤
      padicValRat p (filteredEntryRat z N r k) := by
  let B : ℤ := -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ)
  have hB : B ≤ 0 := by
    have : 0 ≤ (Nat.log p (H N) : ℤ) := by positivity
    have : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
    dsimp [B]
    omega
  unfold filteredEntryRat
  apply prime_sum_valuation_lower _ _ B hB
  intro v hv
  have hv' : v ≤ q N := by have := Finset.mem_range.mp hv; omega
  have hj : b N + k + v < H N := by
    have h := rawColumn_lt_L hk hv'
    unfold L H at *
    omega
  have hfilter : 0 ≤ padicValRat p (filterCoeffRat N v) := by
    simpa [filterCoeffRat] using
      int_prime_valuation_nonneg p ((-1 : ℤ) ^ v * ((q N).choose v : ℤ))
  simpa using prime_mul_valuation_lower (filterCoeffRat N v) _ 0 B
    (by simpa using hB) hfilter (rawEntryRat_odd_prime_log_lower hp2 z N r _ hj)

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem prime_prod_valuation_lower {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (B : ℤ) (hB : B ≤ 0)
    (hf : ∀ x ∈ s, B ≤ padicValRat p (f x)) :
    (s.card : ℤ) * B ≤ padicValRat p (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcard : (s.card : ℤ) * B ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hB
    have hm := prime_mul_valuation_lower (f a) (∏ x ∈ s, f x) B
      ((s.card : ℤ) * B) (by omega) (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))
    convert hm using 1
    simp [Finset.card_insert_of_notMem ha, add_mul]
    ring

theorem prime_det_valuation_lower {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (B : ℤ) (hB : B ≤ 0)
    (hM : ∀ i j, B ≤ padicValRat p (M i j)) :
    (Fintype.card ι : ℤ) * B ≤ padicValRat p (Matrix.det M) := by
  classical
  have hcard : (Fintype.card ι : ℤ) * B ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hB
  rw [Matrix.det_apply']
  apply prime_sum_valuation_lower _ _ _ hcard
  intro σ hσ
  have hprod : (Fintype.card ι : ℤ) * B ≤ padicValRat p (∏ j, M (σ j) j) := by
    simpa using prime_prod_valuation_lower Finset.univ (fun j => M (σ j) j)
      B hB (fun j hj => hM (σ j) j)
  simpa using prime_mul_valuation_lower ((Equiv.Perm.sign σ : ℤ) : ℚ)
    (∏ j, M (σ j) j) 0 ((Fintype.card ι : ℤ) * B) (by simpa using hcard)
    (int_prime_valuation_nonneg p _) hprod

theorem determinantRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N : ℕ) :
    (n N : ℤ) * (-6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ)) ≤
      padicValRat p (determinantRat z N) := by
  have hB : -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ) ≤ 0 := by
    have : 0 ≤ (Nat.log p (H N) : ℤ) := by positivity
    have : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
    omega
  simpa only [determinantRat, Fintype.card_fin] using
    prime_det_valuation_lower (fun r k : Fin (n N) => filteredEntryRat z N r.val k.val)
      _ hB (fun r k => filteredEntryRat_odd_prime_log_lower hp2 z N r.val k.val k.isLt)

end InternalCatalan



namespace InternalCatalan

theorem nat_log_mul_log_prime_le {p H : ℕ} (hp : p.Prime) (hH : 0 < H) :
    (Nat.log p H : ℝ) * Real.log p ≤ Real.log H := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpow : (p : ℝ) ^ Nat.log p H ≤ (H : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p (Nat.ne_of_gt hH)
  have h := Real.log_le_log (pow_pos hpR _) hpow
  simpa only [Real.log_pow] using h

theorem nat_valuation_mul_log_prime_le {p H : ℕ} (hp : p.Prime) (hH : 0 < H) :
    (padicValNat p H : ℝ) * Real.log p ≤ Real.log H := by
  have : Fact p.Prime := ⟨hp⟩
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  calc
    _ ≤ (Nat.log p H : ℝ) * Real.log p :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast padicValNat_le_nat_log (p := p) H)
        (Real.log_nonneg hpR)
    _ ≤ Real.log H := nat_log_mul_log_prime_le hp hH

theorem determinantRat_odd_prime_log_weighted_lower {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) {N : ℕ} (hN : 0 < N) :
    -(n N : ℝ) * (6 * Real.log (H N) + Real.log z.den) ≤
      (padicValRat p (determinantRat z N) : ℝ) * Real.log p := by
  have hH : 0 < H N := by unfold H; omega
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hlogp := Real.log_nonneg hpR
  have hn : 0 ≤ (n N : ℝ) := by positivity
  have hnat := nat_log_mul_log_prime_le hp.out hH
  have hden := nat_valuation_mul_log_prime_le hp.out z.pos
  have hv : (n N : ℝ) *
      (-6 * (Nat.log p (H N) : ℝ) - (padicValNat p z.den : ℝ)) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
    have hcast : (((n N : ℤ) * (-6 * (Nat.log p (H N) : ℤ) -
        (padicValNat p z.den : ℤ)) : ℤ) : ℝ) ≤
        (padicValRat p (determinantRat z N) : ℝ) :=
      Int.cast_le.mpr (determinantRat_odd_prime_log_lower hp2 z N)
    norm_num only [Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_ofNat,
      Int.cast_natCast] at hcast
    exact hcast
  have hscaled := mul_le_mul_of_nonneg_right hv hlogp
  have herr : (n N : ℝ) *
      (6 * ((Nat.log p (H N) : ℝ) * Real.log p) +
        (padicValNat p z.den : ℝ) * Real.log p) ≤
      (n N : ℝ) * (6 * Real.log (H N) + Real.log z.den) :=
    mul_le_mul_of_nonneg_left (by linarith) hn
  nlinarith

theorem determinantRat_odd_prime_above_degrees_integral {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N : ℕ) (hH : H N < p) (hz : z.den < p) :
    0 ≤ padicValRat p (determinantRat z N) := by
  have hlog : Nat.log p (H N) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hH)
  have hdiv : ¬p ∣ z.den := Nat.not_dvd_of_pos_of_lt z.pos hz
  have hden : padicValNat p z.den = 0 := padicValNat.eq_zero_of_not_dvd hdiv
  simpa [hlog, hden] using determinantRat_odd_prime_log_lower hp2 z N

end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem log_abs_determinantRat_truncated_lower (z : ℚ) {N : ℕ}
    (hN : 0 < N) (hz : z.den ≤ H N) (hdet : determinantRat z N ≠ 0) :
    (padicValRat 2 (determinantRat z N) : ℝ) * Real.log 2 +
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter (fun p => p.Prime ∧ p ≠ 2),
        (padicValRat p (determinantRat z N) : ℝ) * Real.log p) ≤
      Real.log |(determinantRat z N : ℝ)| := by
  classical
  have hH : 0 < H N := Nat.mul_pos (by decide) hN
  let s := (Finset.Ioc 0 (H N)).filter (fun p => p.Prime ∧ p ≠ 2)
  let t := insert 2 s
  let u := rationalPrimeSupport (determinantRat z N) ∪ t
  have htprime : ∀ p ∈ t, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · simpa [h] using Nat.prime_two
    · exact (Finset.mem_filter.mp h).2.1
  have huprime : ∀ p ∈ u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact prime_of_mem_rationalPrimeSupport _ h
    · exact htprime p h
  have hformula := log_abs_rational_eq_sum_valuations_on (determinantRat z N)
    hdet u Finset.subset_union_left huprime
  have hsum : (∑ p ∈ t, (padicValRat p (determinantRat z N) : ℝ) * Real.log p) ≤
      ∑ p ∈ u, (padicValRat p (determinantRat z N) : ℝ) * Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    intro p hpu hpt
    have hp := huprime p hpu
    have hp2 : p ≠ 2 := by
      intro h
      apply hpt
      simp [t, h]
    have hpH : H N < p := by
      by_contra h
      apply hpt
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hp.pos, by omega⟩, hp, hp2⟩)
    have : Fact p.Prime := ⟨hp⟩
    have hv := determinantRat_odd_prime_above_degrees_integral hp2 z N hpH
      (lt_of_le_of_lt hz hpH)
    exact mul_nonneg (by exact_mod_cast hv)
      (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (hH.trans hpH)))
  have htwo : 2 ∉ s := by simp [s]
  rw [← hformula] at hsum
  simpa only [t, Finset.sum_insert htwo, s, Nat.cast_ofNat] using hsum

end InternalCatalan

end



namespace InternalCatalan

theorem prime_ne_H {p N : ℕ} (hp : p.Prime) (hN : 0 < N) : p ≠ H N := by
  intro heq
  have hp65 : 65 ≤ p := by
    rw [heq]
    simpa [H] using Nat.mul_le_mul_left 65 (Nat.succ_le_of_lt hN)
  have hdiv : 5 ∣ p := by
    rw [heq]
    exact ⟨13 * N, by unfold H; omega⟩
  have hfive := hp.eq_one_or_self_of_dvd 5 hdiv
  omega

theorem determinantRat_above_degrees_local_integral {p N : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hH : H N ≤ p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    0 ≤ padicValRat p (determinantRat z N) := by
  have hlt : H N < p := lt_of_le_of_ne hH (Ne.symm (prime_ne_H hp.out hN))
  have hlog : Nat.log p (H N) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hlt)
  have hdiv : ¬ p ∣ z.den := fun hd => hz ((ZMod.natCast_eq_zero_iff z.den p).mpr hd)
  have hden : padicValNat p z.den = 0 := padicValNat.eq_zero_of_not_dvd hdiv
  simpa [hlog, hden] using determinantRat_odd_prime_log_lower hp2 z N

theorem determinantRat_odd_prime_loss_above_degrees {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hH : H N ≤ p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHR : (65 : ℝ) * N ≤ p := by exact_mod_cast hH
  have hratio : (65 : ℝ) ≤ (p : ℝ) / N := (le_div_iff₀ hNR).mpr hHR
  rw [oddPrimeLoss_of_ge_65 _ hratio, mul_zero]
  exact_mod_cast determinantRat_above_degrees_local_integral hp2 hN hH z hz

end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def smallOddPrimes (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊2 * Real.sqrt (H N)⌋₊).filter (fun p => p.Prime ∧ p ≠ 2)

theorem mem_smallOddPrimes_iff (N p : ℕ) :
    p ∈ smallOddPrimes N ↔ p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * Real.sqrt (H N) := by
  have hcut : 0 ≤ 2 * Real.sqrt (H N) := by positivity
  simp only [smallOddPrimes, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, hp⟩, hprime, hp2⟩
    exact ⟨hprime, hp2, (Nat.le_floor_iff hcut).mp hp⟩
  · rintro ⟨hprime, hp2, hp⟩
    exact ⟨⟨hprime.pos, (Nat.le_floor_iff hcut).mpr hp⟩, hprime, hp2⟩

theorem smallOddPrimes_card_le (N : ℕ) :
    ((smallOddPrimes N).card : ℝ) ≤ 2 * Real.sqrt (H N) := by
  have hcard : (smallOddPrimes N).card ≤ ⌊2 * Real.sqrt (H N)⌋₊ := by
    calc
      _ ≤ (Finset.Ioc 0 ⌊2 * Real.sqrt (H N)⌋₊).card := by
        unfold smallOddPrimes
        exact Finset.card_filter_le _ _
      _ = _ := by simp
  have hcast : ((smallOddPrimes N).card : ℝ) ≤ (⌊2 * Real.sqrt (H N)⌋₊ : ℝ) := by
    exact_mod_cast hcard
  exact hcast.trans (Nat.floor_le (by positivity))

def smallOddPrimeContribution (z : ℚ) (N : ℕ) : ℝ :=
  ∑ p ∈ smallOddPrimes N,
    (padicValRat p (determinantRat z N) : ℝ) * Real.log p

def smallOddPrimeError (z : ℚ) (N : ℕ) : ℝ :=
  2 * Real.sqrt (H N) * (n N : ℝ) *
    (6 * Real.log (H N) + Real.log z.den)


theorem smallOddPrimeContribution_lower (z : ℚ) {N : ℕ} (hN : 0 < N) :
    -smallOddPrimeError z N ≤ smallOddPrimeContribution z N := by
  let C : ℝ := (n N : ℝ) * (6 * Real.log (H N) + Real.log z.den)
  have hH : (1 : ℝ) ≤ (H N : ℝ) := by
    exact_mod_cast (show 1 ≤ H N by unfold H; omega)
  have hden : (1 : ℝ) ≤ (z.den : ℝ) := by
    exact_mod_cast (show 1 ≤ z.den from z.pos)
  have hlogH := Real.log_nonneg hH
  have hlogden := Real.log_nonneg hden
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : -(((smallOddPrimes N).card : ℝ) * C) ≤ smallOddPrimeContribution z N := by
    calc
      _ = ∑ p ∈ smallOddPrimes N, -C := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        unfold smallOddPrimeContribution
        apply Finset.sum_le_sum
        intro p hp
        rcases (mem_smallOddPrimes_iff N p).mp hp with ⟨hprime, hp2, _⟩
        have : Fact p.Prime := ⟨hprime⟩
        simpa only [C, neg_mul] using determinantRat_odd_prime_log_weighted_lower hp2 z hN
  calc
    -smallOddPrimeError z N = -(2 * Real.sqrt (H N) * C) := by
      dsimp [smallOddPrimeError, C]
      ring
    _ ≤ -(((smallOddPrimes N).card : ℝ) * C) :=
      neg_le_neg (mul_le_mul_of_nonneg_right (smallOddPrimes_card_le N) hC)
    _ ≤ _ := hsum

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem prime_prod_valuation_weighted_lower {p : ℕ} [Fact p.Prime]
    {α : Type*} (s : Finset α) (f : α → ℚ) (w : α → ℕ)
    (hf : ∀ x ∈ s, -(w x : ℤ) ≤ padicValRat p (f x)) :
    -((∑ x ∈ s, w x : ℕ) : ℤ) ≤ padicValRat p (∏ x ∈ s, f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h := prime_mul_valuation_lower (f a) (∏ x ∈ s, f x)
      (-(w a : ℤ)) (-((∑ x ∈ s, w x : ℕ) : ℤ)) (by omega)
      (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))
    simpa only [Nat.cast_add, neg_add] using h

theorem oddPhysicalScalar_valuation_lower {p R B C e : ℕ} [hp : Fact p.Prime]
    (a : Fin C → Fin e → ℚ)
    (ha : ∀ j l, ((a j l).den : ZMod p) ≠ 0)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) :
    -(oddPhysicalLoss j u : ℤ) ≤ padicValRat p (oddPhysicalScalar p a j u) := by
  rcases j with j | (j | j)
  · simp [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
      oddPhysicalIsPaired, oddPhysicalExceptionalTag,
      padicValRat.inv, padicValRat.pow, padicValRat.self hp.out.one_lt]
  · simp [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
      oddPhysicalIsPaired, oddPhysicalExceptionalTag,
      padicValRat.inv, padicValRat.self hp.out.one_lt]
  · cases u with
    | none => simp [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
        oddPhysicalIsPaired, oddPhysicalExceptionalTag]
    | some l =>
      have h := prime_mul_valuation_lower (p : ℚ)⁻¹ (a j l) (-1) 0 (by omega)
        (by simp [padicValRat.inv, padicValRat.self hp.out.one_lt])
        (rational_valuation_nonneg_of_den_ne_zero (ha j l))
      simpa [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
        oddPhysicalIsPaired, oddPhysicalExceptionalTag] using h

theorem oddPhysicalVector_valuation_nonneg {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) (r : Fin n) :
    0 ≤ padicValRat p (oddPhysicalVector U W I V j u r) := by
  apply rational_valuation_nonneg_of_den_ne_zero
  rcases j with j | (j | j)
  · exact hU j r
  · exact hW j r
  · cases u with
    | none => exact hI j r
    | some l => exact hV l r

theorem oddPhysicalVectorMinor_valuation_nonneg {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) :
    0 ≤ padicValRat p (oddPhysicalVectorMinor U W I V c u) := by
  simpa only [mul_zero, oddPhysicalVectorMinor] using prime_det_valuation_lower
    (Matrix.of fun r k => oddPhysicalVector U W I V (c k) (u k) r)
    0 (by omega)
    (fun r k => oddPhysicalVector_valuation_nonneg U W I V hU hW hI hV (c k) (u k) r)

theorem oddPhysicalMinor_valuation_lower {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (ha : ∀ j l, ((a j l).den : ZMod p) ≠ 0)
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c) :
    -((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ) ≤
      padicValRat p (Matrix.det (Matrix.of fun r k =>
        oddPhysicalColumn p U W I V a (c k) r)) := by
  rw [oddPhysicalMinor_expansion]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro u hu
  by_cases hdet : oddPhysicalVectorMinor U W I V c u = 0
  · rw [hdet, mul_zero, padicValRat.zero]
    omega
  have hcount := oddPhysical_total_loss_le_min U W I V c hc u hdet
  have hscal := prime_prod_valuation_weighted_lower Finset.univ
    (fun k => oddPhysicalScalar p a (c k) (u k))
    (fun k => oddPhysicalLoss (c k) (u k))
    (fun k _ => oddPhysicalScalar_valuation_lower a ha (c k) (u k))
  have hvect := oddPhysicalVectorMinor_valuation_nonneg U W I V hU hW hI hV c u
  have hterm := prime_mul_valuation_lower
    (∏ k, oddPhysicalScalar p a (c k) (u k)) (oddPhysicalVectorMinor U W I V c u)
    (-((∑ k, oddPhysicalLoss (c k) (u k) : ℕ) : ℤ)) 0 (by omega) hscal hvect
  have hcint : ((∑ k, oddPhysicalLoss (c k) (u k) : ℕ) : ℤ) ≤
      ((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ) := by exact_mod_cast hcount
  omega

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology

theorem log_nat_div_sqrt_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := (hl.comp hs).const_mul 2
  simp only [mul_zero] at h
  apply h.congr
  intro N
  dsimp only [Function.comp_def]
  rw [Real.log_sqrt (Nat.cast_nonneg N)]
  ring

theorem smallOddPrimeError_div_sq_eq (z : ℚ) {N : ℕ} (hN : 0 < N) :
    smallOddPrimeError z N / (n N : ℝ) ^ 2 =
      (2 * Real.sqrt 65 / 48) *
        ((6 * Real.log 65 + Real.log z.den) * (Real.sqrt (N : ℝ))⁻¹ +
          6 * (Real.log (N : ℝ) / Real.sqrt (N : ℝ))) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold smallOddPrimeError
  simp only [H, n, Nat.cast_mul, Nat.cast_ofNat,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 65)]
  rw [Real.log_mul (by norm_num : (65 : ℝ) ≠ 0) hNr]
  calc
    _ = (2 * Real.sqrt 65 / 48) * (Real.sqrt (N : ℝ) / (N : ℝ)) *
        (6 * (Real.log 65 + Real.log (N : ℝ)) + Real.log z.den) := by
      field_simp [hNr]
    _ = _ := by
      rw [Real.sqrt_div_self]
      ring

theorem smallOddPrimeError_div_sq_tendsto_zero (z : ℚ) :
    Tendsto (fun N : ℕ => smallOddPrimeError z N / (n N : ℝ) ^ 2) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := ((hi.const_mul (6 * Real.log 65 + Real.log z.den)).add
    (log_nat_div_sqrt_tendsto_zero.const_mul 6)).const_mul (2 * Real.sqrt 65 / 48)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (smallOddPrimeError_div_sq_eq z hN).symm

theorem smallOddPrimeContribution_eventually_lower (z : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -ε ≤ smallOddPrimeContribution z N / (n N : ℝ) ^ 2 := by
  have he : ∀ᶠ N : ℕ in atTop, smallOddPrimeError z N / (n N : ℝ) ^ 2 < ε :=
    (tendsto_order.mp (smallOddPrimeError_div_sq_tendsto_zero z)).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  have hsum := div_le_div_of_nonneg_right (smallOddPrimeContribution_lower z hN)
    (sq_nonneg (n N : ℝ))
  have hneg : -ε ≤ -(smallOddPrimeError z N / (n N : ℝ) ^ 2) :=
    neg_le_neg (le_of_lt heN)
  exact hneg.trans (by simpa only [neg_div] using hsum)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem smallOddPrimeCutoff_bounds {N : ℕ} (hN : 0 < N) :
    2 ≤ 2 * Real.sqrt (H N) ∧ 2 * Real.sqrt (H N) ≤ (H N : ℝ) := by
  have hH : (4 : ℝ) ≤ (H N : ℝ) := by
    exact_mod_cast (show 4 ≤ H N by unfold H; omega)
  have hs : 2 ≤ Real.sqrt (H N) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (H N))
  constructor
  · linarith
  · nlinarith [mul_nonneg (Real.sqrt_nonneg (H N)) (sub_nonneg.mpr hs)]

theorem smallOddPrimes_eq_filter_H {N : ℕ} (hN : 0 < N) :
    smallOddPrimes N = (Finset.Ioc 0 (H N)).filter
      (fun p : ℕ => p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * Real.sqrt (H N)) := by
  ext p
  rw [mem_smallOddPrimes_iff]
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hprime, hp2, hp⟩
    have hpH : p ≤ H N := by
      exact_mod_cast hp.trans (smallOddPrimeCutoff_bounds hN).2
    exact ⟨⟨hprime.pos, hpH⟩, hprime, hp2, hp⟩
  · rintro ⟨_, hprime, hp2, hp⟩
    exact ⟨hprime, hp2, hp⟩

theorem oddPrimeContribution_split (z : ℚ) {N : ℕ} (hN : 0 < N) :
    (∑ p ∈ (Finset.Ioc 0 (H N)).filter (fun p => p.Prime ∧ p ≠ 2),
      (padicValRat p (determinantRat z N) : ℝ) * Real.log p) =
    smallOddPrimeContribution z N +
      ∑ p ∈ (Finset.Ioc 0 (H N)).filter
          (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        (padicValRat p (determinantRat z N) : ℝ) * Real.log p := by
  classical
  unfold smallOddPrimeContribution
  rw [smallOddPrimes_eq_filter_H hN]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : p.Prime
  · by_cases hcut : (p : ℝ) ≤ 2 * Real.sqrt (H N)
    · simp [hprime, hcut, not_lt.mpr hcut]
    · have hp2 : p ≠ 2 := by
        intro heq
        subst p
        exact hcut (by simpa only [Nat.cast_ofNat] using (smallOddPrimeCutoff_bounds hN).1)
      simp [hprime, hcut, lt_of_not_ge hcut, hp2]
  · simp [hprime]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.DistinctIndexSums
namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem shifted_range_card_sum_le (s : Finset ℕ) (b : ℕ)
    (hb : ∀ i ∈ s, b ≤ i) :
    (∑ k ∈ Finset.range s.card, (b + k)) ≤ ∑ i ∈ s, i := by
  revert hb
  induction s using Finset.induction_on_max with
  | empty => intro hb; simp
  | insert a s hmax ih =>
    intro hb
    have ha : a ∉ s := by
      intro ha
      exact (Nat.lt_irrefl a) (hmax a ha)
    have hba : b ≤ a := hb a (Finset.mem_insert_self a s)
    have hbs : ∀ i ∈ s, b ≤ i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hsub : s ⊆ Finset.Ico b a := by
      intro i hi
      exact Finset.mem_Ico.mpr ⟨hbs i hi, hmax i hi⟩
    have hcard : s.card ≤ a - b := by
      simpa only [Nat.card_Ico] using Finset.card_le_card hsub
    have hlast : b + s.card ≤ a := by omega
    have hsum := ih hbs
    rw [Finset.card_insert_of_notMem ha, Finset.sum_range_succ, Finset.sum_insert ha]
    omega

private theorem distinct_nat_sum_lower_of_le (s : Finset ℕ) (b : ℕ)
    (hb : ∀ i ∈ s, b ≤ i) :
    s.card * b + s.card * (s.card - 1) / 2 ≤ ∑ i ∈ s, i := by
  have hsum := shifted_range_card_sum_le s b hb
  have he : (∑ k ∈ Finset.range s.card, (b + k)) =
      s.card * b + s.card * (s.card - 1) / 2 := by
    calc
      _ = (∑ _ ∈ Finset.range s.card, b) +
          (∑ k ∈ Finset.range s.card, k) := Finset.sum_add_distrib
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Finset.sum_range_id]
  rwa [he] at hsum


theorem distinct_indices_sum_lower_of_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f (s : Set ι)) (b : ℕ) (hb : ∀ i ∈ s, b ≤ f i) :
    s.card * b + s.card * (s.card - 1) / 2 ≤ ∑ i ∈ s, f i := by
  classical
  have himage : ∀ j ∈ s.image f, b ≤ j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hb i hi
  have h := distinct_nat_sum_lower_of_le (s.image f) b himage
  rw [Finset.card_image_of_injOn hf, Finset.sum_image hf] at h
  exact h

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicSelectorExponent
namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem cast_triangle_product (m : ℕ) :
    ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
  cases m with
  | zero => norm_num
  | succ m =>
    simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem distinct_indices_twice_sum_lower {ι : Type*} (s : Finset ι)
    (f : ι → ℕ) (hf : Set.InjOn f (s : Set ι)) (b : ℕ)
    (hb : ∀ i ∈ s, b ≤ f i) :
    2 * ((s.card : ℝ) * (b : ℝ)) + (s.card : ℝ) * ((s.card : ℝ) - 1) ≤
      2 * ∑ i ∈ s, (f i : ℝ) := by
  have hs : s.card * b + (∑ k ∈ Finset.range s.card, k) ≤ ∑ i ∈ s, f i := by
    rw [Finset.sum_range_id]
    exact distinct_indices_sum_lower_of_le s f hf b hb
  have hg := Finset.sum_range_id_mul_two s.card
  have hn : 2 * (s.card * b) + s.card * (s.card - 1) ≤ 2 * ∑ i ∈ s, f i := by
    omega
  have hr : 2 * ((s.card : ℝ) * (b : ℝ)) + ((s.card * (s.card - 1) : ℕ) : ℝ) ≤
      2 * ∑ i ∈ s, (f i : ℝ) := by
    exact_mod_cast hn
  rwa [cast_triangle_product] at hr

theorem twoAdic_exponent_lower {ι : Type*} (N : ℕ) (E B : Finset ι)
    (u j : ι → ℕ)
    (huE : Set.InjOn u (E : Set ι)) (huB : Set.InjOn u (B : Set ι))
    (hjE : Set.InjOn j (E : Set ι)) (hb : ∀ k ∈ E, b N ≤ j k)
    (hcard : E.card + B.card ≤ n N) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 - 2 * (n N : ℝ) ≤
      ((2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) -
          (H N : ℤ) * (E.card : ℤ) + (∑ k ∈ B, (u k : ℤ)) +
          (Cdegree N : ℤ) * ((n N : ℤ) - (E.card : ℤ) - (B.card : ℤ)) : ℤ) : ℝ) := by
  have hE := distinct_indices_twice_sum_lower E u huE 0 (by simp)
  have hB := distinct_indices_twice_sum_lower B u huB 0 (by simp)
  have hJ := distinct_indices_twice_sum_lower E j hjE (b N) hb
  simp only [Nat.cast_zero, mul_zero, zero_add] at hE hB
  have hm : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hml : (E.card : ℝ) + (B.card : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hcard
  have hq := twoAdicQuadratic_lower N (E.card : ℝ) (B.card : ℝ) hm hl hml
  push_cast
  nlinarith only [hE, hB, hJ, hq, hm, hl, hml]

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem twoAdic_selector_exponent_lower (N : ℕ)
    (τ : Fin (n N) → Fin 3) (u j : Fin (n N) → ℕ)
    (huE : Set.InjOn u {k | τ k = 1})
    (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, b N ≤ j k) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 - 2 * (n N : ℝ) ≤
      ((∑ k : Fin (n N),
        if τ k = 0 then (Cdegree N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
        else (u k : ℤ) : ℤ) : ℝ) := by
  classical
  let E : Finset (Fin (n N)) := Finset.univ.filter (fun k => τ k = 1)
  let B : Finset (Fin (n N)) := Finset.univ.filter (fun k => τ k = 2)
  have huE' : Set.InjOn u (E : Set (Fin (n N))) := by
    intro x hx y hy hxy
    exact huE (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have huB' : Set.InjOn u (B : Set (Fin (n N))) := by
    intro x hx y hy hxy
    exact huB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have hdisj : Disjoint E B := by
    apply Finset.disjoint_left.mpr
    intro k hkE hkB
    have he : τ k = 1 := (Finset.mem_filter.mp hkE).2
    have hb' : τ k = 2 := (Finset.mem_filter.mp hkB).2
    have hn : (1 : Fin 3) = 2 := he.symm.trans hb'
    exact absurd hn (by decide)
  have hcard : E.card + B.card ≤ n N := by
    have hc := Finset.card_le_card (Finset.subset_univ (E ∪ B))
    rw [Finset.card_union_of_disjoint hdisj] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have heach (k : Fin (n N)) :
      (if τ k = 0 then (Cdegree N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
        else (u k : ℤ)) =
      (Cdegree N : ℤ) +
        (if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ) - (Cdegree N : ℤ)
          else 0) +
        (if τ k = 2 then (u k : ℤ) - (Cdegree N : ℤ) else 0) := by
    by_cases h₀ : τ k = 0
    · simp [h₀]
    by_cases h₁ : τ k = 1
    · simp [h₁]
    have h₂ : τ k = 2 := by omega
    simp [h₂]
  have hsumE : (∑ k : Fin (n N),
      if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ) - (Cdegree N : ℤ)
        else 0) =
      ∑ k ∈ E, (2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ) - (Cdegree N : ℤ)) := by
    simp only [E, Finset.sum_filter]
  have hsumB : (∑ k : Fin (n N),
      if τ k = 2 then (u k : ℤ) - (Cdegree N : ℤ) else 0) =
      ∑ k ∈ B, ((u k : ℤ) - (Cdegree N : ℤ)) := by
    simp only [B, Finset.sum_filter]
  have hsumC : (∑ _ : Fin (n N), (Cdegree N : ℤ)) = (n N : ℤ) * (Cdegree N : ℤ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Int.nsmul_eq_mul]
  have hsum : (∑ k : Fin (n N),
      if τ k = 0 then (Cdegree N : ℤ)
      else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
      else (u k : ℤ)) =
      2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) -
        (H N : ℤ) * (E.card : ℤ) + (∑ k ∈ B, (u k : ℤ)) +
        (Cdegree N : ℤ) * ((n N : ℤ) - (E.card : ℤ) - (B.card : ℤ)) := by
    simp_rw [heach]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumE, hsumB, hsumC]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Int.nsmul_eq_mul]
    ring
  rw [hsum]
  exact twoAdic_exponent_lower N E B u j huE' huB'
    (fun _ _ _ _ h => hj h) (fun k _ => hb k) hcard

theorem twoAdic_selector_zpow_le (N : ℕ)
    (τ : Fin (n N) → Fin 3) (u j : Fin (n N) → ℕ)
    (huE : Set.InjOn u {k | τ k = 1})
    (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, b N ≤ j k) :
    (2 : ℝ) ^ (-(∑ k : Fin (n N),
        if τ k = 0 then (Cdegree N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
        else (u k : ℤ))) ≤
      (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  have h := twoAdic_selector_exponent_lower N τ u j huE huB hj hb
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  simp only [Int.cast_neg]
  linarith only [h]

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.ChebyshevContact
namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

def centralCoefficientMap (m : ℤ) (k : ℕ) : ℚ →ₗ[ℚ] ℚ where
  toFun a := a * centralCoeffKernel ((k : ℤ) - m)
  map_add' a b := by ring
  map_smul' a b := by simp only [smul_eq_mul, RingHom.id_apply]; ring

def centralFunctional (m : ℤ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (centralCoefficientMap m)

@[simp] theorem centralFunctional_monomial (m : ℤ) (k : ℕ) (a : ℚ) :
    centralFunctional m (monomial k a) = a * centralCoeffKernel ((k : ℤ) - m) := by
  simp [centralFunctional, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
    centralCoefficientMap]

theorem centralFunctional_C_mul (m : ℤ) (a : ℚ) (P : ℚ[X]) :
    centralFunctional m (Polynomial.C a * P) = a * centralFunctional m P := by
  rw [← smul_eq_C_mul, (centralFunctional m).map_smul]
  rfl

theorem centralFunctional_X_mul (m : ℤ) (P : ℚ[X]) :
    centralFunctional m (X * P) = centralFunctional (m - 1) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
  | monomial k a =>
      rw [X_mul_monomial, centralFunctional_monomial, centralFunctional_monomial]
      congr 2
      push_cast
      omega

theorem centralFunctional_stein (P : ℚ[X]) :
    centralFunctional 0 ((1 - X ^ 2) * derivative P) =
      centralFunctional 0 (X * P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [mul_add, map_add, hP, hQ]
  | monomial k a =>
      cases k with
      | zero =>
          rw [X_mul_monomial]
          simp [centralCoeffKernel]
      | succ k =>
          rw [derivative_monomial_succ, sub_mul, one_mul, X_pow_mul_monomial,
            X_mul_monomial, map_sub]
          simp only [centralFunctional_monomial, sub_zero]
          have hs := centralCoeffKernel_nat_step k
          have hscaled := congrArg (fun z : ℚ => a * z) hs
          push_cast at hscaled ⊢
          norm_num only [add_assoc, Int.reduceAdd] at hscaled ⊢
          nlinarith only [hscaled]

theorem centralFunctional_T_zero (d : ℕ) (hd : 0 < d) :
    centralFunctional 0 (Chebyshev.T ℚ (d : ℤ)) = 0 := by
  have hode := congrArg (centralFunctional 0)
    (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℚ) (d : ℤ))
  have hstein := centralFunctional_stein (derivative (Chebyshev.T ℚ (d : ℤ)))
  have hcast : ((d : ℤ) ^ 2 : ℚ[X]) = Polynomial.C ((d : ℚ) ^ 2) := by
    simp
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hode
  rw [map_sub, hcast, centralFunctional_C_mul] at hode
  have hz : (d : ℚ) ^ 2 * centralFunctional 0 (Chebyshev.T ℚ (d : ℤ)) = 0 := by
    linarith only [hode, hstein]
  have hdn : (d : ℚ) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hz).resolve_left hdn

theorem centralFunctional_two_X_mul (m : ℤ) (P : ℚ[X]) :
    centralFunctional m (2 * X * P) = 2 * centralFunctional (m - 1) P := by
  rw [← Polynomial.C_ofNat, mul_assoc,
    centralFunctional_C_mul, centralFunctional_X_mul]

theorem centralFunctional_T_tail (d : ℕ) : ∀ m : ℕ,
    centralFunctional ((m : ℤ) + 1) (Chebyshev.T ℚ (d : ℤ)) =
      (Chebyshev.U ℚ ((d : ℤ) - 1)).coeff m := by
  induction d using Nat.twoStepInduction with
  | zero =>
      intro m
      rw [Nat.cast_zero, Chebyshev.T_zero, zero_sub, Chebyshev.U_neg_one,
        coeff_zero, ← monomial_zero_one, centralFunctional_monomial,
        centralCoeffKernel_of_neg (by omega : ((0 : ℕ) : ℤ) - ((m : ℤ) + 1) < 0)]
      ring
  | one =>
      intro m
      rw [Nat.cast_one, Chebyshev.T_one, sub_self, Chebyshev.U_zero,
        ← monomial_one_one_eq_X, centralFunctional_monomial]
      cases m with
      | zero => norm_num
      | succ m =>
          rw [centralCoeffKernel_of_neg (by omega :
            ((1 : ℕ) : ℤ) - (((m + 1 : ℕ) : ℤ) + 1) < 0)]
          simp [Polynomial.coeff_one]
  | more d ih0 ih1 =>
      intro m
      have hindex : ((d + 2 : ℕ) : ℤ) - 1 = (d : ℤ) + 1 := by omega
      rw [hindex, Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two,
        map_sub, centralFunctional_two_X_mul, Chebyshev.U_add_one]
      rw [coeff_sub, mul_assoc, coeff_ofNat_mul]
      cases m with
      | zero =>
          norm_num only [Nat.cast_zero, zero_add, sub_self]
          have hvan := centralFunctional_T_zero (d + 1) (by omega)
          simp only [Nat.cast_add, Nat.cast_one] at hvan
          have hprev := ih0 0
          simp only [Nat.cast_zero, zero_add] at hprev
          rw [hvan, hprev, coeff_X_mul_zero]
      | succ m =>
          have hmain := ih1 m
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hmain
          have hprev := ih0 (m + 1)
          simp only [Nat.cast_add, Nat.cast_one] at hprev
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          rw [hmain, hprev, coeff_X_mul]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

private theorem rationalIntCast_apply (z : ℤ) :
    (Int.castRingHom ℚ) z = (z : ℚ) := rfl

theorem centralFunctional_eq_sum_range (m : ℤ) {P : ℚ[X]} {C : ℕ}
    (hP : P.natDegree < C) :
    centralFunctional m P = ∑ u ∈ Finset.range C,
      P.coeff u * centralCoeffKernel ((u : ℤ) - m) := by
  change P.sum (fun u a => a * centralCoeffKernel ((u : ℤ) - m)) = _
  apply Polynomial.sum_eq_of_subset
  · intro u
    simp
  · intro u hu
    apply Finset.mem_range.mpr
    exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hu)) hP

theorem reversedRow_centralFunctional {C j : ℕ} (hj : j < C) (F : ℤ[X])
    (hF : F.natDegree < C) :
    (∑ i ∈ Finset.range C,
      ((reversedRow C F).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      centralFunctional ((C : ℤ) - j) (F.map (Int.castRingHom ℚ)) := by
  have hC : 0 < C := (Nat.zero_le j).trans_lt hj
  have hmap : (F.map (Int.castRingHom ℚ)).natDegree < C :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hF
  rw [centralFunctional_eq_sum_range _ hmap]
  simp only [Polynomial.coeff_map, rationalIntCast_apply]
  calc
    _ = ∑ i ∈ Finset.range C, (F.coeff (C - 1 - i) : ℚ) *
        centralCoeffKernel ((((C - 1 - i : ℕ) : ℤ)) - ((C : ℤ) - j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [reversedRow_coeff, if_pos hi']
      congr 2
      omega
    _ = _ := Finset.sum_range_reflect
      (fun u => (F.coeff u : ℚ) * centralCoeffKernel ((u : ℤ) - ((C : ℤ) - j))) C

theorem reversedChebyshev_contact {C d j : ℕ} (hd : d < C) (hj : j < C) :
    (∑ i ∈ Finset.range C,
      ((reversedRow C (Chebyshev.T ℤ (d : ℤ))).coeff i : ℚ) *
        centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((reversedRow C (Chebyshev.U ℤ ((d : ℤ) - 1))).coeff j : ℚ) := by
  rw [reversedRow_centralFunctional hj _ (by simpa using hd), Chebyshev.map_T]
  have hindex : (C : ℤ) - j = ((C - 1 - j : ℕ) : ℤ) + 1 := by omega
  rw [hindex, centralFunctional_T_tail, reversedRow_coeff, if_pos hj]
  have hmap := congrArg (fun P : ℚ[X] => P.coeff (C - 1 - j))
    (Chebyshev.map_U (Int.castRingHom ℚ) ((d : ℤ) - 1))
  simpa only [Polynomial.coeff_map, rationalIntCast_apply] using hmap.symm

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MomentFilter
namespace OAI

section

open scoped BigOperators Polynomial

noncomputable section

namespace InternalCatalan

open Polynomial

def filteredColumnInt (N k : ℕ) : ℤ[X] :=
  X ^ (b N + k) * (1 - X) ^ q N

def filterCoeff (N j k : ℕ) : ℤ :=
  if b N + k ≤ j then
    (-1 : ℤ) ^ (j - b N - k) * (Nat.choose (q N) (j - b N - k) : ℤ)
  else 0

theorem one_sub_X_pow_expansion (Q : ℕ) :
    ((1 : ℤ[X]) - X) ^ Q =
      ∑ v ∈ Finset.range (Q + 1),
        C ((-1 : ℤ) ^ v * (Nat.choose Q v : ℤ)) * X ^ v := by
  calc
    ((1 : ℤ[X]) - X) ^ Q = (-X + 1) ^ Q := by
      congr 1
      ring
    _ = ∑ v ∈ Finset.range (Q + 1),
        (-X : ℤ[X]) ^ v * 1 ^ (Q - v) * (Nat.choose Q v : ℤ[X]) :=
      add_pow (-X : ℤ[X]) 1 Q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [neg_pow]
      simp only [one_pow, mul_one, map_mul, map_pow, map_neg,
        map_one, C_eq_natCast]
      ring

theorem coeff_one_sub_X_pow (Q j : ℕ) :
    (((1 : ℤ[X]) - X) ^ Q).coeff j =
      (-1 : ℤ) ^ j * (Nat.choose Q j : ℤ) := by
  rw [one_sub_X_pow_expansion, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro v hv hvj
    simp [Ne.symm hvj]
  · intro hj
    have hQj : Q < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hQj]

theorem filteredColumnInt_expansion (N k : ℕ) :
    filteredColumnInt N k =
      ∑ v ∈ Finset.range (q N + 1),
        C ((-1 : ℤ) ^ v * (Nat.choose (q N) v : ℤ)) *
          X ^ (b N + k + v) := by
  rw [filteredColumnInt, one_sub_X_pow_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [pow_add]
  ring

theorem filteredColumnInt_coeff (N j k : ℕ) :
    (filteredColumnInt N k).coeff j = filterCoeff N j k := by
  rw [filteredColumnInt, coeff_X_pow_mul', filterCoeff]
  simp only [coeff_one_sub_X_pow, Nat.sub_add_eq]

theorem filterCoeff_eq_zero_of_lt (N j k : ℕ) (hj : j < b N + k) :
    filterCoeff N j k = 0 := by
  simp [filterCoeff, Nat.not_le.mpr hj]

theorem filterCoeff_eq_zero_of_gt (N j k : ℕ)
    (hj : b N + k + q N < j) : filterCoeff N j k = 0 := by
  have hqj : q N < j - b N - k := by omega
  simp [filterCoeff, Nat.choose_eq_zero_of_lt hqj]

theorem filteredColumnInt_support (N k : ℕ) :
    (filteredColumnInt N k).support ⊆
      Finset.Icc (b N + k) (b N + k + q N) := by
  intro j hj
  rw [Finset.mem_Icc]
  have hcoeff : filterCoeff N j k ≠ 0 := by
    simpa only [mem_support_iff, filteredColumnInt_coeff] using hj
  constructor
  · by_contra h
    exact hcoeff (filterCoeff_eq_zero_of_lt N j k (Nat.lt_of_not_ge h))
  · by_contra h
    exact hcoeff (filterCoeff_eq_zero_of_gt N j k (Nat.lt_of_not_ge h))

theorem filteredColumnInt_support_contactRange (N k : ℕ) (hk : k < n N) :
    (filteredColumnInt N k).support ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  have hj' := filteredColumnInt_support N k hj
  rw [Finset.mem_Icc] at hj'
  rw [Finset.mem_Ico]
  have htop := rawColumn_lt_L (N := N) (k := k) (v := q N) hk (le_refl (q N))
  omega

theorem filteredColumnInt_eq_sum_contactRange (N k : ℕ) (hk : k < n N) :
    filteredColumnInt N k =
      ∑ j ∈ Finset.Ico (b N) (L N),
        C (filterCoeff N j k) * X ^ j := by
  calc
    filteredColumnInt N k =
        (filteredColumnInt N k).sum (fun j c => C c * X ^ j) :=
      (sum_C_mul_X_pow_eq _).symm
    _ = ∑ j ∈ Finset.Ico (b N) (L N),
        C ((filteredColumnInt N k).coeff j) * X ^ j :=
      sum_eq_of_subset (fun j c => C c * X ^ j)
        (by intro j; simp) (filteredColumnInt_support_contactRange N k hk)
    _ = _ := by simp only [filteredColumnInt_coeff]


variable {V : Type*} [AddCommGroup V]

theorem map_filteredColumnInt (F : ℤ[X] →ₗ[ℤ] V) (N k : ℕ) :
    F (filteredColumnInt N k) =
      ∑ v ∈ Finset.range (q N + 1),
        ((-1 : ℤ) ^ v * (Nat.choose (q N) v : ℤ)) •
          F (X ^ (b N + k + v)) := by
  rw [filteredColumnInt_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← smul_eq_C_mul, F.map_smul]

theorem map_filteredColumnInt_contactRange (F : ℤ[X] →ₗ[ℤ] V)
    (N k : ℕ) (hk : k < n N) :
    F (filteredColumnInt N k) =
      ∑ j ∈ Finset.Ico (b N) (L N),
        filterCoeff N j k • F (X ^ j) := by
  rw [filteredColumnInt_eq_sum_contactRange N k hk, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← smul_eq_C_mul, F.map_smul]


end InternalCatalan

end

end


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan












end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.TwoAdicCoefficients
namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

theorem chebyshev_T_coeff_two_pow_dvd (d : ℤ) (u : ℕ) :
    (2 : ℤ) ^ (u - 1) ∣ (Chebyshev.T ℤ d).coeff u := by
  cases u with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_sub_one]
    refine ⟨(Chebyshev.C ℤ d).coeff (k + 1), ?_⟩
    have hc : (Chebyshev.C ℤ d).coeff (k + 1) * (2 : ℤ) ^ (k + 1) =
        2 * (Chebyshev.T ℤ d).coeff (k + 1) := by
      simpa only [← Polynomial.C_ofNat, comp_C_mul_X_coeff, coeff_C_mul] using
        congrArg (fun P : ℤ[X] => P.coeff (k + 1))
          (Chebyshev.C_comp_two_mul_X ℤ d)
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    calc
      2 * (Chebyshev.T ℤ d).coeff (k + 1) =
          (Chebyshev.C ℤ d).coeff (k + 1) * 2 ^ (k + 1) := hc.symm
      _ = 2 * (2 ^ k * (Chebyshev.C ℤ d).coeff (k + 1)) := by ring

theorem chebyshev_U_coeff_two_pow_dvd (d : ℤ) (u : ℕ) :
    (2 : ℤ) ^ u ∣ (Chebyshev.U ℤ d).coeff u := by
  refine ⟨(Chebyshev.S ℤ d).coeff u, ?_⟩
  rw [← Chebyshev.S_comp_two_mul_X ℤ d]
  simp only [← Polynomial.C_ofNat, comp_C_mul_X_coeff]
  ring

theorem reversed_T_coeff_two_pow_dvd (C : ℕ) (d : ℤ) (i : ℕ) :
    (2 : ℤ) ^ (C - 1 - i - 1) ∣
      (reversedRow C (Chebyshev.T ℤ d)).coeff i := by
  rw [reversedRow_coeff]
  split_ifs
  · exact chebyshev_T_coeff_two_pow_dvd d (C - 1 - i)
  · exact dvd_zero _





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicConvolution
namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

theorem two_pow_sub_dvd_coeff_mul (P Q : ℤ[X]) (B i : ℕ)
    (hQ : ∀ j, (2 : ℤ) ^ (B - j) ∣ Q.coeff j) :
    (2 : ℤ) ^ (B - i) ∣ (P * Q).coeff i := by
  rw [coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨a, b⟩ hab
  have hab' : a + b = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hpow : (2 : ℤ) ^ (B - i) ∣ (2 : ℤ) ^ (B - b) :=
    pow_dvd_pow 2 (by omega)
  exact dvd_mul_of_dvd_right (hpow.trans (hQ b)) (P.coeff a)

theorem rowP_coeff_two_pow_dvd (N r i : ℕ) :
    (2 : ℤ) ^ (Cdegree N - 2 - i) ∣ (rowP N r).coeff i := by
  unfold rowP
  apply two_pow_sub_dvd_coeff_mul
  intro j
  have he : Cdegree N - 2 - j = Cdegree N - 1 - j - 1 := by omega
  rw [he]
  exact reversed_T_coeff_two_pow_dvd (Cdegree N) (rowDistance N r : ℤ) j


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicSmoothingDecomposition
namespace OAI


namespace InternalCatalan

theorem centralCoeff_two_adic_eq (l : ℕ) :
    padicValRat 2 (centralCoeff l) =
      (padicValNat 2 ((2 * l).choose l) : ℤ) - 2 * (l : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnum : (((2 * l).choose l : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.centralBinom_pos l))
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have hfour : padicValRat 2 (4 : ℚ) = 2 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow, htwo]
    norm_num
  unfold centralCoeff
  rw [padicValRat.div hnum (pow_ne_zero _ (by norm_num)),
    padicValRat.of_nat, padicValRat.pow, hfour]
  ring

theorem centralCoeff_two_adic_lower (l : ℕ) :
    -2 * (l : ℤ) ≤ padicValRat 2 (centralCoeff l) := by
  rw [centralCoeff_two_adic_eq]
  omega

theorem odd_nat_two_adic_eq_zero (l : ℕ) :
    padicValRat 2 ((2 * l + 1 : ℕ) : ℚ) = 0 := by
  have hn : ¬2 ∣ 2 * l + 1 := by omega
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
  norm_num

theorem momentScalar_even_two_adic_eq (l : ℕ) :
    padicValRat 2 (momentScalar (2 * l)) =
      1 + 2 * (l : ℤ) - (padicValNat 2 ((2 * l).choose l) : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [momentScalar_even,
    padicValRat.div (by norm_num) (mul_ne_zero hodd (centralCoeff_ne_zero l)),
    padicValRat.mul hodd (centralCoeff_ne_zero l), htwo,
    odd_nat_two_adic_eq_zero, centralCoeff_two_adic_eq]
  ring

theorem centralBinom_two_adic_le_log (l : ℕ) :
    padicValNat 2 ((2 * l).choose l) ≤ Nat.log 2 (2 * l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_choose (p := 2) (by omega : l ≤ 2 * l)
    (by omega : Nat.log 2 (2 * l) < Nat.log 2 (2 * l) + 1)]
  calc
    _ ≤ (Finset.Ico 1 (Nat.log 2 (2 * l) + 1)).card := Finset.card_filter_le _ _
    _ = Nat.log 2 (2 * l) := by simp

theorem momentScalar_even_two_adic_lower (l : ℕ) :
    1 + 2 * (l : ℤ) - (Nat.log 2 (2 * l) : ℤ) ≤
      padicValRat 2 (momentScalar (2 * l)) := by
  rw [momentScalar_even_two_adic_eq]
  have hb : (padicValNat 2 ((2 * l).choose l) : ℤ) ≤ (Nat.log 2 (2 * l) : ℤ) := by
    exact_mod_cast centralBinom_two_adic_le_log l
  omega

theorem momentScalar_even_div_two_adic_lower (l j : ℕ) :
    1 + 2 * (l : ℤ) - (Nat.log 2 (2 * l) : ℤ) - (Nat.log 2 (j + 1) : ℤ) ≤
      padicValRat 2 (momentScalar (2 * l) / ((j + 1 : ℕ) : ℚ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : momentScalar (2 * l) ≠ 0 := by
    rw [momentScalar_even]
    exact div_ne_zero (by norm_num)
      (mul_ne_zero (by positivity) (centralCoeff_ne_zero l))
  have hj : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [padicValRat.div hm hj, padicValRat.of_nat]
  have hmval := momentScalar_even_two_adic_lower l
  have hjval : (padicValNat 2 (j + 1) : ℤ) ≤ (Nat.log 2 (j + 1) : ℤ) := by
    exact_mod_cast padicValNat_le_nat_log (p := 2) (j + 1)
  omega





open Filter
open scoped Topology BigOperators

noncomputable def smoothingTerm (i j k : ℕ) : ℚ_[2] :=
  ((momentScalar (i + k) / ((j + k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[2])

theorem smoothingTerm_norm_le_zpow (i j k : ℕ) :
    ‖smoothingTerm i j k‖ ≤
      (2 : ℝ) ^ ((Nat.log 2 (i + k) : ℤ) +
        (Nat.log 2 (j + k + 1) : ℤ) - ((i + k + 1 : ℕ) : ℤ)) := by
  by_cases hm : momentScalar (i + k) = 0
  · simp only [smoothingTerm, hm, zero_div, Rat.cast_zero, norm_zero]
    positivity
  have heven : (i + k) % 2 = 0 := by
    by_contra h
    exact hm (by simp [momentScalar, h])
  have hidx : 2 * ((i + k) / 2) = i + k := by omega
  have hv := momentScalar_even_div_two_adic_lower ((i + k) / 2) (j + k)
  rw [hidx] at hv
  have hq : momentScalar (i + k) / ((j + k + 1 : ℕ) : ℚ) ≠ 0 :=
    div_ne_zero hm (by positivity)
  have hq₂ : smoothingTerm i j k ≠ 0 := by
    unfold smoothingTerm
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hq₂]
  change (2 : ℝ) ^ (-Padic.valuation
    ((momentScalar (i + k) / ((j + k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[2])) ≤ _
  rw [Padic.valuation_ratCast]
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  push_cast at hv ⊢
  have hidxZ : 2 * ((↑((i + k) / 2) : ℤ)) = (i : ℤ) + k := by
    exact_mod_cast hidx
  omega

theorem smoothingTerm_norm_le (i j k : ℕ) :
    ‖smoothingTerm i j k‖ ≤
      ((i + k + 1 : ℕ) : ℝ) * ((j + k + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k := by
  have ha : (2 : ℝ) ^ Nat.log 2 (i + k) ≤ ((i + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_add_one 2 (i + k)
  have hb : (2 : ℝ) ^ Nat.log 2 (j + k + 1) ≤ ((j + k + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_add_one 2 (j + k + 1)
  have hc : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (i + k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hd : 1 / (2 : ℝ) ^ (i + k + 1) ≤ (1 / 2 : ℝ) ^ k := by
    simpa only [one_div_pow] using
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ k) hc
  calc
    ‖smoothingTerm i j k‖ ≤
        (2 : ℝ) ^ ((Nat.log 2 (i + k) : ℤ) +
          (Nat.log 2 (j + k + 1) : ℤ) - ((i + k + 1 : ℕ) : ℤ)) :=
      smoothingTerm_norm_le_zpow i j k
    _ = ((2 : ℝ) ^ Nat.log 2 (i + k) * (2 : ℝ) ^ Nat.log 2 (j + k + 1)) /
        (2 : ℝ) ^ (i + k + 1) := by
      rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp only [zpow_natCast]
    _ ≤ (((i + k + 1 : ℕ) : ℝ) * ((j + k + 2 : ℕ) : ℝ)) /
        (2 : ℝ) ^ (i + k + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul ha hb (by positivity) (by positivity)) (by positivity)
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hd (by positivity)

private theorem smoothing_majorant_summable (i j : ℕ) :
    Summable (fun k : ℕ =>
      ((i + k + 1 : ℕ) : ℝ) * ((j + k + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
  have h₀ := summable_geometric_two
  have h₁ := summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by norm_num)
  have h₂ := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := (1 / 2 : ℝ)) (by norm_num)
  convert (h₂.add (h₁.mul_left ((i : ℝ) + j + 3))).add
    (h₀.mul_left (((i : ℝ) + 1) * ((j : ℝ) + 2))) using 1
  rfl
  ext k
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_one]
  ring

theorem smoothingTerm_summable_norm (i j : ℕ) :
    Summable (fun k : ℕ => ‖smoothingTerm i j k‖) := by
  apply (smoothing_majorant_summable i j).of_norm_bounded
  intro k
  simpa only [norm_norm] using smoothingTerm_norm_le i j k

theorem smoothingTerm_summable (i j : ℕ) : Summable (smoothingTerm i j) :=
  (smoothingTerm_summable_norm i j).of_norm

noncomputable def smoothingMoment (i j : ℕ) : ℚ_[2] := ∑' k, smoothingTerm i j k

theorem smoothingMoment_hasSum (i j : ℕ) :
    HasSum (smoothingTerm i j) (smoothingMoment i j) :=
  (smoothingTerm_summable i j).hasSum

theorem smoothingTerm_tendsto_zero (i j : ℕ) :
    Tendsto (smoothingTerm i j) atTop (𝓝 0) :=
  (smoothingTerm_summable i j).tendsto_atTop_zero

theorem smoothingMoment_step (i j : ℕ) :
    smoothingMoment i j - smoothingMoment (i + 1) (j + 1) =
      ((momentScalar i / ((j + 1 : ℕ) : ℚ) : ℚ) : ℚ_[2]) := by
  have hshift : (fun k : ℕ => smoothingTerm i j (k + 1)) =
      smoothingTerm (i + 1) (j + 1) := by
    funext k
    simp only [smoothingTerm, Nat.add_left_comm, Nat.add_comm]
  have hs := (smoothingTerm_summable i j).tsum_eq_zero_add
  rw [hshift] at hs
  change smoothingMoment i j = smoothingTerm i j 0 + smoothingMoment (i + 1) (j + 1) at hs
  rw [hs, add_sub_cancel_right]
  simp [smoothingTerm]

end InternalCatalan



namespace InternalCatalan

open Filter
open scoped Topology BigOperators

private theorem smoothing_square_le_pow (k : ℕ) : (k + 1) ^ 2 ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases h₀ : k = 0
    · subst k
      norm_num
    by_cases h₁ : k = 1
    · subst k
      norm_num
    have hk : 2 ≤ k := by omega
    calc
      (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ (k + 2) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1 + 2) := by
        simp only [pow_add, pow_one, pow_two]
        ring

theorem smoothingTerm_norm_le_uniform (H i j k : ℕ) (hi : i < H) (hj : j < H) :
    ‖smoothingTerm i j k‖ ≤ 2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
  have hH : 0 < H := by omega
  have ha : (2 : ℝ) ^ Nat.log 2 (i + k) ≤ ((H + k : ℕ) : ℝ) := by
    exact_mod_cast (le_trans (Nat.pow_log_le_add_one 2 (i + k))
      (by omega : i + k + 1 ≤ H + k))
  have hb : (2 : ℝ) ^ Nat.log 2 (j + k + 1) ≤ ((H + k : ℕ) : ℝ) := by
    exact_mod_cast (le_trans (Nat.pow_log_le_self 2 (by omega : j + k + 1 ≠ 0))
      (by omega : j + k + 1 ≤ H + k))
  have hc : ((H + k : ℕ) : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 * (2 : ℝ) ^ (k + 2) := by
    have hlin : H + k ≤ H * (k + 1) := by nlinarith
    have hpoly : (H + k) ^ 2 ≤ H ^ 2 * (k + 1) ^ 2 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left hlin 2
    have hbound := Nat.mul_le_mul_left (H ^ 2) (smoothing_square_le_pow k)
    exact_mod_cast le_trans hpoly hbound
  calc
    ‖smoothingTerm i j k‖ ≤
        (2 : ℝ) ^ ((Nat.log 2 (i + k) : ℤ) +
          (Nat.log 2 (j + k + 1) : ℤ) - ((i + k + 1 : ℕ) : ℤ)) :=
      smoothingTerm_norm_le_zpow i j k
    _ = ((2 : ℝ) ^ Nat.log 2 (i + k) * (2 : ℝ) ^ Nat.log 2 (j + k + 1)) /
        (2 : ℝ) ^ (i + k + 1) := by
      rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp only [zpow_natCast]
    _ ≤ ((H + k : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ (i + k + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [pow_two] using mul_le_mul ha hb (by positivity) (by positivity)
    _ ≤ ((H : ℝ) ^ 2 * (2 : ℝ) ^ (k + 2)) / (2 : ℝ) ^ (i + k + 1) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = 2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
      rw [show i + k + 1 = i + (k + 1) by omega]
      simp only [pow_add, pow_one, pow_two]
      field_simp

theorem smoothingMoment_norm_le_uniform (H i j : ℕ) (hi : i < H) (hj : j < H) :
    ‖smoothingMoment i j‖ ≤ 2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
  have hpartial : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, smoothingTerm i j k‖ ≤
      2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, norm_zero]; positivity
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (Padic.nonarchimedean _ _).trans
        (max_le ih (smoothingTerm_norm_le_uniform H i j n hi hj))
  exact le_of_tendsto_of_tendsto'
    ((smoothingMoment_hasSum i j).tendsto_sum_nat.norm) tendsto_const_nhds hpartial

end InternalCatalan



noncomputable section

open Filter
open scoped BigOperators Topology

namespace InternalCatalan

private theorem smoothingScalar_step (n : ℕ) :
    ((n + 3 : ℕ) : ℚ) * momentScalar (n + 2) =
      ((n + 2 : ℕ) : ℚ) * momentScalar n := by
  rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
  · rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      momentScalar_even, momentScalar_even]
    have hc := centralCoeff_step l
    have hc' := congrArg (fun x : ℚ => ((2 * l + 3 : ℕ) : ℚ) * x) hc
    have hc0 := centralCoeff_ne_zero l
    have hc1 := centralCoeff_ne_zero (l + 1)
    have hden0 : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hden1 : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast at hc' ⊢
    field_simp
    nlinarith only [hc']
  · rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      momentScalar_odd, momentScalar_odd]
    ring

theorem momentScalar_padic_tendsto_zero :
    Tendsto (fun n : ℕ => (momentScalar n : ℚ_[2])) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : ‖(momentScalar n : ℚ_[2])‖ ≤ ‖smoothingTerm 0 0 n‖ := by
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have he : (momentScalar n : ℚ_[2]) =
        ((n + 1 : ℕ) : ℚ_[2]) * smoothingTerm 0 0 n := by
      simp only [smoothingTerm, Nat.zero_add]
      exact_mod_cast (show momentScalar n =
        ((n + 1 : ℕ) : ℚ) * (momentScalar n / ((n + 1 : ℕ) : ℚ)) by
          field_simp)
    have hb : ‖((n + 1 : ℕ) : ℚ_[2])‖ ≤ 1 := by
      simpa only [Int.cast_natCast] using
        (Padic.norm_int_le_one (p := 2) ((n + 1 : ℕ) : ℤ))
    rw [he, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hb
  apply squeeze_zero_norm hnorm
  simpa only [norm_zero] using (smoothingTerm_tendsto_zero 0 0).norm

private theorem smoothing_sum_range_sub_add_two (f : ℕ → ℚ_[2]) (n : ℕ) :
    (∑ u ∈ Finset.range n, (f u - f (u + 2))) =
      f 0 + f 1 - f n - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem smoothing_hasSum_sub_add_two_value (f : ℕ → ℚ_[2])
    (hf : Tendsto f atTop (𝓝 0)) {a : ℚ_[2]}
    (ha : HasSum (fun u => f u - f (u + 2)) a) : a = f 0 + f 1 := by
  have ht : Tendsto (fun n => f 0 + f 1 - f n - f (n + 1))
      atTop (𝓝 (f 0 + f 1)) := by
    simpa using
      ((tendsto_const_nhds.sub hf).sub (hf.comp (tendsto_add_atTop_nat 1)))
  have hs := ha.tendsto_sum_nat
  simp only [smoothing_sum_range_sub_add_two] at hs
  exact tendsto_nhds_unique hs ht

theorem smoothingMoment_first_boundary_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ_[2]) * smoothingMoment (d + 2) 0 =
      ((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment d 0 +
        (momentScalar d : ℚ_[2]) + (momentScalar (d + 1) : ℚ_[2]) := by
  have hs := ((smoothingMoment_hasSum (d + 2) 0).mul_left
      ((d + 2 : ℕ) : ℚ_[2])).sub
    ((smoothingMoment_hasSum d 0).mul_left ((d + 1 : ℕ) : ℚ_[2]))
  have hs' : HasSum
      (fun u => (momentScalar (d + u) : ℚ_[2]) -
        (momentScalar (d + u + 2) : ℚ_[2]))
      (((d + 2 : ℕ) : ℚ_[2]) * smoothingMoment (d + 2) 0 -
        ((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment d 0) := by
    convert hs using 1
    rfl
    ext u
    have hrec := smoothingScalar_step (d + u)
    have hq : momentScalar (d + u) - momentScalar (d + u + 2) =
        ((d + 2 : ℕ) : ℚ) *
          (momentScalar (d + 2 + u) / ((u + 1 : ℕ) : ℚ)) -
        ((d + 1 : ℕ) : ℚ) *
          (momentScalar (d + u) / ((u + 1 : ℕ) : ℚ)) := by
      rw [show d + 2 + u = d + u + 2 by omega]
      have hu : (u : ℚ) + 1 ≠ 0 := by positivity
      push_cast at hrec ⊢
      field_simp [hu]
      nlinarith only [hrec]
    simpa only [smoothingTerm, Nat.zero_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℚ_[2])) hq
  have hlim : Tendsto (fun u => (momentScalar (d + u) : ℚ_[2])) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm d] using
      momentScalar_padic_tendsto_zero.comp (tendsto_add_atTop_nat d)
  have hv := smoothing_hasSum_sub_add_two_value _ hlim hs'
  simp only [Nat.add_zero] at hv
  linear_combination hv

theorem smoothingMoment_one_zero : smoothingMoment 1 0 = 2 := by
  have hs := (hasSum_nat_add_iff' 1).mpr (smoothingMoment_hasSum 1 0)
  have hs' : HasSum
      (fun u => (momentScalar u : ℚ_[2]) - (momentScalar (u + 2) : ℚ_[2]))
      (smoothingMoment 1 0) := by
    convert hs using 1
    · rfl
    · ext u
      have hrec := smoothingScalar_step u
      have hq : momentScalar u - momentScalar (u + 2) =
          momentScalar (u + 2) / ((u + 2 : ℕ) : ℚ) := by
        have hu : (u : ℚ) + 2 ≠ 0 := by positivity
        push_cast at hrec ⊢
        field_simp [hu]
        nlinarith only [hrec]
      simpa only [smoothingTerm, Nat.zero_add,
        show 1 + (u + 1) = u + 2 by omega,
        show u + 1 + 1 = u + 2 by omega,
        Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using
          congrArg (fun x : ℚ => (x : ℚ_[2])) hq
    · simp [smoothingTerm, momentScalar_odd 0]
  have hv := smoothing_hasSum_sub_add_two_value _ momentScalar_padic_tendsto_zero hs'
  simpa [momentScalar_odd 0] using hv

theorem smoothingMoment_second_boundary_step (d : ℕ) :
    ((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment 0 (d + 2) =
      (d : ℚ_[2]) * smoothingMoment 0 d + 2 / ((d + 1 : ℕ) : ℚ_[2]) := by
  have htail := (hasSum_nat_add_iff' 2).mpr (smoothingMoment_hasSum 0 d)
  have htail' : HasSum
      (fun u => ((momentScalar (u + 2) / ((d + u + 3 : ℕ) : ℚ) : ℚ) : ℚ_[2]))
      (smoothingMoment 0 d - 2 / ((d + 1 : ℕ) : ℚ_[2])) := by
    convert htail using 1
    · rfl
    · ext u
      simp only [smoothingTerm, Nat.zero_add,
        show d + (u + 2) + 1 = d + u + 3 by omega]
    · simp [smoothingTerm, Finset.sum_range_succ, momentScalar_odd 0]
  have hs := ((smoothingMoment_hasSum 0 (d + 2)).mul_left
      ((d + 1 : ℕ) : ℚ_[2])).sub (htail'.mul_left (d : ℚ_[2]))
  have hs' : HasSum
      (fun u => (momentScalar u : ℚ_[2]) - (momentScalar (u + 2) : ℚ_[2]))
      (((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment 0 (d + 2) -
        (d : ℚ_[2]) * (smoothingMoment 0 d - 2 / ((d + 1 : ℕ) : ℚ_[2]))) := by
    convert hs using 1
    rfl
    ext u
    have hrec := smoothingScalar_step u
    have hq : momentScalar u - momentScalar (u + 2) =
        ((d + 1 : ℕ) : ℚ) * (momentScalar u / ((d + u + 3 : ℕ) : ℚ)) -
        (d : ℚ) * (momentScalar (u + 2) / ((d + u + 3 : ℕ) : ℚ)) := by
      have hu : (d : ℚ) + u + 3 ≠ 0 := by positivity
      push_cast at hrec ⊢
      field_simp [hu]
      nlinarith only [hrec]
    simpa only [smoothingTerm, Nat.zero_add,
      show d + 2 + u + 1 = d + u + 3 by omega,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using
        congrArg (fun x : ℚ => (x : ℚ_[2])) hq
  have hv := smoothing_hasSum_sub_add_two_value _ momentScalar_padic_tendsto_zero hs'
  have hd : (d : ℚ_[2]) + 1 ≠ 0 := by
    exact_mod_cast (show (d : ℚ) + 1 ≠ 0 by positivity)
  simp only [momentScalar_zero, momentScalar_odd 0, Rat.cast_ofNat,
    Rat.cast_zero, add_zero] at hv
  push_cast at hv ⊢
  field_simp [hd] at hv ⊢
  linear_combination hv

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

theorem smoothingMoment_minus_decomposition (d : ℕ) :
    smoothingMoment (d) (0) = (boundaryMinus d : ℚ_[2]) +
      smoothingMoment 0 0 * (centralCoeffKernel (d : ℤ) : ℚ_[2]) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases d with
      | zero =>
        simpa [centralCoeffKernel] using smoothingMoment_one_zero
      | succ d =>
        change smoothingMoment ((d + 2)) (0) = (boundaryMinus (d + 2) : ℚ_[2]) +
          smoothingMoment 0 0 * (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℚ_[2])
        have ha := smoothingMoment_first_boundary_step d
        rw [ih d (by omega)] at ha
        have hr : ((d + 2 : ℕ) : ℚ_[2]) * (boundaryMinus (d + 2) : ℚ_[2]) =
            ((d + 1 : ℕ) : ℚ_[2]) * (boundaryMinus d : ℚ_[2]) +
              (momentScalar d : ℚ_[2]) + (momentScalar (d + 1) : ℚ_[2]) := by
          exact_mod_cast boundaryMinus_step d
        have hc : ((d + 2 : ℕ) : ℚ_[2]) *
              (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℚ_[2]) =
            ((d + 1 : ℕ) : ℚ_[2]) * (centralCoeffKernel (d : ℤ) : ℚ_[2]) := by
          exact_mod_cast centralCoeffKernel_nat_step d
        have hstart := congrArg (fun x : ℚ_[2] => smoothingMoment 0 0 * x) hc
        have hd : ((d + 2 : ℕ) : ℚ_[2]) ≠ 0 := by
          exact_mod_cast (show ((d + 2 : ℕ) : ℚ) ≠ 0 by positivity)
        apply mul_left_cancel₀ hd
        linear_combination ha - hr - hstart

theorem smoothingMoment_plus_succ_decomposition (u : ℕ) :
    smoothingMoment (0) ((u + 1)) = (boundaryPlus (u + 1) : ℚ_[2]) +
      smoothingMoment 0 1 * (centralCoeffKernel (u : ℤ) : ℚ_[2]) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero =>
        have ha := smoothingMoment_second_boundary_step 0
        norm_num at ha
        simpa [boundaryPlus, centralCoeffKernel] using ha
      | succ u =>
        change smoothingMoment (0) ((u + 2 + 1)) =
          (boundaryPlus (u + 2 + 1) : ℚ_[2]) +
            smoothingMoment 0 1 * (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℚ_[2])
        have ha := smoothingMoment_second_boundary_step (u + 1)
        rw [ih u (by omega)] at ha
        have hr : ((u + 1 + 1 : ℕ) : ℚ_[2]) * (boundaryPlus (u + 1 + 2) : ℚ_[2]) =
            ((u + 1 : ℕ) : ℚ_[2]) * (boundaryPlus (u + 1) : ℚ_[2]) +
              2 / ((u + 1 + 1 : ℕ) : ℚ_[2]) := by
          have hr0 := congrArg (fun x : ℚ => (x : ℚ_[2])) (boundaryPlus_step (u + 1))
          push_cast at hr0 ⊢
          exact hr0
        have hc : ((u + 2 : ℕ) : ℚ_[2]) *
              (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℚ_[2]) =
            ((u + 1 : ℕ) : ℚ_[2]) * (centralCoeffKernel (u : ℤ) : ℚ_[2]) := by
          exact_mod_cast centralCoeffKernel_nat_step u
        have hstart := congrArg (fun x : ℚ_[2] => smoothingMoment 0 1 * x) hc
        have hu : ((u + 2 : ℕ) : ℚ_[2]) ≠ 0 := by
          exact_mod_cast (show ((u + 2 : ℕ) : ℚ) ≠ 0 by positivity)
        apply mul_left_cancel₀ hu
        linear_combination ha - hr - hstart

theorem smoothingMoment_decomposition (i j : ℕ) :
    smoothingMoment (i) (j) = (momentRat i j : ℚ_[2]) +
      smoothingMoment 0 0 * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]) +
      smoothingMoment 0 1 * (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => norm_num [centralCoeffKernel]
    | succ j =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((j + 1 : ℕ) : ℤ)) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      have he : ((j + 1 : ℕ) : ℤ) - (0 : ℤ) - 1 = (j : ℤ) := by omega
      simp only [Nat.cast_zero]
      rw [momentRat_zero_left, hn, he]
      simpa using smoothingMoment_plus_succ_decomposition j
  | succ i ih =>
    cases j with
    | zero =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      simp only [Nat.cast_zero]
      rw [momentRat_zero_right, hn]
      simpa using smoothingMoment_minus_decomposition (i + 1)
    | succ j =>
      have ha := smoothingMoment_step i j
      have hr : (momentRat i j : ℚ_[2]) - (momentRat (i + 1) (j + 1) : ℚ_[2]) =
          (momentScalar i : ℚ_[2]) / ((j + 1 : ℕ) : ℚ_[2]) := by
        exact_mod_cast momentRat_step i j
      have hd : ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) =
          (i : ℤ) - (j : ℤ) := by omega
      have he : ((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1 =
          (j : ℤ) - (i : ℤ) - 1 := by omega
      change smoothingMoment ((i + 1)) ((j + 1)) =
        (momentRat (i + 1) (j + 1) : ℚ_[2]) +
          smoothingMoment 0 0 * (centralCoeffKernel (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) : ℚ_[2]) +
          smoothingMoment 0 1 *
            (centralCoeffKernel (((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) : ℚ_[2])
      rw [hd, he]
      rw [ih j] at ha
      push_cast at ha hr
      linear_combination hr - ha

theorem smoothingMoment_discrepancies (q : ℚ) (i j : ℕ) :
    (momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
        (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]) =
      smoothingMoment i j +
        (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
          (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]) +
        (-smoothingMoment 0 1) *
          (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]) := by
  rw [smoothingMoment_decomposition]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.TwoAdicSmoothedMinor
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan


def rawMatrixRat (z : ℚ) (N : ℕ) :
    Matrix (Fin (n N)) ↥(Finset.Ico (b N) (L N)) ℚ :=
  fun r j => rawEntryRat z N r.val j.val

def rawFilterInt (N : ℕ) :
    Matrix ↥(Finset.Ico (b N) (L N)) (Fin (n N)) ℤ :=
  fun j k => filterCoeff N j.val k.val

theorem filteredEntryRat_eq_sum_contactRange (z : ℚ) (N r k : ℕ)
    (hk : k < n N) :
    filteredEntryRat z N r k =
      ∑ j ∈ Finset.Ico (b N) (L N),
        (filterCoeff N j k : ℚ) * rawEntryRat z N r j := by
  let F : ℤ[X] →ₗ[ℤ] ℚ :=
    Polynomial.lsum fun j => LinearMap.toSpanSingleton ℤ ℚ (rawEntryRat z N r j)
  have hF (j : ℕ) : F (X ^ j) = rawEntryRat z N r j := by
    simp [F, Polynomial.lsum_apply, Polynomial.X_pow_eq_monomial]
  calc
    filteredEntryRat z N r k = F (filteredColumnInt N k) := by
      rw [map_filteredColumnInt]
      simp only [hF, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast]
      rfl
    _ = _ := by
      simpa only [hF, zsmul_eq_mul] using
        (map_filteredColumnInt_contactRange F N k hk)

theorem filteredMatrixRat_eq_raw_mul_filter (z : ℚ) (N : ℕ) :
    (fun r k : Fin (n N) => filteredEntryRat z N r.val k.val) =
      rawMatrixRat z N * (Matrix.of fun j k => (rawFilterInt N j k : ℚ)) := by
  ext r k
  rw [Matrix.mul_apply]
  simp only [rawMatrixRat, rawFilterInt, Matrix.of_apply]
  rw [Finset.sum_coe_sort (Finset.Ico (b N) (L N))
    (fun j : ℕ => rawEntryRat z N r.val j * (filterCoeff N j k.val : ℚ))]
  rw [filteredEntryRat_eq_sum_contactRange z N r.val k.val k.isLt]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem determinantRat_eq_det_raw_mul_filter (z : ℚ) (N : ℕ) :
    determinantRat z N =
      Matrix.det (rawMatrixRat z N * (Matrix.of fun j k => (rawFilterInt N j k : ℚ))) := by
  rw [determinantRat, filteredMatrixRat_eq_raw_mul_filter]

def rawMinorRat (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) : ℚ :=
  Matrix.det (Matrix.of fun r k : Fin (n N) => rawEntryRat z N r.val (c k).val)

theorem rawMinorRat_eq_zero_of_not_injective (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (hc : ¬Function.Injective c) : rawMinorRat z N c = 0 := by
  classical
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  unfold rawMinorRat
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply]
  rw [hij]

theorem determinantRat_eq_sum_raw_choices (z : ℚ) (N : ℕ) :
    determinantRat z N =
      ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)),
        ((∏ k : Fin (n N), rawFilterInt N (c k) k : ℤ) : ℚ) * rawMinorRat z N c := by
  classical
  rw [determinantRat_eq_det_raw_mul_filter]
  calc
    _ = ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)),
        ∑ σ : Equiv.Perm (Fin (n N)), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k : Fin (n N),
            rawMatrixRat z N (σ k) (c k) * (rawFilterInt N (c k) k : ℚ) := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.of_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [rawMinorRat, rawMatrixRat, rawFilterInt]
      rw [Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      simp only [Int.cast_prod, Finset.prod_mul_distrib, Matrix.of_apply]
      ring

theorem determinantRat_eq_sum_raw_minors (z : ℚ) (N : ℕ) :
    determinantRat z N =
      ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)) with Function.Injective c,
        ((∏ k : Fin (n N), rawFilterInt N (c k) k : ℤ) : ℚ) * rawMinorRat z N c := by
  classical
  rw [determinantRat_eq_sum_raw_choices]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hcinj
  have hnot : ¬Function.Injective c := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcinj
  rw [rawMinorRat_eq_zero_of_not_injective z N c hnot, mul_zero]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

def intPolynomialSeries (P : ℤ[X]) : PowerSeries ℚ :=
  (P.map (Int.castRingHom ℚ) : ℚ[X])

@[simp] theorem coeff_intPolynomialSeries (P : ℤ[X]) (j : ℕ) :
    PowerSeries.coeff j (intPolynomialSeries P) = (P.coeff j : ℚ) := by
  simp [intPolynomialSeries]

@[simp] theorem intPolynomialSeries_mul (P Q : ℤ[X]) :
    intPolynomialSeries (P * Q) = intPolynomialSeries P * intPolynomialSeries Q := by
  simp [intPolynomialSeries]

def contactSeries (P : ℤ[X]) : PowerSeries ℚ :=
  intPolynomialSeries P * (PowerSeries.X * centralKernelSeries)

theorem coeff_X_centralKernelSeries (j : ℕ) :
    PowerSeries.coeff j (PowerSeries.X * centralKernelSeries) =
      centralCoeffKernel ((j : ℤ) - 1) := by
  cases j with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, Nat.cast_zero,
        centralCoeffKernel_of_neg (by norm_num : (0 : ℤ) - 1 < 0)]
  | succ j =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_centralKernelSeries]
      congr 1
      omega

theorem contactSeries_coeff_eq_sum (P : ℤ[X]) {B j : ℕ} (hj : j < B) :
    PowerSeries.coeff j (contactSeries P) =
      ∑ i ∈ Finset.range B,
        (P.coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1) := by
  unfold contactSeries
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => PowerSeries.coeff i (intPolynomialSeries P) *
        PowerSeries.coeff k (PowerSeries.X * centralKernelSeries)) j]
  calc
    _ = ∑ i ∈ Finset.range (j + 1),
        (P.coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coeff_intPolynomialSeries, coeff_X_centralKernelSeries]
      congr 2
      have hi' := Finset.mem_range.mp hi
      omega
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ B))
      intro i hi hin
      have hin' : ¬ i < j + 1 := by simpa only [Finset.mem_range] using hin
      rw [centralCoeffKernel_of_neg (by omega : (j : ℤ) - i - 1 < 0), mul_zero]

theorem series_coeff_mul_congr_below {S T : PowerSeries ℚ} {B : ℕ}
    (hST : ∀ j < B, PowerSeries.coeff j S = PowerSeries.coeff j T)
    (Q : PowerSeries ℚ) {j : ℕ} (hj : j < B) :
    PowerSeries.coeff j (Q * S) = PowerSeries.coeff j (Q * T) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨u, v⟩ huv
  have huv' : u + v = j := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [hST v (by omega)]

theorem contactSeries_mul (P Q : ℤ[X]) :
    contactSeries (P * Q) = intPolynomialSeries P * contactSeries Q := by
  simp only [contactSeries, intPolynomialSeries_mul, mul_assoc]

theorem reversedChebyshev_contact_series {C d j : ℕ}
    (hd : d < C) (hj : j < C) :
    PowerSeries.coeff j
        (contactSeries (reversedRow C (Chebyshev.T ℤ (d : ℤ)))) =
      PowerSeries.coeff j
        (intPolynomialSeries (reversedRow C (Chebyshev.U ℤ ((d : ℤ) - 1)))) := by
  rw [contactSeries_coeff_eq_sum _ hj, coeff_intPolynomialSeries]
  exact reversedChebyshev_contact hd hj

theorem row_contact_of_gt_g {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : g N < r) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  have hjC : j < Cdegree N := by
    rw [Cdegree_eq_L_add_g]
    omega
  have hjH : j < H N := by
    rw [H_eq_Cdegree_add_h]
    omega
  have hd : rowDistance N r < Cdegree N := rowDistance_lt_Cdegree hN hr
  have hs : Int.sign (rowOffset N r) = 1 := by
    apply Int.sign_eq_one_of_pos
    unfold rowOffset
    omega
  have hbase : ∀ l < Cdegree N,
      PowerSeries.coeff l
          (contactSeries
            (reversedRow (Cdegree N) (Chebyshev.T ℤ (rowDistance N r : ℤ)))) =
        PowerSeries.coeff l
          (intPolynomialSeries
            (reversedRow (Cdegree N)
              (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)))) := by
    intro l hl
    exact reversedChebyshev_contact_series hd hl
  have hmul := series_coeff_mul_congr_below hbase
    (intPolynomialSeries ((1 - X : ℤ[X]) ^ h N)) hjC
  rw [← contactSeries_mul, ← intPolynomialSeries_mul] at hmul
  rw [contactSeries_coeff_eq_sum _ hjH, coeff_intPolynomialSeries] at hmul
  simpa only [rowP, rowD, hs, Polynomial.C_1, one_mul] using hmul

theorem row_contact {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  rcases le_or_gt r (g N) with hrg | hrg
  · exact row_contact_of_le_g hN hr hrg hj
  · exact row_contact_of_gt_g hN hr hrg hj

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def smoothingColumn (N r j : ℕ) : ℚ_[2] :=
  ∑ i ∈ Finset.range (H N),
    ((rowP N r).coeff i : ℚ_[2]) * smoothingMoment i j

def exceptionColumn (q : ℚ) (N r j : ℕ) : ℚ_[2] :=
  (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
    ∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ_[2]) *
        (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2])

def boundaryColumn (N r j : ℕ) : ℚ_[2] :=
  ∑ i ∈ Finset.range (H N),
    ((rowD N r).coeff i : ℚ_[2]) *
      ((-smoothingMoment 0 1) * (if i = j then 1 else 0) -
        (3 / 2 : ℚ_[2]) * (zetaRat i j : ℚ_[2]))

theorem rawEntryRat_two_adic_decomposition (q : ℚ) {N r j : ℕ}
    (hN : 0 < N) (hr : r < n N) (hj : j < L N) :
    (rawEntryRat q N r j : ℚ_[2]) =
      smoothingColumn N r j + exceptionColumn q N r j + boundaryColumn N r j := by
  classical
  have hjH : j < H N := by
    have hLH : L N ≤ H N := by unfold L H; omega
    exact lt_of_lt_of_le hj hLH
  have hcontact :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          (centralCoeffKernel ((j : ℤ) - i - 1) : ℚ_[2])) =
        ((rowD N r).coeff j : ℚ_[2]) := by
    exact_mod_cast row_contact hN hr hj
  have hdelta :
      (∑ i ∈ Finset.range (H N),
        ((rowD N r).coeff i : ℚ_[2]) * (if i = j then 1 else 0)) =
        ((rowD N r).coeff j : ℚ_[2]) := by
    simp [Finset.mem_range, hjH]
  have hE :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) =
        exceptionColumn q N r j := by
    unfold exceptionColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hB :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((-smoothingMoment 0 1) *
            (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]))) =
        (-smoothingMoment 0 1) * ((rowD N r).coeff j : ℚ_[2]) := by
    rw [← hcontact, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hentrysum :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) =
        smoothingColumn N r j + exceptionColumn q N r j +
          (-smoothingMoment 0 1) * ((rowD N r).coeff j : ℚ_[2]) := by
    simp_rw [smoothingMoment_discrepancies q, mul_add, Finset.sum_add_distrib]
    rw [hE, hB]
    rfl
  have hboundary : boundaryColumn N r j =
      (-smoothingMoment 0 1) * ((rowD N r).coeff j : ℚ_[2]) -
        (3 / 2 : ℚ_[2]) *
          ∑ i ∈ Finset.range (H N),
            ((rowD N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
    unfold boundaryColumn
    calc
      _ = (-smoothingMoment 0 1) *
          (∑ i ∈ Finset.range (H N),
            ((rowD N r).coeff i : ℚ_[2]) * (if i = j then 1 else 0)) -
          (3 / 2 : ℚ_[2]) *
            ∑ i ∈ Finset.range (H N),
              ((rowD N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hdelta]
  have hrawcast : (rawEntryRat q N r j : ℚ_[2]) =
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) -
        (3 / 2 : ℚ_[2]) *
          ∑ i ∈ Finset.range (H N),
            ((rowD N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
    simp only [rawEntryRat, Rat.cast_sub, Rat.cast_mul, Rat.cast_sum,
      Rat.cast_add, Rat.cast_ofNat, Rat.cast_div, Rat.cast_intCast]
  rw [hrawcast, hentrysum, hboundary]
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def rawColumnTerm (z : ℚ) (N r j : ℕ) (t : Fin 3) : ℚ_[2] :=
  if t = 0 then smoothingColumn N r j
  else if t = 1 then exceptionColumn z N r j
  else boundaryColumn N r j

theorem rawColumnTerm_sum (z : ℚ) (N r j : ℕ) :
    (∑ t : Fin 3, rawColumnTerm z N r j t) =
      smoothingColumn N r j + exceptionColumn z N r j + boundaryColumn N r j := by
  simp [Fin.sum_univ_succ, rawColumnTerm, add_assoc]

theorem rawMinorRat_cast_two_adic (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    (rawMinorRat z N c : ℚ_[2]) =
      Matrix.det (Matrix.of fun r k : Fin (n N) =>
        (rawEntryRat z N r.val (c k).val : ℚ_[2])) := by
  simp only [rawMinorRat, Matrix.det_apply', Matrix.of_apply, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_prod, Rat.cast_intCast]

theorem rawMinorRat_two_adic_column_expansion (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    (rawMinorRat z N c : ℚ_[2]) =
      ∑ τ : Fin (n N) → Fin 3,
        Matrix.det (Matrix.of fun r k : Fin (n N) =>
          rawColumnTerm z N r.val (c k).val (τ k)) := by
  classical
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => (rawEntryRat z N r.val (c k).val : ℚ_[2])) =
        (Matrix.of fun r k : Fin (n N) =>
          ∑ t : Fin 3, rawColumnTerm z N r.val (c k).val t) := by
    ext r k
    simp only [Matrix.of_apply, rawColumnTerm_sum]
    exact rawEntryRat_two_adic_decomposition z hN r.isLt
      (Finset.mem_Ico.mp (c k).property).2
  rw [rawMinorRat_cast_two_adic, hmatrix]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]


end InternalCatalan

end



noncomputable section

namespace InternalCatalan

theorem padic_two_norm_int_le_of_pow_dvd {z : ℤ} {e : ℕ}
    (hdiv : (2 : ℤ) ^ e ∣ z) : ‖(z : ℚ_[2])‖ ≤ 1 / (2 : ℝ) ^ e := by
  obtain ⟨w, rfl⟩ := hdiv
  push_cast
  rw [norm_mul, norm_pow]
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  rw [htwo]
  calc
    (1 / 2 : ℝ) ^ e * ‖(w : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ e * 1 :=
      mul_le_mul_of_nonneg_left (Padic.norm_int_le_one w) (by positivity)
    _ = 1 / (2 : ℝ) ^ e := by simp only [mul_one, one_div_pow]

theorem smoothingColumn_term_norm_le (N r i j : ℕ) (hi : i < H N) (hj : j < H N) :
    ‖((rowP N r).coeff i : ℚ_[2]) * smoothingMoment i j‖ ≤
      8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
  have hp := padic_two_norm_int_le_of_pow_dvd (rowP_coeff_two_pow_dvd N r i)
  have hm := smoothingMoment_norm_le_uniform (H N) i j hi hj
  have hexp : Cdegree N ≤ (Cdegree N - 2 - i) + i + 2 := by omega
  have hpow : (2 : ℝ) ^ Cdegree N ≤
      (2 : ℝ) ^ ((Cdegree N - 2 - i) + i) * 4 := by
    calc
      (2 : ℝ) ^ Cdegree N ≤ (2 : ℝ) ^ (((Cdegree N - 2 - i) + i) + 2) :=
        pow_le_pow_right₀ (by norm_num) hexp
      _ = (2 : ℝ) ^ ((Cdegree N - 2 - i) + i) * 4 := by
        rw [pow_add]
        norm_num
  rw [norm_mul]
  calc
    ‖((rowP N r).coeff i : ℚ_[2])‖ * ‖smoothingMoment i j‖ ≤
        (1 / (2 : ℝ) ^ (Cdegree N - 2 - i)) *
          (2 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ i) :=
      mul_le_mul hp hm (norm_nonneg _) (by positivity)
    _ = 2 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ ((Cdegree N - 2 - i) + i) := by
      rw [pow_add]
      ring
    _ ≤ 8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * (H N : ℝ) ^ 2)
      nlinarith only [hh]

theorem smoothingColumn_norm_le (N r j : ℕ) (hj : j < H N) :
    ‖smoothingColumn N r j‖ ≤ 8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
  unfold smoothingColumn
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  exact smoothingColumn_term_norm_le N r i j (Finset.mem_range.mp hi) hj







open scoped BigOperators

theorem padic_two_det_norm_le_prod_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[2]) (U : ι → ℝ) (hU : ∀ k, 0 ≤ U k)
    (hM : ∀ r k, ‖M r k‖ ≤ U k) :
    ‖Matrix.det M‖ ≤ ∏ k, U k := by
  classical
  rw [Matrix.det_apply']
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Finset.prod_nonneg (fun k hk => hU k))
  intro σ hσ
  rw [norm_mul, norm_prod]
  calc
    ‖((Equiv.Perm.sign σ : ℤ) : ℚ_[2])‖ * ∏ k, ‖M (σ k) k‖ ≤
        1 * ∏ k, U k := by
      apply mul_le_mul (Padic.norm_int_le_one (Equiv.Perm.sign σ))
      · exact Finset.prod_le_prod (fun k hk => norm_nonneg _) (fun k hk => hM (σ k) k)
      · exact Finset.prod_nonneg (fun k hk => norm_nonneg _)
      · norm_num
    _ = ∏ k, U k := one_mul _


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.ExceptionalScalarBounds
namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem two_adic_sum_lower {α : Type*} (s : Finset α) (f : α → ℚ)
    (B : ℤ) (hB : B ≤ 0) (hf : ∀ x ∈ s, B ≤ padicValRat 2 (f x)) :
    B ≤ padicValRat 2 (∑ x ∈ s, f x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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

theorem harmonicRat_two_adic_lower (d n H : ℕ) (hn : n ≤ H) :
    -((d : ℤ) * (Nat.log 2 H : ℤ)) ≤ padicValRat 2 (harmonicRat d n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold harmonicRat
  apply two_adic_sum_lower
  · have : 0 ≤ (d : ℤ) * (Nat.log 2 H : ℤ) := by positivity
    omega
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hval : padicValNat 2 (k + 1) ≤ Nat.log 2 H :=
      (padicValNat_le_nat_log (p := 2) (k + 1)).trans
        (Nat.log_mono_right (by omega : k + 1 ≤ H))
    have hval' : (padicValNat 2 (k + 1) : ℤ) ≤ (Nat.log 2 H : ℤ) := by
      exact_mod_cast hval
    simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hval' (by positivity))

private theorem zetaRat_two_adic_lower_of_le (H i j : ℕ)
    (hi : i < H) (hji : j ≤ i) :
    -2 * (Nat.log 2 H : ℤ) ≤ padicValRat 2 (zetaRat i j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hj : j < H := lt_of_le_of_lt hji hi
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, padicValRat.neg]
    simpa using harmonicRat_two_adic_lower 2 i H (Nat.le_of_lt hi)
  · have hden : ((i - j : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show i - j ≠ 0 by omega)
    have heq : (i : ℚ) - (j : ℚ) = ((i - j : ℕ) : ℚ) :=
      (Nat.cast_sub hji).symm
    by_cases hnum : harmonicRat 1 i - harmonicRat 1 j = 0
    · rw [zetaRat_of_ne hij, hnum, zero_div, padicValRat.zero]
      have : 0 ≤ (Nat.log 2 H : ℤ) := by positivity
      omega
    · have hival : -(Nat.log 2 H : ℤ) ≤ padicValRat 2 (harmonicRat 1 i) := by
        simpa using harmonicRat_two_adic_lower 1 i H (Nat.le_of_lt hi)
      have hjval : -(Nat.log 2 H : ℤ) ≤ padicValRat 2 (harmonicRat 1 j) := by
        simpa using harmonicRat_two_adic_lower 1 j H (Nat.le_of_lt hj)
      have hsum := padicValRat.min_le_padicValRat_add (p := 2)
        (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
        (by simpa only [sub_eq_add_neg] using hnum)
      rw [← sub_eq_add_neg, padicValRat.neg] at hsum
      have hnval : -(Nat.log 2 H : ℤ) ≤
          padicValRat 2 (harmonicRat 1 i - harmonicRat 1 j) :=
        (le_min hival hjval).trans hsum
      have hdval : padicValNat 2 (i - j) ≤ Nat.log 2 H :=
        (padicValNat_le_nat_log (p := 2) (i - j)).trans
          (Nat.log_mono_right (by omega : i - j ≤ H))
      rw [zetaRat_of_ne hij, heq, padicValRat.div hnum hden, padicValRat.of_nat]
      omega

theorem zetaRat_two_adic_lower (H i j : ℕ) (hi : i < H) (hj : j < H) :
    -2 * (Nat.log 2 H : ℤ) ≤ padicValRat 2 (zetaRat i j) := by
  rcases le_total j i with hji | hij
  · exact zetaRat_two_adic_lower_of_le H i j hi hji
  · rw [zetaRat_symm]
    exact zetaRat_two_adic_lower_of_le H j i hj hij


end InternalCatalan



noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

def exceptionScalar (q : ℚ) (N u j : ℕ) : ℚ_[2] :=
  (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
    ∑ v ∈ Finset.range (h N + 1),
      (((1 - X : ℤ[X]) ^ h N).coeff v : ℚ_[2]) *
        (centralCoeffKernel (((Cdegree N - 1 - u + v : ℕ) : ℤ) - j) : ℚ_[2])

def boundaryScalar (N u j : ℕ) : ℚ_[2] :=
  ∑ v ∈ Finset.range (h N + 1),
    (((1 - X : ℤ[X]) ^ h N).coeff v : ℚ_[2]) *
      ((-smoothingMoment 0 1) * (if Cdegree N - 1 - u + v = j then 1 else 0) -
        (3 / 2 : ℚ_[2]) * (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2]))

theorem exceptionalScalar_index_lt_H {N u v : ℕ}
    (hu : u < Cdegree N) (hv : v < h N + 1) :
    Cdegree N - 1 - u + v < H N := by
  unfold Cdegree h H at *
  omega

private theorem contract_rowFactor_reversed (N : ℕ) (F : ℤ[X]) (w : ℕ → ℚ_[2]) :
    (∑ i ∈ Finset.range (H N),
      ((((1 - X : ℤ[X]) ^ h N * reversedRow (Cdegree N) F).coeff i) : ℚ_[2]) *
        w i) =
      ∑ u ∈ Finset.range (Cdegree N), (F.coeff u : ℚ_[2]) *
        ∑ v ∈ Finset.range (h N + 1),
          (((1 - X : ℤ[X]) ^ h N).coeff v : ℚ_[2]) *
            w (Cdegree N - 1 - u + v) := by
  classical
  have hfactor : (1 - X : ℤ[X]) ^ h N =
      ∑ v ∈ Finset.range (h N + 1),
        Polynomial.C (((1 - X : ℤ[X]) ^ h N).coeff v) * X ^ v :=
    Polynomial.as_sum_range_C_mul_X_pow' _
      (lt_of_le_of_lt (rowFactor_natDegree_le N) (Nat.lt_succ_self _))
  have hpoly : (1 - X : ℤ[X]) ^ h N * reversedRow (Cdegree N) F =
      ∑ u ∈ Finset.range (Cdegree N), ∑ v ∈ Finset.range (h N + 1),
        Polynomial.C (F.coeff u * ((1 - X : ℤ[X]) ^ h N).coeff v) *
          X ^ (Cdegree N - 1 - u + v) := by
    unfold reversedRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    calc
      _ = (∑ v ∈ Finset.range (h N + 1),
          Polynomial.C (((1 - X : ℤ[X]) ^ h N).coeff v) * X ^ v) *
            (Polynomial.C (F.coeff u) * X ^ (Cdegree N - 1 - u)) :=
        congrArg (fun Q : ℤ[X] => Q *
          (Polynomial.C (F.coeff u) * X ^ (Cdegree N - 1 - u))) hfactor
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [map_mul, pow_add]
        ring
  rw [hpoly]
  simp only [finsetSum_coeff, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hi := exceptionalScalar_index_lt_H
    (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  simp [Finset.mem_range, hi, mul_assoc]

theorem exceptionColumn_eq_sum_exceptionScalar (q : ℚ) (N r j : ℕ) :
    exceptionColumn q N r j =
      ∑ u ∈ Finset.range (Cdegree N),
        ((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2]) *
          exceptionScalar q N u j := by
  unfold exceptionColumn rowP
  rw [contract_rowFactor_reversed, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  unfold exceptionScalar
  ring

theorem boundaryColumn_eq_sum_boundaryScalar (N r j : ℕ) :
    boundaryColumn N r j =
      ∑ u ∈ Finset.range (Cdegree N),
        ((Int.sign (rowOffset N r) *
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2]) *
            boundaryScalar N u j := by
  unfold boundaryColumn rowD
  simp only [mul_assoc, coeff_C_mul, Int.cast_mul]
  rw [← Finset.mul_sum, contract_rowFactor_reversed, Finset.mul_sum]
  simp only [boundaryScalar]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem padic_two_norm_rat_le_zpow_of_valuation {x : ℚ} {b : ℤ}
    (hb : b ≤ padicValRat 2 x) : ‖(x : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-b) := by
  by_cases hx : x = 0
  · simp only [hx, Rat.cast_zero, norm_zero]
    positivity
  have hx₂ : (x : ℚ_[2]) ≠ 0 := by exact_mod_cast hx
  rw [Padic.norm_eq_zpow_neg_valuation hx₂, Padic.valuation_ratCast]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (neg_le_neg hb)

theorem centralCoeff_norm_le (l : ℕ) :
    ‖(centralCoeff l : ℚ_[2])‖ ≤ (2 : ℝ) ^ (2 * (l : ℤ)) := by
  simpa only [neg_mul, neg_neg] using
    padic_two_norm_rat_le_zpow_of_valuation (centralCoeff_two_adic_lower l)

theorem centralCoeffKernel_norm_le (d : ℤ) :
    ‖(centralCoeffKernel d : ℚ_[2])‖ ≤ (2 : ℝ) ^ d := by
  by_cases hd : 0 ≤ d ∧ d % 2 = 0
  · have heq : 2 * ((d.toNat / 2 : ℕ) : ℤ) = d := by omega
    simpa only [centralCoeffKernel, if_pos hd, heq] using
      centralCoeff_norm_le (d.toNat / 2)
  · simp only [centralCoeffKernel, if_neg hd, Rat.cast_zero, norm_zero]
    positivity

theorem zetaRat_norm_le (H i j : ℕ) (hi : i < H) (hj : j < H) :
    ‖(zetaRat i j : ℚ_[2])‖ ≤ (2 : ℝ) ^ (2 * Nat.log 2 H) := by
  have hb := padic_two_norm_rat_le_zpow_of_valuation
    (zetaRat_two_adic_lower H i j hi hj)
  have heq : -(-2 * (Nat.log 2 H : ℤ)) = ((2 * Nat.log 2 H : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq, zpow_natCast] at hb
  exact hb

theorem exceptionScalar_norm_le (q : ℚ) {N u : ℕ} (j : ℕ)
    (hu : u < Cdegree N) :
    ‖exceptionScalar q N u j‖ ≤
      ‖4 * (q : ℚ_[2]) - smoothingMoment 0 0‖ *
        (2 : ℝ) ^ ((H N : ℤ) - 1 - u - j) := by
  unfold exceptionScalar
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro v hv
  have hv' := Finset.mem_range.mp hv
  have hCH := H_eq_Cdegree_add_h N
  have hindex : (((Cdegree N - 1 - u + v : ℕ) : ℤ) - j) ≤
      (H N : ℤ) - 1 - u - j := by omega
  have hk := (centralCoeffKernel_norm_le
    (((Cdegree N - 1 - u + v : ℕ) : ℤ) - j)).trans
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hindex)
  rw [norm_mul]
  calc
    _ ≤ 1 * (2 : ℝ) ^ ((H N : ℤ) - 1 - u - j) :=
      mul_le_mul (Padic.norm_int_le_one _) hk (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem boundaryScalar_norm_le {N u j : ℕ}
    (hu : u < Cdegree N) (hj : j < H N) :
    ‖boundaryScalar N u j‖ ≤
      max ‖-smoothingMoment 0 1‖ (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) := by
  have hthree : ‖(3 : ℚ_[2])‖ ≤ (1 : ℝ) := by
    simpa using Padic.norm_int_le_one (3 : ℤ)
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  have hratio : ‖(3 / 2 : ℚ_[2])‖ ≤ (2 : ℝ) := by
    rw [norm_div, htwo]
    calc
      _ ≤ 1 / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hthree (by norm_num)
      _ = _ := by norm_num
  unfold boundaryScalar
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_trans (norm_nonneg _) (le_max_left _ _))
  intro v hv
  have hi := exceptionalScalar_index_lt_H hu (Finset.mem_range.mp hv)
  have hz := zetaRat_norm_le (H N) (Cdegree N - 1 - u + v) j hi hj
  have hdelta : ‖(-smoothingMoment 0 1) *
      (if Cdegree N - 1 - u + v = j then (1 : ℚ_[2]) else 0)‖ ≤
      ‖-smoothingMoment 0 1‖ := by
    split_ifs <;> simp
  have hzeta : ‖(3 / 2 : ℚ_[2]) *
      (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2])‖ ≤
      2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N)) := by
    rw [norm_mul]
    exact mul_le_mul hratio hz (norm_nonneg _) (by norm_num)
  have hinner : ‖(-smoothingMoment 0 1) *
      (if Cdegree N - 1 - u + v = j then (1 : ℚ_[2]) else 0) -
      (3 / 2 : ℚ_[2]) * (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2])‖ ≤
      max ‖-smoothingMoment 0 1‖ (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) := by
    have hsum := Padic.nonarchimedean
      ((-smoothingMoment 0 1) *
        (if Cdegree N - 1 - u + v = j then (1 : ℚ_[2]) else 0))
      (-((3 / 2 : ℚ_[2]) * (zetaRat (Cdegree N - 1 - u + v) j : ℚ_[2])))
    rw [← sub_eq_add_neg, norm_neg] at hsum
    exact hsum.trans (max_le_max hdelta hzeta)
  rw [norm_mul]
  calc
    _ ≤ 1 * max ‖-smoothingMoment 0 1‖
        (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) :=
      mul_le_mul (Padic.norm_int_le_one _) hinner (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RawMinorCoefficientExpansion
namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open Classical
open scoped BigOperators

abbrev rawCoefficientIndex (N : ℕ) (t : Fin 3) :=
  Fin (if t = 0 then 1 else Cdegree N)

def rawCoefficientVector (N r j : ℕ) (t : Fin 3) (u : ℕ) : ℚ_[2] :=
  if t = 0 then smoothingColumn N r j
  else if t = 1 then ((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2])
  else ((Int.sign (rowOffset N r) *
    (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2])

def rawCoefficientScalar (z : ℚ) (N j : ℕ) (t : Fin 3) (u : ℕ) : ℚ_[2] :=
  if t = 0 then 1
  else if t = 1 then exceptionScalar z N u j
  else boundaryScalar N u j

def rawCoefficientMinor (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) : ℚ_[2] :=
  Matrix.det (Matrix.of fun r k : Fin (n N) =>
    rawCoefficientVector N r.val (c k).val (τ k) (u k).val)

theorem rawColumnTerm_coefficient_expansion (z : ℚ) (N r j : ℕ) (t : Fin 3) :
    rawColumnTerm z N r j t =
      ∑ u : rawCoefficientIndex N t,
        rawCoefficientVector N r j t u.val * rawCoefficientScalar z N j t u.val := by
  by_cases h0 : t = 0
  · subst t
    simp [rawColumnTerm, rawCoefficientIndex, rawCoefficientVector, rawCoefficientScalar]
  · by_cases h1 : t = 1
    · subst t
      have hsum := Fin.sum_univ_eq_sum_range
        (fun u : ℕ => ((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2]) *
          exceptionScalar z N u j) (Cdegree N)
      simpa [rawColumnTerm, rawCoefficientIndex, rawCoefficientVector,
        rawCoefficientScalar] using
        (exceptionColumn_eq_sum_exceptionScalar z N r j).trans hsum.symm
    · have h2 : t = 2 := by omega
      subst t
      have hsum := Fin.sum_univ_eq_sum_range
        (fun u : ℕ => ((Int.sign (rowOffset N r) *
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2]) *
            boundaryScalar N u j) (Cdegree N)
      simpa [rawColumnTerm, rawCoefficientIndex, rawCoefficientVector,
        rawCoefficientScalar] using
        (boundaryColumn_eq_sum_boundaryScalar N r j).trans hsum.symm

theorem rawColumnMinor_coefficient_expansion (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3) :
    Matrix.det (Matrix.of fun r k : Fin (n N) =>
      rawColumnTerm z N r.val (c k).val (τ k)) =
      ∑ u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k),
        (∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
          rawCoefficientMinor N c τ u := by
  classical
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => rawColumnTerm z N r.val (c k).val (τ k)) =
        (Matrix.of fun r k : Fin (n N) =>
          ∑ a : rawCoefficientIndex N (τ k),
            rawCoefficientVector N r.val (c k).val (τ k) a.val *
              rawCoefficientScalar z N (c k).val (τ k) a.val) := by
    ext r k
    simp only [Matrix.of_apply, rawColumnTerm_coefficient_expansion]
  rw [hmatrix]
  calc
    _ = ∑ u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k),
        ∑ σ : Equiv.Perm (Fin (n N)), ((Equiv.Perm.sign σ : ℤ) : ℚ_[2]) *
          ∏ k : Fin (n N),
            rawCoefficientVector N (σ k).val (c k).val (τ k) (u k).val *
              rawCoefficientScalar z N (c k).val (τ k) (u k).val := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [rawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem rawCoefficientMinor_eq_zero_of_repeat_exception (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    {i j : Fin (n N)} (hne : i ≠ j) (hi : τ i = 1) (hj : τ j = 1)
    (hu : (u i).val = (u j).val) : rawCoefficientMinor N c τ u = 0 := by
  unfold rawCoefficientMinor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, rawCoefficientVector, hi, hj, hu]

theorem rawCoefficientMinor_eq_zero_of_repeat_boundary (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    {i j : Fin (n N)} (hne : i ≠ j) (hi : τ i = 2) (hj : τ j = 2)
    (hu : (u i).val = (u j).val) : rawCoefficientMinor N c τ u = 0 := by
  unfold rawCoefficientMinor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, rawCoefficientVector, hi, hj, hu]

theorem rawCoefficientMinor_exception_injOn (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    (hdet : rawCoefficientMinor N c τ u ≠ 0) :
    Set.InjOn (fun k => (u k).val) {k | τ k = 1} := by
  intro i hi j hj hu
  by_contra hne
  exact hdet (rawCoefficientMinor_eq_zero_of_repeat_exception N c τ u hne hi hj hu)

theorem rawCoefficientMinor_boundary_injOn (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    (hdet : rawCoefficientMinor N c τ u ≠ 0) :
    Set.InjOn (fun k => (u k).val) {k | τ k = 2} := by
  intro i hi j hj hu
  by_contra hne
  exact hdet (rawCoefficientMinor_eq_zero_of_repeat_boundary N c τ u hne hi hj hu)


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.UnconvolvedVectorBounds
namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

theorem unconvolvedP_entry_norm_le (N r u : ℕ) :
    ‖((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2])‖ ≤
      (2 : ℝ) ^ (1 - (u : ℤ)) := by
  calc
    _ ≤ 1 / (2 : ℝ) ^ (u - 1) :=
      padic_two_norm_int_le_of_pow_dvd
        (chebyshev_T_coeff_two_pow_dvd (rowDistance N r : ℤ) u)
    _ = (2 : ℝ) ^ (-((u - 1 : ℕ) : ℤ)) := by
      simp only [zpow_neg, zpow_natCast, one_div]
    _ ≤ (2 : ℝ) ^ (1 - (u : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)

theorem unconvolvedD_entry_norm_le (N r u : ℕ) :
    ‖((Int.sign (rowOffset N r) *
      (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2])‖ ≤
      (2 : ℝ) ^ (-(u : ℤ)) := by
  have hdiv := dvd_mul_of_dvd_right
    (chebyshev_U_coeff_two_pow_dvd ((rowDistance N r : ℤ) - 1) u)
    (Int.sign (rowOffset N r))
  simpa only [zpow_neg, zpow_natCast, one_div] using
    padic_two_norm_int_le_of_pow_dvd hdiv

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.RawCoefficientEntryBound
namespace OAI


noncomputable section

namespace InternalCatalan

def discrepancyNormFactor (z : ℚ) : ℝ :=
  max 1 (max ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ ‖smoothingMoment 0 1‖)

theorem one_le_discrepancyNormFactor (z : ℚ) : 1 ≤ discrepancyNormFactor z :=
  le_max_left _ _

theorem discrepancyNormFactor_nonneg (z : ℚ) : 0 ≤ discrepancyNormFactor z :=
  zero_le_one.trans (one_le_discrepancyNormFactor z)

theorem rawCoefficientEntry_norm_le (z : ℚ) {N r j : ℕ}
    (hN : 0 < N) (hj : j < L N) (t : Fin 3) (u : rawCoefficientIndex N t) :
    ‖rawCoefficientVector N r j t u.val * rawCoefficientScalar z N j t u.val‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) *
        (2 : ℝ) ^ (-(if t = 0 then (Cdegree N : ℤ)
          else if t = 1 then 2 * (u.val : ℤ) + (j : ℤ) - (H N : ℤ)
          else (u.val : ℤ))) := by
  have hjH : j < H N := by unfold L H at *; omega
  have hHone : 1 ≤ (H N : ℝ) := by
    have hH : 1 ≤ H N := by unfold H; omega
    exact_mod_cast hH
  have hHsq : 1 ≤ (H N : ℝ) ^ 2 := by
    nlinarith only [hHone, sq_nonneg ((H N : ℝ) - 1)]
  have hFone := one_le_discrepancyNormFactor z
  have hFzero := discrepancyNormFactor_nonneg z
  have hFcommon : discrepancyNormFactor z ≤
      8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by
    nlinarith only [hFone, mul_le_mul_of_nonneg_left hHsq hFzero]
  have hScommon : 8 * (H N : ℝ) ^ 2 ≤
      8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hFone (sq_nonneg (H N : ℝ))]
  have he1 : ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ ≤ discrepancyNormFactor z :=
    (le_max_left _ _).trans (le_max_right _ _)
  have he2 : ‖smoothingMoment 0 1‖ ≤ discrepancyNormFactor z :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases h0 : t = 0
  · simp only [rawCoefficientVector, rawCoefficientScalar, h0, if_pos, mul_one]
    have hs := (smoothingColumn_norm_le N r j hjH).trans
      (div_le_div_of_nonneg_right hScommon (by positivity :
        (0 : ℝ) ≤ (2 : ℝ) ^ Cdegree N))
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using hs
  · have hu : u.val < Cdegree N := by
      simpa only [rawCoefficientIndex, if_neg h0] using u.isLt
    by_cases h1 : t = 1
    · simp only [rawCoefficientVector, rawCoefficientScalar, h1, ite_true]
      rw [norm_mul]
      calc
        _ ≤ (2 : ℝ) ^ (1 - (u.val : ℤ)) *
            (‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ *
              (2 : ℝ) ^ ((H N : ℤ) - 1 - u.val - j)) :=
          mul_le_mul (unconvolvedP_entry_norm_le N r u.val)
            (exceptionScalar_norm_le z j hu) (norm_nonneg _) (by positivity)
        _ = ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ *
            (2 : ℝ) ^ (-(2 * (u.val : ℤ) + j - (H N : ℤ))) := by
          rw [mul_left_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have he : (1 - (u.val : ℤ)) + ((H N : ℤ) - 1 - u.val - j) =
              -(2 * (u.val : ℤ) + j - (H N : ℤ)) := by ring
          rw [he]
        _ ≤ _ := mul_le_mul_of_nonneg_right (he1.trans hFcommon) (by positivity)
    · have hp : (2 : ℝ) ^ Nat.log 2 (H N) ≤ (H N : ℝ) + 1 := by
        exact_mod_cast Nat.pow_log_le_add_one 2 (H N)
      have hp' : (2 : ℝ) ^ Nat.log 2 (H N) ≤ 2 * (H N : ℝ) := by
        linarith only [hp, hHone]
      have hlog : 2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N)) ≤ 8 * (H N : ℝ) ^ 2 := by
        have hp2 := mul_nonneg (sub_nonneg.mpr hp')
          (show 0 ≤ 2 * (H N : ℝ) + (2 : ℝ) ^ Nat.log 2 (H N) by positivity)
        rw [Nat.mul_comm 2 (Nat.log 2 (H N)), pow_mul]
        nlinarith only [hp2]
      have hBcommon : max ‖-smoothingMoment 0 1‖
          (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) ≤
          8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by
        rw [norm_neg]
        exact max_le (he2.trans hFcommon) (hlog.trans hScommon)
      simp only [rawCoefficientVector, rawCoefficientScalar, h0, h1, ite_false]
      rw [norm_mul]
      calc
        _ ≤ (2 : ℝ) ^ (-(u.val : ℤ)) *
            (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) :=
          mul_le_mul (unconvolvedD_entry_norm_le N r u.val)
            ((boundaryScalar_norm_le hu hjH).trans hBcommon)
            (norm_nonneg _) (by positivity)
        _ = _ := mul_comm _ _

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RawMinorCoefficientNorm
namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rawCoefficientTerm_eq_det (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) :
    (∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
        rawCoefficientMinor N c τ u =
      Matrix.det (Matrix.of fun r k : Fin (n N) =>
        rawCoefficientVector N r.val (c k).val (τ k) (u k).val *
          rawCoefficientScalar z N (c k).val (τ k) (u k).val) := by
  classical
  simp only [rawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.prod_mul_distrib]
  ring

private theorem prod_two_zpow_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    (∏ k, (2 : ℝ) ^ (-v k)) = (2 : ℝ) ^ (-(∑ k, v k)) := by
  classical
  calc
    _ = ∏ k, (2 : ℝ) ^ (((-v k) : ℤ) : ℝ) := by
      simp only [Real.rpow_intCast]
    _ = (2 : ℝ) ^ (∑ k, (((-v k) : ℤ) : ℝ)) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = (2 : ℝ) ^ (((-(∑ k, v k)) : ℤ) : ℝ) := by
      simp only [Int.cast_neg, Int.cast_sum, Finset.sum_neg_distrib]
    _ = _ := Real.rpow_intCast _ _

theorem rawCoefficientTerm_norm_le_zpow (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) :
    ‖(∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
        rawCoefficientMinor N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ (-(∑ k : Fin (n N),
          if τ k = 0 then (Cdegree N : ℤ)
          else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (H N : ℤ)
          else ((u k).val : ℤ))) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawCoefficientTerm_eq_det]
  calc
    _ ≤ ∏ k : Fin (n N),
        (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) *
          (2 : ℝ) ^ (-(if τ k = 0 then (Cdegree N : ℤ)
            else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (H N : ℤ)
            else ((u k).val : ℤ))) := by
      apply padic_two_det_norm_le_prod_column
      · intro k
        positivity
      · intro r k
        exact rawCoefficientEntry_norm_le z hN
          (Finset.mem_Ico.mp (c k).property).2 (τ k) (u k)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, prod_two_zpow_neg]

theorem rawCoefficientTerm_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) (hc : Function.Injective c)
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) :
    ‖(∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
        rawCoefficientMinor N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  have hF := discrepancyNormFactor_nonneg z
  by_cases hz : rawCoefficientMinor N c τ u = 0
  · rw [hz, mul_zero, norm_zero]
    positivity
  have hj : Function.Injective (fun k => (c k).val) := by
    intro i j hij
    exact hc (Subtype.ext hij)
  have hp := twoAdic_selector_zpow_le N τ (fun k => (u k).val) (fun k => (c k).val)
    (rawCoefficientMinor_exception_injOn N c τ u hz)
    (rawCoefficientMinor_boundary_injOn N c τ u hz) hj
    (fun k => (Finset.mem_Ico.mp (c k).property).1)
  exact (rawCoefficientTerm_norm_le_zpow z hN c τ u).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

theorem rawColumnMinor_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) (hc : Function.Injective c)
    (τ : Fin (n N) → Fin 3) :
    ‖Matrix.det (Matrix.of fun r k : Fin (n N) =>
      rawColumnTerm z N r.val (c k).val (τ k))‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawColumnMinor_coefficient_expansion]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro u hu
  exact rawCoefficientTerm_norm_le z hN c hc τ u

theorem rawMinorRat_two_adic_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) (hc : Function.Injective c) :
    ‖(rawMinorRat z N c : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawMinorRat_two_adic_column_expansion z hN c]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro τ hτ
  exact rawColumnMinor_norm_le z hN c hc τ

theorem determinantRat_two_adic_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N) :
    ‖(determinantRat z N : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [determinantRat_eq_sum_raw_minors]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro c hc
  rw [norm_mul]
  calc
    _ ≤ 1 * ((8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ))) :=
      mul_le_mul (Padic.norm_int_le_one _)
        (rawMinorRat_two_adic_norm_le z hN c (Finset.mem_filter.mp hc).2)
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.FinitePlacePartialAssembly
namespace OAI


noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology

theorem determinantRat_two_adic_valuation_lower (z : ℚ) {N : ℕ} (hN : 0 < N)
    (hd : determinantRat z N ≠ 0) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 - 2 * (n N : ℝ) -
        (n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ≤
      (padicValRat 2 (determinantRat z N) : ℝ) := by
  have hd₂ : (determinantRat z N : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hH : 0 < (H N : ℝ) := by unfold H; positivity
  have hA : 0 < 8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by positivity
  have hApow : (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N ≠ 0 :=
    ne_of_gt (pow_pos hA _)
  have hE : (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (norm_pos_iff.mpr hd₂) (determinantRat_two_adic_norm_le z hN)
  rw [Padic.norm_eq_zpow_neg_valuation hd₂, Padic.valuation_ratCast] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [← Real.rpow_intCast, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1),
    Real.logb_mul hApow hE, Real.logb_pow,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hl
  simp only [Int.cast_neg] at hl
  linarith only [hl]

theorem tendsto_twoAdic_log_error (z : ℚ) :
    Tendsto (fun N : ℕ =>
      (2 + Real.logb 2 (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2)) / (n N : ℝ))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ) / (48 * (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 48 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hs := (hi.const_mul
    ((2 + Real.logb 2 (8 * discrepancyNormFactor z * (65 : ℝ) ^ 2)) / 48)).add
      (hl.const_mul 2)
  simp only [mul_zero, add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hconst : 8 * discrepancyNormFactor z * (65 : ℝ) ^ 2 ≠ 0 := by positivity
  have hfactor : 8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 =
      (8 * discrepancyNormFactor z * (65 : ℝ) ^ 2) * (N : ℝ) ^ 2 := by
    simp only [H, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hfactor, Real.logb_mul hconst (pow_ne_zero _ hNr), Real.logb_pow]
  simp only [n, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNr]
  ring

theorem determinantRat_two_adic_eventually_lower (z : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(505 / 4608 : ℝ) - ε ≤
        (padicValRat 2 (determinantRat z N) : ℝ) / (n N : ℝ) ^ 2 := by
  have he : ∀ᶠ N : ℕ in atTop,
      (2 + Real.logb 2 (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2)) / (n N : ℝ) < ε :=
    (tendsto_order.mp (tendsto_twoAdic_log_error z)).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  intro hd
  have hn : 0 < (n N : ℝ) := by unfold n; positivity
  have herr := mul_le_mul_of_nonneg_left
    (le_of_lt ((div_lt_iff₀ hn).mp heN)) (le_of_lt hn)
  have hv := determinantRat_two_adic_valuation_lower z hN hd
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith only [herr, hv]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology BigOperators

def largeOddPrimeContribution (z : ℚ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 (H N)).filter
      (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
    (padicValRat p (determinantRat z N) : ℝ) * Real.log p

theorem log_abs_determinantRat_place_split_lower (z : ℚ) {N : ℕ}
    (hN : 0 < N) (hz : z.den ≤ H N) (hdet : determinantRat z N ≠ 0) :
    (padicValRat 2 (determinantRat z N) : ℝ) * Real.log 2 +
      smallOddPrimeContribution z N + largeOddPrimeContribution z N ≤
      Real.log |(determinantRat z N : ℝ)| := by
  have h := log_abs_determinantRat_truncated_lower z hN hz hdet
  rw [oddPrimeContribution_split z hN] at h
  simpa only [largeOddPrimeContribution, add_assoc] using h

theorem determinantRat_without_large_primes_eventually_lower (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(505 / 4608 : ℝ) * Real.log 2 - ε ≤
        (Real.log |(determinantRat z N : ℝ)| - largeOddPrimeContribution z N) /
          (n N : ℝ) ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he2 : 0 < ε / (2 * Real.log 2) := by positivity
  have htwo := determinantRat_two_adic_eventually_lower z he2
  have hsmall := smallOddPrimeContribution_eventually_lower z
    (show 0 < ε / 2 by positivity)
  filter_upwards [htwo, hsmall, eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop z.den] with N htwoN hsmallN hN hden
  intro hdet
  have hz : z.den ≤ H N := by unfold H; omega
  have hn : 0 < (n N : ℝ) := by unfold n; positivity
  have hn2 : 0 < (n N : ℝ) ^ 2 := sq_pos_of_pos hn
  have ht := mul_le_mul_of_nonneg_right (htwoN hdet) (le_of_lt hlog)
  have herr : ε / (2 * Real.log 2) * Real.log 2 = ε / 2 := by
    field_simp [ne_of_gt hlog]
  have hsplit := div_le_div_of_nonneg_right
    (log_abs_determinantRat_place_split_lower z hN hz hdet) (le_of_lt hn2)
  rw [add_div, add_div] at hsplit
  rw [sub_mul, herr] at ht
  rw [sub_div]
  have heq : (padicValRat 2 (determinantRat z N) : ℝ) * Real.log 2 /
      (n N : ℝ) ^ 2 =
      ((padicValRat 2 (determinantRat z N) : ℝ) / (n N : ℝ) ^ 2) * Real.log 2 := by
    ring
  rw [heq] at hsplit
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.ZetaFive.Identities.WeightedPNT
namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

noncomputable def primeIntervalSum (x y : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with p.Prime, Real.log (p : ℝ)

theorem mem_primeInterval_iff {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (p : ℕ) :
    p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime ↔
      x < (p : ℝ) ∧ (p : ℝ) ≤ y ∧ p.Prime := by
  simp only [Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt hx, Nat.le_floor_iff (hx.trans hxy), and_assoc]

theorem primeIntervalSum_eq_theta_sub {x y : ℝ} (hxy : x ≤ y) :
    primeIntervalSum x y = Chebyshev.theta y - Chebyshev.theta x := by
  unfold primeIntervalSum Chebyshev.theta
  simp only [Finset.sum_filter]
  have h := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0)
    (Nat.zero_le ⌊x⌋₊) (Nat.floor_le_floor hxy)
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

theorem theta_scaled_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => Chebyshev.theta (c * R) / R) atTop (𝓝 c) := by
  have hscale : Tendsto (fun R : ℝ => c * R) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have h := (hPNT.comp hscale).const_mul c
  simp only [mul_one] at h
  apply h.congr
  intro R
  change c * (Chebyshev.theta (c * R) / (c * R)) = Chebyshev.theta (c * R) / R
  rw [← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hc)]

theorem primeIntervalSum_scaled_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    Tendsto (fun R : ℝ => primeIntervalSum (α * R) (β * R) / R)
      atTop (𝓝 (β - α)) := by
  have h := (theta_scaled_tendsto hPNT (hα.trans hαβ)).sub
    (theta_scaled_tendsto hPNT hα)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [primeIntervalSum_eq_theta_sub (mul_le_mul_of_nonneg_right hαβ.le hR), sub_div]

noncomputable def weightedPrimeIntervalSum (F : ℝ → ℝ) (α β R : ℝ) : ℝ :=
  (∑ p ∈ Finset.Ioc ⌊α * R⌋₊ ⌊β * R⌋₊ with p.Prime,
    F ((p : ℝ) / R) * Real.log (p : ℝ)) / R

theorem weightedPrimeIntervalSum_const (c α β R : ℝ) :
    weightedPrimeIntervalSum (fun _ => c) α β R =
      c * (primeIntervalSum (α * R) (β * R) / R) := by
  simp only [weightedPrimeIntervalSum, primeIntervalSum, ← Finset.mul_sum,
    mul_div_assoc]


noncomputable def finiteStepPrimeSum {ι : Type*} (s : Finset ι)
    (a b weight : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i ∈ s, weight i * (primeIntervalSum (a i * R) (b i * R) / R)

theorem finiteStepPrimeSum_tendsto {ι : Type*} (s : Finset ι)
    (a b weight : ι → ℝ)
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i < b i) :
    Tendsto (finiteStepPrimeSum s a b weight) atTop
      (𝓝 (∑ i ∈ s, weight i * (b i - a i))) := by
  apply tendsto_finsetSum s
  intro i hi
  exact (primeIntervalSum_scaled_tendsto hPNT (ha i hi) (hab i hi)).const_mul (weight i)

end Zeta5.Workers.W14

end OAI

end

section
-- module Solutions.OAICatalan.ZetaFive.Identities.WeightedOrder
namespace OAI

open Finset

namespace Zeta5.Workers.W14

theorem log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast hp.one_lt.le

theorem weightedPrimeIntervalSum_mono
    {F G : ℝ → ℝ} {α β R : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hR : 0 < R)
    (hFG : ∀ x ∈ Set.Ioc α β, F x ≤ G x) :
    weightedPrimeIntervalSum F α β R ≤ weightedPrimeIntervalSum G α β R := by
  unfold weightedPrimeIntervalSum
  apply div_le_div_of_nonneg_right _ hR.le
  apply Finset.sum_le_sum
  intro p hp
  have hmem := (mem_primeInterval_iff (mul_nonneg hα hR.le)
    (mul_le_mul_of_nonneg_right hαβ hR.le) p).mp hp
  apply mul_le_mul_of_nonneg_right _ (log_prime_nonneg hmem.2.2)
  apply hFG
  exact ⟨(lt_div_iff₀ hR).mpr hmem.1, (div_le_iff₀ hR).mpr hmem.2.1⟩


theorem weightedPrimeIntervalSum_bounds
    {F : ℝ → ℝ} {α β R l u : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hR : 0 < R)
    (hF : ∀ x ∈ Set.Ioc α β, l ≤ F x ∧ F x ≤ u) :
    l * (primeIntervalSum (α * R) (β * R) / R) ≤
        weightedPrimeIntervalSum F α β R ∧
      weightedPrimeIntervalSum F α β R ≤
        u * (primeIntervalSum (α * R) (β * R) / R) := by
  constructor
  · simpa only [weightedPrimeIntervalSum_const] using
      weightedPrimeIntervalSum_mono hα hαβ hR (fun x hx => (hF x hx).1)
  · simpa only [weightedPrimeIntervalSum_const] using
      weightedPrimeIntervalSum_mono hα hαβ hR (fun x hx => (hF x hx).2)



end Zeta5.Workers.W14

end OAI

end

section
-- module Solutions.OAICatalan.ZetaFive.Identities.RiemannSqueeze
namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14





theorem weightedPrimeIntervalSum_add_adjacent (F : ℝ → ℝ) {α β γ R : ℝ}
    (hαβ : α ≤ β) (hβγ : β ≤ γ) (hR : 0 ≤ R) :
    weightedPrimeIntervalSum F α β R + weightedPrimeIntervalSum F β γ R =
      weightedPrimeIntervalSum F α γ R := by
  unfold weightedPrimeIntervalSum
  simp only [Finset.sum_filter]
  rw [← add_div]
  congr 1
  exact Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then F ((p : ℝ) / R) * Real.log (p : ℝ) else 0)
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hαβ hR))
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hβγ hR))

theorem weightedPrimeIntervalSum_partition (F : ℝ → ℝ) (a : ℕ → ℝ)
    (ha : Monotone a) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∑ i ∈ Finset.range n, weightedPrimeIntervalSum F (a i) (a (i + 1)) R) =
      weightedPrimeIntervalSum F (a 0) (a n) R := by
  induction n with
  | zero => simp [weightedPrimeIntervalSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact weightedPrimeIntervalSum_add_adjacent F (ha (Nat.zero_le n))
      (ha (Nat.le_succ n)) hR

theorem weightedPrimeIntervalSum_partition_bounds
    {n : ℕ} {a l u : ℕ → ℝ} {F : ℝ → ℝ} {R : ℝ}
    (ha : Monotone a) (ha0 : 0 ≤ a 0) (hR : 0 < R)
    (hcell : ∀ i < n, ∀ x ∈ Set.Ioc (a i) (a (i + 1)), l i ≤ F x ∧ F x ≤ u i) :
    finiteStepPrimeSum (Finset.range n) a (fun i => a (i + 1)) l R ≤
        weightedPrimeIntervalSum F (a 0) (a n) R ∧
      weightedPrimeIntervalSum F (a 0) (a n) R ≤
        finiteStepPrimeSum (Finset.range n) a (fun i => a (i + 1)) u R := by
  rw [← weightedPrimeIntervalSum_partition F a ha n hR.le]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact (weightedPrimeIntervalSum_bounds (ha0.trans (ha (Nat.zero_le i)))
      (ha (Nat.le_succ i)) hR (hcell i (Finset.mem_range.mp hi))).1
  · apply Finset.sum_le_sum
    intro i hi
    exact (weightedPrimeIntervalSum_bounds (ha0.trans (ha (Nat.zero_le i)))
      (ha (Nat.le_succ i)) hR (hcell i (Finset.mem_range.mp hi))).2



theorem weightedPrimeIntervalSum_tendsto_of_darboux
    {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (_hαβ : α < β)
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    (hDarboux : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (a l u : ℕ → ℝ),
      Monotone a ∧ a 0 = α ∧ a n = β ∧
      (∀ i < n, a i < a (i + 1)) ∧
      (∀ i < n, ∀ x ∈ Set.Ioc (a i) (a (i + 1)), l i ≤ F x ∧ F x ≤ u i) ∧
      (∫ x in α..β, F x) - ε < ∑ i ∈ Finset.range n, l i * (a (i + 1) - a i) ∧
      (∑ i ∈ Finset.range n, u i * (a (i + 1) - a i)) < (∫ x in α..β, F x) + ε) :
    Tendsto (weightedPrimeIntervalSum F α β) atTop (𝓝 (∫ x in α..β, F x)) := by
  apply tendsto_order.mpr
  constructor
  · intro v hv
    obtain ⟨n, a, l, u, ha, ha0, han, hs, hb, hl, hu⟩ :=
      hDarboux (((∫ x in α..β, F x) - v) / 2) (by linarith)
    have hp : 0 < a 0 := ha0.symm ▸ hα
    have ht := finiteStepPrimeSum_tendsto (Finset.range n) a (fun i => a (i + 1)) l
      hPNT (fun i _ => hp.trans_le (ha (Nat.zero_le i)))
      (fun i hi => hs i (Finset.mem_range.mp hi))
    have hv' : v < ∑ i ∈ Finset.range n, l i * (a (i + 1) - a i) := by linarith
    filter_upwards [(tendsto_order.mp ht).1 v hv', eventually_gt_atTop (0 : ℝ)] with R hr hR
    have hbound := (weightedPrimeIntervalSum_partition_bounds ha hp.le hR hb).1
    rw [ha0, han] at hbound
    exact hr.trans_le hbound
  · intro v hv
    obtain ⟨n, a, l, u, ha, ha0, han, hs, hb, hl, hu⟩ :=
      hDarboux ((v - (∫ x in α..β, F x)) / 2) (by linarith)
    have hp : 0 < a 0 := ha0.symm ▸ hα
    have ht := finiteStepPrimeSum_tendsto (Finset.range n) a (fun i => a (i + 1)) u
      hPNT (fun i _ => hp.trans_le (ha (Nat.zero_le i)))
      (fun i hi => hs i (Finset.mem_range.mp hi))
    have hv' : (∑ i ∈ Finset.range n, u i * (a (i + 1) - a i)) < v := by linarith
    filter_upwards [(tendsto_order.mp ht).2 v hv', eventually_gt_atTop (0 : ℝ)] with R hr hR
    have hbound := (weightedPrimeIntervalSum_partition_bounds ha hp.le hR hb).2
    rw [ha0, han] at hbound
    exact hbound.trans_lt hr

end Zeta5.Workers.W14

end OAI

end

section
-- module Solutions.OAICatalan.ZetaFive.Arithmetic.LargePrimeWeighted
namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

noncomputable def affineGrid (a b : ℝ) (n i : ℕ) : ℝ :=
  a + (b - a) / n * i



theorem grid_zero (a b : ℝ) (n : ℕ) : affineGrid a b n 0 = a := by
  simp [affineGrid]

theorem grid_end (a b : ℝ) {n : ℕ} (hn : 0 < n) : affineGrid a b n n = b := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold affineGrid
  rw [div_mul_cancel₀ _ hn']
  ring

theorem grid_width (a b : ℝ) (n i : ℕ) :
    affineGrid a b n (i + 1) - affineGrid a b n i = (b - a) / n := by
  simp only [affineGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem grid_strict {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) :
    StrictMono (affineGrid a b n) := by
  intro i j hij
  unfold affineGrid
  exact add_lt_add_of_le_of_lt le_rfl
    (mul_lt_mul_of_pos_left (by exact_mod_cast hij)
      (div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)))
















end Zeta5.Workers.W14

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.PrimeLimits.ContinuousWeightedPNT
namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

theorem continuous_darboux {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (p l u : ℕ → ℝ),
      Monotone p ∧ p 0 = a ∧ p n = b ∧
      (∀ i < n, p i < p (i + 1)) ∧
      (∀ i < n, ∀ x ∈ Set.Ioc (p i) (p (i + 1)), l i ≤ F x ∧ F x ≤ u i) ∧
      (∫ x in a..b, F x) - ε < ∑ i ∈ Finset.range n, l i * (p (i + 1) - p i) ∧
      (∑ i ∈ Finset.range n, u i * (p (i + 1) - p i)) < (∫ x in a..b, F x) + ε := by
  intro ε hε
  let η := ε / (4 * (b - a))
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, huv⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((b - a) / δ))
  have hn0 : 0 < n := by
    have h : (0 : ℝ) < n := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hn)
    exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmesh : (b - a) / n < δ := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hδ).mp ((le_max_right (1 : ℝ) ((b - a) / δ)).trans_lt hn)
    nlinarith
  let p := affineGrid a b n
  let l := fun i => F (p i) - η
  let u := fun i => F (p i) + η
  have hp : StrictMono p := grid_strict hab hn0
  have hp0 : p 0 = a := grid_zero a b n
  have hpn : p n = b := grid_end a b hn0
  have hsub : ∀ i < n, Set.Icc (p i) (p (i + 1)) ⊆ Set.Icc a b := by
    intro i hi x hx
    have hlo := hp.monotone (Nat.zero_le i)
    have hhi := hp.monotone (show i + 1 ≤ n by omega)
    rw [hp0] at hlo
    rw [hpn] at hhi
    exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩
  have hcell : ∀ i < n, ∀ x ∈ Set.Icc (p i) (p (i + 1)), l i ≤ F x ∧ F x ≤ u i := by
    intro i hi x hx
    have hpi : p i ∈ Set.Icc a b := hsub i hi ⟨le_rfl, (hp (Nat.lt_succ_self i)).le⟩
    have hd : dist x (p i) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      have hw : p (i + 1) - p i = (b - a) / n := grid_width a b n i
      linarith [hx.2]
    have h := huv x (hsub i hi hx) (p i) hpi hd
    rw [Real.dist_eq] at h
    have hh := abs_lt.mp h
    dsimp [l, u]
    constructor <;> linarith
  have hint : ∀ i < n, IntervalIntegrable F MeasureTheory.volume (p i) (p (i + 1)) := by
    intro i hi
    exact ContinuousOn.intervalIntegrable_of_Icc (hp (Nat.lt_succ_self i)).le
      (hF.mono (hsub i hi))
  have hsumInt : (∑ i ∈ Finset.range n, ∫ x in p i..p (i + 1), F x) = ∫ x in a..b, F x := by
    simpa only [hp0, hpn] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hlo : (∑ i ∈ Finset.range n, l i * (p (i + 1) - p i)) ≤ ∫ x in a..b, F x := by
    rw [← hsumInt]
    apply Finset.sum_le_sum
    intro i hi
    have h := intervalIntegral.integral_mono_on (hp (Nat.lt_succ_self i)).le
      (continuous_const.intervalIntegrable (p i) (p (i + 1)) : IntervalIntegrable (fun _ : ℝ => l i)
        MeasureTheory.volume (p i) (p (i + 1))) (hint i (Finset.mem_range.mp hi))
      (fun x hx => (hcell i (Finset.mem_range.mp hi) x hx).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hhi : (∫ x in a..b, F x) ≤ ∑ i ∈ Finset.range n, u i * (p (i + 1) - p i) := by
    rw [← hsumInt]
    apply Finset.sum_le_sum
    intro i hi
    have h := intervalIntegral.integral_mono_on (hp (Nat.lt_succ_self i)).le
      (hint i (Finset.mem_range.mp hi))
      (continuous_const.intervalIntegrable (p i) (p (i + 1)) : IntervalIntegrable (fun _ : ℝ => u i)
        MeasureTheory.volume (p i) (p (i + 1)))
      (fun x hx => (hcell i (Finset.mem_range.mp hi) x hx).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hgap : (∑ i ∈ Finset.range n, u i * (p (i + 1) - p i)) -
      (∑ i ∈ Finset.range n, l i * (p (i + 1) - p i)) = 2 * η * (b - a) := by
    rw [← Finset.sum_sub_distrib]
    have heq : ∀ i : ℕ, u i * (p (i + 1) - p i) - l i * (p (i + 1) - p i) =
        (2 * η) * (p (i + 1) - p i) := by intro i; dsimp [u, l]; ring
    simp_rw [heq]
    rw [← Finset.mul_sum, Finset.sum_range_sub, hp0, hpn]
  have hsmall : 2 * η * (b - a) < ε := by
    dsimp [η]
    have hbane : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have heq : 2 * (ε / (4 * (b - a))) * (b - a) = ε / 2 := by field_simp [hbane]; ring
    rw [heq]
    linarith
  refine ⟨n, p, l, u, hp.monotone, hp0, hpn, fun i _ => hp (Nat.lt_succ_self i),
    fun i hi x hx => hcell i hi x ⟨hx.1.le, hx.2⟩, ?_, ?_⟩ <;> linarith

theorem continuous_weightedPrime_tendsto {F : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hF : ContinuousOn F (Set.Icc a b))
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) :=
  weightedPrimeIntervalSum_tendsto_of_darboux ha hab hPNT (continuous_darboux hab hF)


end Zeta5.Workers.W14

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.PrimeLimits.ImportedPNTCoreBridge
/-! Port note (prove2.me): the openai/math original imports `PrimeNumberTheoremAnd.Catalan.Consequences`
for `ψ(x) ~ x` and `θ(x) ~ x`. The platform has only Mathlib, so this module takes the prime number
theorem in the form `ψ(x)/x → 1` from the published, Proved prove2.me statement
`ZetaNine.HarmonicStability.psi_pnt_rate`, and derives `θ(x)/x → 1` from it with Mathlib's
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`. The exported statements are unchanged. -/

namespace OAI


noncomputable section
namespace Zeta5.W12.ImportedPNTCoreBridge
open Filter Asymptotics
open scoped Topology BigOperators



theorem psi_ratio_tendsto_one :
    Tendsto (fun R : ℝ => Chebyshev.psi R / R) atTop (𝓝 1) :=
  ZetaNine.HarmonicStability.psi_pnt_rate

/-- `(2 √x · log x) / x → 0`. -/
theorem sqrt_mul_log_div_tendsto_zero :
    Tendsto (fun R : ℝ => 2 * √R * Real.log R / R) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have h2 := h.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [← Real.sqrt_eq_rpow]
  have hs : 0 < √R := Real.sqrt_pos.mpr hR
  have hsq : √R * √R = R := Real.mul_self_sqrt hR.le
  have e : Real.log R / √R = √R * Real.log R / R := by
    rw [div_eq_div_iff hs.ne' hR.ne']
    linear_combination Real.log R * hsq.symm
  rw [e]
  ring

theorem theta_ratio_tendsto_one :
    Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1) := by
  have hdiff : Tendsto (fun R : ℝ => (Chebyshev.psi R - Chebyshev.theta R) / R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ sqrt_mul_log_div_tendsto_zero
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < R)]
    exact div_le_div_of_nonneg_right (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hR) (by linarith)
  have := psi_ratio_tendsto_one.sub hdiff
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  field_simp
  ring


end Zeta5.W12.ImportedPNTCoreBridge

end
end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeLossNormalization
namespace OAI

section

open Filter
open scoped Topology BigOperators
open Zeta5.Workers.W14
open Zeta5.W12.ImportedPNTCoreBridge

namespace InternalCatalan

theorem oddPrimeLoss_weighted_0_25 (R : ℝ) (hR : 0 < R) :
    weightedPrimeIntervalSum oddPrimeLoss 0 25 R =
      96 * (Chebyshev.theta (25 * R) / R) := by
  have hconstant : weightedPrimeIntervalSum oddPrimeLoss 0 25 R =
      weightedPrimeIntervalSum (fun _ => 96) 0 25 R := by
    unfold weightedPrimeIntervalSum
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hupper : p ≤ ⌊(25 : ℝ) * R⌋₊ :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    have hreal : (p : ℝ) ≤ 25 * R :=
      (Nat.le_floor_iff (by positivity : 0 ≤ (25 : ℝ) * R)).mp hupper
    rw [oddPrimeLoss_of_le_25 _ ((div_le_iff₀ hR).mpr hreal)]
  rw [hconstant, weightedPrimeIntervalSum_const]
  simp only [primeIntervalSum, Chebyshev.theta, zero_mul, Nat.floor_zero]

theorem oddPrimeLoss_weighted_tendsto_real :
    Tendsto (weightedPrimeIntervalSum oddPrimeLoss 0 65)
      atTop (𝓝 (8609 / 2 : ℝ)) := by
  have hfirst := (theta_scaled_tendsto theta_ratio_tendsto_one
    (by norm_num : (0 : ℝ) < 25)).const_mul (96 : ℝ)
  have hlast := continuous_weightedPrime_tendsto
    (by norm_num : (0 : ℝ) < 25) (by norm_num : (25 : ℝ) < 65)
    (continuous_oddPrimeLoss.continuousOn : ContinuousOn oddPrimeLoss (Set.Icc 25 65))
    theta_ratio_tendsto_one
  rw [integral_oddPrimeLoss_25_65] at hlast
  have hcombined := hfirst.add hlast
  norm_num at hcombined
  apply hcombined.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simpa only [oddPrimeLoss_weighted_0_25 R hR] using
    (weightedPrimeIntervalSum_add_adjacent oddPrimeLoss
      (by norm_num : (0 : ℝ) ≤ 25) (by norm_num : (25 : ℝ) ≤ 65) hR.le)

theorem oddPrimeLoss_prime_sum_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ Finset.Ioc 0 (65 * N) with p.Prime,
        oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / N)
      atTop (𝓝 (8609 / 2 : ℝ)) := by
  have h := oddPrimeLoss_weighted_tendsto_real.comp tendsto_natCast_atTop_atTop
  have hfloor (N : ℕ) : ⌊(65 : ℝ) * N⌋₊ = 65 * N := by
    rw [show (65 : ℝ) * N = ((65 * N : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
    exact Nat.floor_natCast _
  simpa only [Function.comp_def, weightedPrimeIntervalSum, zero_mul,
    Nat.floor_zero, hfloor] using h

end InternalCatalan

end

section

open Filter
open scoped Topology BigOperators
open Zeta5.Workers.W14

namespace InternalCatalan

noncomputable def removedPrimeLoss (N : ℕ) : ℝ :=
  (∑ p ∈ (Finset.Ioc 0 (H N)).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ 2 * Real.sqrt (H N)),
    oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / N

theorem removedPrimeLoss_nonneg (N : ℕ) : 0 ≤ removedPrimeLoss N := by
  unfold removedPrimeLoss
  apply div_nonneg _ (Nat.cast_nonneg N)
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (oddPrimeLoss_mem_Icc _).1
    (log_prime_nonneg (Finset.mem_filter.mp hp).2.1)

theorem removedPrimeLoss_le (N : ℕ) :
    removedPrimeLoss N ≤
      (96 * Real.log 4 * 2) * (Real.sqrt (H N) / N) := by
  let y : ℝ := 2 * Real.sqrt (H N)
  let s := (Finset.Ioc 0 (H N)).filter
    (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ y)
  let t := (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hsub : s ⊆ t := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, hprime, hcut⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hpI).1,
        (Nat.le_floor_iff hy).mpr hcut⟩, hprime⟩
  have hsum : (∑ p ∈ s, oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) ≤
      96 * Chebyshev.theta y := by
    calc
      _ ≤ ∑ p ∈ s, (96 : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (oddPrimeLoss_mem_Icc _).2
          (log_prime_nonneg (Finset.mem_filter.mp hp).2.1)
      _ ≤ ∑ p ∈ t, (96 : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        exact mul_nonneg (by norm_num)
          (log_prime_nonneg (Finset.mem_filter.mp hp).2)
      _ = 96 * Chebyshev.theta y := by
        simp only [t, Chebyshev.theta, Finset.mul_sum]
  calc
    removedPrimeLoss N ≤ (96 * Chebyshev.theta y) / N :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
    _ ≤ (96 * (Real.log 4 * y)) / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hy) (by norm_num))
        (Nat.cast_nonneg N)
    _ = (96 * Real.log 4 * 2) * (Real.sqrt (H N) / N) := by
      dsimp [y]
      ring

theorem sqrt_H_div_tendsto_zero :
    Tendsto (fun N : ℕ => Real.sqrt (H N) / N) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp hcast)).const_mul (Real.sqrt 65)
  simpa only [H, Nat.cast_mul, Nat.cast_ofNat, Function.comp_def,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 65),
    mul_div_assoc, Real.sqrt_div_self, mul_zero] using h

theorem removedPrimeLoss_tendsto_zero :
    Tendsto removedPrimeLoss atTop (𝓝 0) := by
  have h := sqrt_H_div_tendsto_zero.const_mul (96 * Real.log 4 * 2)
  simp only [mul_zero] at h
  exact squeeze_zero removedPrimeLoss_nonneg removedPrimeLoss_le h

theorem oddPrimeLoss_large_prime_sum_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
          (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / N)
      atTop (𝓝 (8609 / 2 : ℝ)) := by
  have h := oddPrimeLoss_prime_sum_tendsto.sub removedPrimeLoss_tendsto_zero
  simp only [sub_zero] at h
  apply h.congr
  intro N
  apply (sub_eq_iff_eq_add).mpr
  unfold removedPrimeLoss
  rw [← add_div]
  congr 1
  change (∑ p ∈ Finset.Ioc 0 (H N) with p.Prime,
      oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) = _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : p.Prime
  · by_cases hcut : (p : ℝ) ≤ 2 * Real.sqrt (H N)
    · simp [hprime, hcut, not_lt.mpr hcut]
    · simp [hprime, hcut, lt_of_not_ge hcut]
  · simp [hprime]


end InternalCatalan

end


namespace InternalCatalan

open Filter

theorem large_prime_cutoff_square {N p : ℕ}
    (hp : 2 * Real.sqrt (H N) < (p : ℝ)) : 4 * H N < p ^ 2 := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (H N))
  have hs := Real.sqrt_nonneg (H N)
  have hr : (4 : ℝ) * (H N : ℝ) < (p : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (p : ℝ) by positivity]
  exact_mod_cast hr

theorem large_prime_cutoff_gt_fixed {B N p : ℕ} (hB : B ^ 2 ≤ N)
    (hp : 2 * Real.sqrt (H N) < (p : ℝ)) : B < p := by
  have hBH : B ^ 2 ≤ H N := by unfold H; omega
  have hs : (B : ℝ) ≤ Real.sqrt (H N) :=
    (Real.le_sqrt (Nat.cast_nonneg B) (Nat.cast_nonneg (H N))).mpr
      (by exact_mod_cast hBH)
  have hreal : (B : ℝ) < (p : ℝ) := by
    linarith [Real.sqrt_nonneg (H N)]
  exact_mod_cast hreal

theorem large_prime_witness_den_eventually (z : ℚ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      2 * Real.sqrt (H N) < (p : ℝ) → (z.den : ZMod p) ≠ 0 := by
  filter_upwards [eventually_ge_atTop (z.den ^ 2)] with N hN
  intro p hp hz
  have hden := large_prime_cutoff_gt_fixed hN hp
  exact (Nat.not_dvd_of_pos_of_lt z.pos hden)
    ((ZMod.natCast_eq_zero_iff z.den p).mp hz)

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology BigOperators

theorem oddPrimeLoss_large_prime_normalized_tendsto :
    Tendsto (fun N : ℕ =>
      (N : ℝ) *
        (∑ p ∈ (Finset.Ioc 0 (H N)).filter
            (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
          oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / (n N : ℝ) ^ 2)
      atTop (𝓝 (8609 / 4608 : ℝ)) := by
  have hs := oddPrimeLoss_large_prime_sum_tendsto.div_const (2304 : ℝ)
  norm_num only [div_div, show (2 : ℝ) * 2304 = 4608 by norm_num] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [n, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNr]
  ring

theorem oddPrimeLoss_large_prime_normalized_eventually_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) *
        (∑ p ∈ (Finset.Ioc 0 (H N)).filter
            (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
          oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / (n N : ℝ) ^ 2 <
        (8609 / 4608 : ℝ) + ε :=
  (tendsto_order.mp oddPrimeLoss_large_prime_normalized_tendsto).2 _ (by linarith)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.OddPrimeUpperPoolEnumeration
namespace OAI


namespace InternalCatalan

def oddPrimeUpperPairHighSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (p + b N) (p + min (A N) (L N - p))

def oddPrimeUpperCentralSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (max (b N) (H N - p)) (min p (L N))

def oddPrimeUpperRetainedSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (b N) (L N) \
    (oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N)

def oddPrimeUpperExceptionalSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (L N - p) (min (b N) (H N - p))

theorem oddPrimeUpperPairHighSet_mem_iff (p N j : ℕ) :
    j ∈ oddPrimeUpperPairHighSet p N ↔
      ∃ ell, b N ≤ ell ∧ ell < min (A N) (L N - p) ∧ j = p + ell := by
  simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico]
  constructor
  · intro hj
    refine ⟨j - p, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨ell, hlo, hhi, rfl⟩
    constructor <;> omega

theorem oddPrimeUpperCentralSet_mem_iff (p N j : ℕ) :
    j ∈ oddPrimeUpperCentralSet p N ↔
      b N ≤ j ∧ j < L N ∧ H N - p ≤ j ∧ j < p := by
  simp only [oddPrimeUpperCentralSet, Finset.mem_Ico]
  omega

theorem oddPrimeUpperPairHighSet_subset_raw (p N : ℕ) :
    oddPrimeUpperPairHighSet p N ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico] at hj
  apply Finset.mem_Ico.mpr
  constructor <;> omega

theorem oddPrimeUpperCentralSet_subset_raw (p N : ℕ) :
    oddPrimeUpperCentralSet p N ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  have h := (oddPrimeUpperCentralSet_mem_iff p N j).mp hj
  exact Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩

theorem oddPrimeUpperRetainedSet_subset_raw (p N : ℕ) :
    oddPrimeUpperRetainedSet p N ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  exact (Finset.mem_sdiff.mp hj).1

theorem oddPrimeUpperPairHighSet_disjoint_central (p N : ℕ) :
    Disjoint (oddPrimeUpperPairHighSet p N) (oddPrimeUpperCentralSet p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjp hjc
  simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico] at hjp
  have h := (oddPrimeUpperCentralSet_mem_iff p N j).mp hjc
  omega

theorem oddPrimeUpperRetainedSet_disjoint_pairHigh (p N : ℕ) :
    Disjoint (oddPrimeUpperRetainedSet p N) (oddPrimeUpperPairHighSet p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjp
  exact (Finset.mem_sdiff.mp hjr).2 (Finset.mem_union.mpr (Or.inl hjp))

theorem oddPrimeUpperRetainedSet_disjoint_central (p N : ℕ) :
    Disjoint (oddPrimeUpperRetainedSet p N) (oddPrimeUpperCentralSet p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjc
  exact (Finset.mem_sdiff.mp hjr).2 (Finset.mem_union.mpr (Or.inr hjc))

theorem oddPrimeUpperPool_partition (p N : ℕ) :
    oddPrimeUpperRetainedSet p N ∪
      (oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N) =
        Finset.Ico (b N) (L N) := by
  ext j
  simp only [oddPrimeUpperRetainedSet, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hj | hj | hj)
    · exact hj.1
    · exact oddPrimeUpperPairHighSet_subset_raw p N hj
    · exact oddPrimeUpperCentralSet_subset_raw p N hj
  · intro hj
    by_cases hp : j ∈ oddPrimeUpperPairHighSet p N
    · exact Or.inr (Or.inl hp)
    by_cases hc : j ∈ oddPrimeUpperCentralSet p N
    · exact Or.inr (Or.inr hc)
    · exact Or.inl ⟨hj, by simp [hp, hc]⟩

theorem oddPrimeUpperRetainedSet_mem_iff (p N j : ℕ) :
    j ∈ oddPrimeUpperRetainedSet p N ↔
      b N ≤ j ∧ j < L N ∧ (j < H N - p ∨ p ≤ j) ∧
        j ∉ oddPrimeUpperPairHighSet p N := by
  constructor
  · intro hj
    have hraw := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hj).1
    have hnot := (Finset.mem_sdiff.mp hj).2
    refine ⟨hraw.1, hraw.2, ?_, fun hpair => hnot (Finset.mem_union.mpr (Or.inl hpair))⟩
    by_cases hJ : j < H N - p
    · exact Or.inl hJ
    · apply Or.inr
      by_contra hpj
      apply hnot
      apply Finset.mem_union.mpr
      apply Or.inr
      exact (oddPrimeUpperCentralSet_mem_iff p N j).mpr
        ⟨hraw.1, hraw.2, by omega, by omega⟩
  · rintro ⟨hb, hL, hside, hpair⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨hb, hL⟩, ?_⟩
    intro hbad
    rcases Finset.mem_union.mp hbad with hbad | hbad
    · exact hpair hbad
    · have hc := (oddPrimeUpperCentralSet_mem_iff p N j).mp hbad
      rcases hside with hside | hside <;> omega

theorem oddPrimeUpperPairHighSet_card (p N : ℕ) :
    (oddPrimeUpperPairHighSet p N).card = min (A N) (L N - p) - b N := by
  rw [oddPrimeUpperPairHighSet, Nat.card_Ico]
  omega

theorem oddPrimeUpperCentralSet_card (p N : ℕ) :
    (oddPrimeUpperCentralSet p N).card = min p (L N) - max (b N) (H N - p) := by
  rw [oddPrimeUpperCentralSet, Nat.card_Ico]

theorem oddPrimeUpperRetainedSet_card (p N : ℕ) :
    (oddPrimeUpperRetainedSet p N).card =
      (L N - b N) - (min (A N) (L N - p) - b N) -
        (min p (L N) - max (b N) (H N - p)) := by
  have hsub : oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N ⊆
      Finset.Ico (b N) (L N) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hpair | hcentral
    · exact oddPrimeUpperPairHighSet_subset_raw p N hpair
    · exact oddPrimeUpperCentralSet_subset_raw p N hcentral
  rw [oddPrimeUpperRetainedSet, Finset.card_sdiff_of_subset hsub,
    Finset.card_union_of_disjoint (oddPrimeUpperPairHighSet_disjoint_central p N),
    oddPrimeUpperPairHighSet_card, oddPrimeUpperCentralSet_card, Nat.card_Ico]
  omega

theorem oddPrimeUpperExceptionalSet_card (p N : ℕ) :
    (oddPrimeUpperExceptionalSet p N).card = min (b N) (H N - p) - (L N - p) := by
  rw [oddPrimeUpperExceptionalSet, Nat.card_Ico]

theorem oddPrimeUpperExceptionalSet_mem_iff (p N ell : ℕ) :
    ell ∈ oddPrimeUpperExceptionalSet p N ↔
      ell < H N - p ∧ ¬(b N ≤ ell ∨ ell < L N - p) := by
  simp only [oddPrimeUpperExceptionalSet, Finset.mem_Ico]
  omega

theorem oddPrimeUpperPairIndex_bounds {p N ell : ℕ} (hN : 0 < N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hell : ell ∈ Finset.Ico (b N) (min (A N) (L N - p))) :
    ell ∈ oddPrimeUpperRetainedSet p N ∧
      p + ell ∈ oddPrimeUpperPairHighSet p N ∧
        ell < p ∧ ell < H N - p := by
  have he := Finset.mem_Ico.mp hell
  have hLH : L N < H N := by unfold L H; omega
  have hellp : ell < p := by
    have hA : ell < A N := he.2.trans_le (Nat.min_le_left _ _)
    unfold H at hH
    unfold A at hA
    omega
  have hhigh : p + ell < L N := by omega
  have hellJ : ell < H N - p := by omega
  have hnot : ell ∉ oddPrimeUpperPairHighSet p N := by
    intro hh
    simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico] at hh
    omega
  refine ⟨?_, ?_, hellp, hellJ⟩
  · exact (oddPrimeUpperRetainedSet_mem_iff p N ell).mpr
      ⟨he.1, by omega, Or.inl hellJ, hnot⟩
  · exact (oddPrimeUpperPairHighSet_mem_iff p N (p + ell)).mpr
      ⟨ell, he.1, he.2, rfl⟩

end InternalCatalan



noncomputable section

namespace InternalCatalan




def oddPrimeUpperPoolSplit (p N : ℕ) :
    (↥(oddPrimeUpperRetainedSet p N) ⊕
      (↥(oddPrimeUpperPairHighSet p N) ⊕ ↥(oddPrimeUpperCentralSet p N))) ≃
        ↥(Finset.Ico (b N) (L N)) := by
  classical
  let f : (↥(oddPrimeUpperRetainedSet p N) ⊕
      (↥(oddPrimeUpperPairHighSet p N) ⊕ ↥(oddPrimeUpperCentralSet p N))) →
        ↥(Finset.Ico (b N) (L N)) := fun x => match x with
    | Sum.inl j => ⟨j.val, oddPrimeUpperRetainedSet_subset_raw p N j.property⟩
    | Sum.inr (Sum.inl j) => ⟨j.val, oddPrimeUpperPairHighSet_subset_raw p N j.property⟩
    | Sum.inr (Sum.inr j) => ⟨j.val, oddPrimeUpperCentralSet_subset_raw p N j.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_pairHigh p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_central p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_pairHigh p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperPairHighSet_disjoint_central p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_central p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperPairHighSet_disjoint_central p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
  · intro j
    have hj : j.val ∈ oddPrimeUpperRetainedSet p N ∪
        (oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N) := by
      rw [oddPrimeUpperPool_partition]
      exact j.property
    rcases Finset.mem_union.mp hj with hr | hpc
    · exact ⟨Sum.inl ⟨j.val, hr⟩, rfl⟩
    · rcases Finset.mem_union.mp hpc with hp | hc
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, hp⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨j.val, hc⟩), rfl⟩

def oddPrimeUpperPoolEnumeration (p N : ℕ) :
    (Fin (Fintype.card ↥(oddPrimeUpperRetainedSet p N)) ⊕
      (Fin (Fintype.card ↥(oddPrimeUpperPairHighSet p N)) ⊕
        Fin (Fintype.card ↥(oddPrimeUpperCentralSet p N)))) ≃
          ↥(Finset.Ico (b N) (L N)) :=
  (Equiv.sumCongr (Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm
    (Equiv.sumCongr (Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm
      (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm)).trans
        (oddPrimeUpperPoolSplit p N)

@[simp] theorem oddPrimeUpperPoolEnumeration_retained_val (p N : ℕ)
    (j : Fin (Fintype.card ↥(oddPrimeUpperRetainedSet p N))) :
    (oddPrimeUpperPoolEnumeration p N (Sum.inl j)).val =
      ((Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j).val := rfl

@[simp] theorem oddPrimeUpperPoolEnumeration_pairHigh_val (p N : ℕ)
    (j : Fin (Fintype.card ↥(oddPrimeUpperPairHighSet p N))) :
    (oddPrimeUpperPoolEnumeration p N (Sum.inr (Sum.inl j))).val =
      ((Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j).val := rfl

@[simp] theorem oddPrimeUpperPoolEnumeration_central_val (p N : ℕ)
    (j : Fin (Fintype.card ↥(oddPrimeUpperCentralSet p N))) :
    (oddPrimeUpperPoolEnumeration p N (Sum.inr (Sum.inr j))).val =
      ((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val := rfl

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.OddLowerPairPool
namespace OAI


noncomputable section

namespace InternalCatalan

def oddLowerPairProfile (x : ℝ) : ℝ :=
  max (min (min x (59 - x)) 19 - max 7 (65 - 2 * x)) 0

def oddLowerLossProfile (x : ℝ) : ℝ :=
  96 - max (oddLowerPairProfile x - 4) 0

def oddUpperRankProfile (x : ℝ) : ℝ :=
  max (59 - x) 0 + max (59 - x - 19) 0 +
    max (65 - x - max 7 (59 - x)) 0

def oddUpperSimpleProfile (x : ℝ) : ℝ :=
  max (min 19 (59 - x) - 7) 0 +
    max (min 7 (65 - x) - max 0 (59 - x)) 0

def oddUpperLossProfile (x : ℝ) : ℝ :=
  min (min 96 (48 + oddUpperRankProfile x))
    (2 * oddUpperRankProfile x + oddUpperSimpleProfile x)

def oddLowerPairCountReal (N : ℕ) (p : ℝ) : ℝ :=
  max (min (min p ((L N : ℝ) - p)) (A N : ℝ) -
    max (b N : ℝ) ((H N : ℝ) - 2 * p)) 0

def oddLowerCountLossReal (N : ℕ) (p : ℝ) : ℝ :=
  2 * (n N : ℝ) - max (oddLowerPairCountReal N p - (q N : ℝ)) 0

def oddUpperRankCountReal (N : ℕ) (p : ℝ) : ℝ :=
  max ((L N : ℝ) - p) 0 + max ((L N : ℝ) - p - (A N : ℝ)) 0 +
    max ((H N : ℝ) - p - max (b N : ℝ) ((L N : ℝ) - p)) 0

def oddUpperSimpleCountReal (N : ℕ) (p : ℝ) : ℝ :=
  max (min (A N : ℝ) ((L N : ℝ) - p) - (b N : ℝ)) 0 +
    max (min (b N : ℝ) ((H N : ℝ) - p) - max 0 ((L N : ℝ) - p)) 0

def oddUpperCountLossReal (N : ℕ) (p : ℝ) : ℝ :=
  min (min (2 * (n N : ℝ)) ((n N : ℝ) + oddUpperRankCountReal N p))
    (2 * oddUpperRankCountReal N p + oddUpperSimpleCountReal N p)

def oddLowerPairCount (N p : ℕ) : ℕ :=
  (min (min (p : ℤ) ((L N : ℤ) - p)) (A N : ℤ) -
    max (b N : ℤ) ((H N : ℤ) - 2 * p)).toNat

def oddLowerCountLoss (N p : ℕ) : ℕ :=
  2 * n N - (oddLowerPairCount N p - q N)

def oddUpperRankCount (N p : ℕ) : ℕ :=
  ((L N : ℤ) - p).toNat + ((L N : ℤ) - p - (A N : ℤ)).toNat +
    ((H N : ℤ) - p - max (b N : ℤ) ((L N : ℤ) - p)).toNat

def oddUpperSimpleCount (N p : ℕ) : ℕ :=
  (min (A N : ℤ) ((L N : ℤ) - p) - (b N : ℤ)).toNat +
    (min (b N : ℤ) ((H N : ℤ) - p) - max 0 ((L N : ℤ) - p)).toNat

def oddUpperCountLoss (N p : ℕ) : ℕ :=
  min (min (2 * n N) (n N + oddUpperRankCount N p))
    (2 * oddUpperRankCount N p + oddUpperSimpleCount N p)







theorem oddLoss_intToNat_cast (z : ℤ) :
    (z.toNat : ℝ) = max (z : ℝ) 0 := by
  by_cases hz : 0 ≤ z
  · have hzR : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    rw [max_eq_left hzR]
    exact_mod_cast (Int.toNat_of_nonneg hz)
  · have hzle : z ≤ 0 := by omega
    have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hzle
    rw [Int.toNat_eq_zero.mpr hzle, Nat.cast_zero, max_eq_right hzR]

theorem oddLoss_natSub_cast (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max ((a : ℝ) - (b : ℝ)) 0 := by
  by_cases hab : b ≤ a
  · have habR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab
    rw [Nat.cast_sub hab, max_eq_left (sub_nonneg.mpr habR)]
  · have hba : a ≤ b := by omega
    have hbaR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hba
    rw [Nat.sub_eq_zero_of_le hba, Nat.cast_zero,
      max_eq_right (sub_nonpos.mpr hbaR)]

theorem oddLoss_intCast_min (a b : ℤ) :
    ((min a b : ℤ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  rcases le_total a b with hab | hba
  · have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [min_eq_left hab, min_eq_left habR]
  · have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [min_eq_right hba, min_eq_right hbaR]

theorem oddLoss_intCast_max (a b : ℤ) :
    ((max a b : ℤ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  rcases le_total a b with hab | hba
  · have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [max_eq_right hab, max_eq_right habR]
  · have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [max_eq_left hba, max_eq_left hbaR]

theorem oddLoss_natCast_min (a b : ℕ) :
    ((min a b : ℕ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  rcases le_total a b with hab | hba
  · have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [min_eq_left hab, min_eq_left habR]
  · have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [min_eq_right hba, min_eq_right hbaR]

theorem oddLowerPairCount_cast (N p : ℕ) :
    (oddLowerPairCount N p : ℝ) = oddLowerPairCountReal N (p : ℝ) := by
  simp only [oddLowerPairCount, oddLowerPairCountReal, oddLoss_intToNat_cast,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
    oddLoss_intCast_min, oddLoss_intCast_max]

theorem oddUpperRankCount_cast (N p : ℕ) :
    (oddUpperRankCount N p : ℝ) = oddUpperRankCountReal N (p : ℝ) := by
  simp only [oddUpperRankCount, oddUpperRankCountReal, Nat.cast_add,
    oddLoss_intToNat_cast, Int.cast_sub, Int.cast_natCast, oddLoss_intCast_max]

theorem oddUpperSimpleCount_cast (N p : ℕ) :
    (oddUpperSimpleCount N p : ℝ) = oddUpperSimpleCountReal N (p : ℝ) := by
  simp only [oddUpperSimpleCount, oddUpperSimpleCountReal, Nat.cast_add,
    oddLoss_intToNat_cast, Int.cast_sub, Int.cast_natCast, Int.cast_zero,
    oddLoss_intCast_min, oddLoss_intCast_max]

theorem oddUpperCountLoss_cast (N p : ℕ) :
    (oddUpperCountLoss N p : ℝ) = oddUpperCountLossReal N (p : ℝ) := by
  simp only [oddUpperCountLoss, oddUpperCountLossReal, oddLoss_natCast_min,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    oddUpperRankCount_cast, oddUpperSimpleCount_cast]

theorem oddLowerPairCount_le_A (N p : ℕ) : oddLowerPairCount N p ≤ A N := by
  unfold oddLowerPairCount
  rw [Int.toNat_le]
  have htop : min (min (p : ℤ) ((L N : ℤ) - p)) (A N : ℤ) ≤ A N :=
    min_le_right _ _
  have hbottom : (0 : ℤ) ≤ max (b N : ℤ) ((H N : ℤ) - 2 * p) :=
    le_trans (Int.natCast_nonneg (b N)) (le_max_left _ _)
  omega

theorem oddLowerLossSubtrahend_le (N p : ℕ) :
    oddLowerPairCount N p - q N ≤ 2 * n N := by
  have hpair := oddLowerPairCount_le_A N p
  have hsub : oddLowerPairCount N p - q N ≤ oddLowerPairCount N p :=
    Nat.sub_le _ _
  have hA : A N ≤ 2 * n N := by
    unfold A n
    omega
  exact le_trans hsub (le_trans hpair hA)

theorem oddLowerCountLoss_cast (N p : ℕ) :
    (oddLowerCountLoss N p : ℝ) = oddLowerCountLossReal N (p : ℝ) := by
  unfold oddLowerCountLoss oddLowerCountLossReal
  rw [Nat.cast_sub (oddLowerLossSubtrahend_le N p),
    oddLoss_natSub_cast, oddLowerPairCount_cast]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

end InternalCatalan

end



namespace InternalCatalan

theorem oddLowerPairProfile_of_le_23 (x : ℝ) (hx : x ≤ 23) :
    oddLowerPairProfile x = 0 := by
  unfold oddLowerPairProfile
  apply max_eq_right
  apply sub_nonpos.mpr
  calc
    min (min x (59 - x)) 19 ≤ 19 := min_le_right _ _
    _ ≤ 65 - 2 * x := by linarith
    _ ≤ max 7 (65 - 2 * x) := le_max_right _ _

theorem oddLowerPairProfile_23_29 (x : ℝ) (hlo : 23 ≤ x) (hhi : x ≤ 29) :
    oddLowerPairProfile x = 2 * x - 46 := by
  have hmin : min (min x (59 - x)) 19 = 19 :=
    min_eq_right (le_min (by linarith) (by linarith))
  rw [oddLowerPairProfile, hmin,
    max_eq_right (show (7 : ℝ) ≤ 65 - 2 * x by linarith),
    max_eq_left (show (0 : ℝ) ≤ 19 - (65 - 2 * x) by linarith)]
  ring

theorem oddLowerPairProfile_29_65div2 (x : ℝ)
    (hlo : 29 ≤ x) (hhi : x ≤ 65 / 2) :
    oddLowerPairProfile x = 12 := by
  have hmin : min (min x (59 - x)) 19 = 19 :=
    min_eq_right (le_min (by linarith) (by linarith))
  rw [oddLowerPairProfile, hmin,
    max_eq_left (show (65 : ℝ) - 2 * x ≤ 7 by linarith)]
  norm_num

theorem oddLowerLossProfile_eq (x : ℝ) (hx : x ≤ 65 / 2) :
    oddLowerLossProfile x = oddPrimeLoss x := by
  by_cases h23 : x ≤ 23
  · rw [oddLowerLossProfile, oddLowerPairProfile_of_le_23 x h23,
      oddPrimeLoss_of_le_25 x (by linarith)]
    norm_num
  by_cases h25 : x ≤ 25
  · rw [oddLowerLossProfile, oddLowerPairProfile_23_29 x (by linarith) (by linarith),
      max_eq_right (show 2 * x - 46 - 4 ≤ (0 : ℝ) by linarith),
      oddPrimeLoss_of_le_25 x h25]
    ring
  by_cases h29 : x ≤ 29
  · rw [oddLowerLossProfile, oddLowerPairProfile_23_29 x (by linarith) h29,
      max_eq_left (show (0 : ℝ) ≤ 2 * x - 46 - 4 by linarith),
      oddPrimeLoss_25_29 x (by linarith) h29]
    ring
  rw [oddLowerLossProfile, oddLowerPairProfile_29_65div2 x (by linarith) hx,
    oddPrimeLoss_29_65div2 x (by linarith) hx]
  norm_num

end InternalCatalan



noncomputable section

namespace InternalCatalan

theorem oddUpperProfiles_65div2_40 (x : ℝ) (hlo : 65 / 2 ≤ x) (hhi : x ≤ 40) :
    oddUpperRankProfile x = 105 - 2 * x ∧ oddUpperSimpleProfile x = 12 := by
  have _ := hlo
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 59 - x - 19 by linarith),
      max_eq_right (show (7 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - (59 - x) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_left (show (19 : ℝ) ≤ 59 - x by linarith),
      min_eq_left (show (7 : ℝ) ≤ 65 - x by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 19 - 7 by norm_num),
      max_eq_right (show (7 : ℝ) - (59 - x) ≤ 0 by linarith)]
    ring

theorem oddUpperProfiles_40_52 (x : ℝ) (hlo : 40 ≤ x) (hhi : x ≤ 52) :
    oddUpperRankProfile x = 65 - x ∧ oddUpperSimpleProfile x = 52 - x := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_right (show (7 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - (59 - x) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_left (show (7 : ℝ) ≤ 65 - x by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 59 - x - 7 by linarith),
      max_eq_right (show (7 : ℝ) - (59 - x) ≤ 0 by linarith)]
    ring

theorem oddUpperProfiles_52_58 (x : ℝ) (hlo : 52 ≤ x) (hhi : x ≤ 58) :
    oddUpperRankProfile x = 117 - 2 * x ∧ oddUpperSimpleProfile x = x - 52 := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - 7 by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_left (show (7 : ℝ) ≤ 65 - x by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      max_eq_left (show (0 : ℝ) ≤ 7 - (59 - x) by linarith)]
    ring

theorem oddUpperProfiles_58_59 (x : ℝ) (hlo : 58 ≤ x) (hhi : x ≤ 59) :
    oddUpperRankProfile x = 59 - x ∧ oddUpperSimpleProfile x = 6 := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show 65 - x - 7 ≤ (0 : ℝ) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_right (show 65 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - (59 - x) by linarith)]
    ring

theorem oddUpperProfiles_59_65 (x : ℝ) (hlo : 59 ≤ x) (hhi : x ≤ 65) :
    oddUpperRankProfile x = 0 ∧ oddUpperSimpleProfile x = 65 - x := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_right (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show 65 - x - 7 ≤ (0 : ℝ) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_right (show 65 - x ≤ (7 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      sub_zero, max_eq_left (show (0 : ℝ) ≤ 65 - x by linarith)]
    ring

theorem oddUpperProfiles_of_ge_65 (x : ℝ) (hlo : 65 ≤ x) :
    oddUpperRankProfile x = 0 ∧ oddUpperSimpleProfile x = 0 := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_right (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show 65 - x - 7 ≤ (0 : ℝ) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_right (show 65 - x ≤ (7 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      sub_zero, max_eq_right (show 65 - x ≤ (0 : ℝ) by linarith)]
    ring

private theorem oddUpperLossProfile_of_second (x r s : ℝ)
    (hR : oddUpperRankProfile x = r) (hS : oddUpperSimpleProfile x = s)
    (h96 : 2 * r + s ≤ 96) (h48 : 2 * r + s ≤ 48 + r) :
    oddUpperLossProfile x = 2 * r + s := by
  rw [oddUpperLossProfile, hR, hS, min_eq_right (le_min h96 h48)]

theorem oddUpperLossProfile_eq (x : ℝ) (hx : 65 / 2 ≤ x) :
    oddUpperLossProfile x = oddPrimeLoss x := by
  by_cases h40 : x ≤ 40
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_65div2_40 x hx h40
    by_cases hmid : x ≤ 69 / 2
    · rw [oddUpperLossProfile, hR, hS,
        oddPrimeLoss_65div2_69div2 x hx hmid,
        min_eq_right (show 48 + (105 - 2 * x) ≤ (96 : ℝ) by linarith),
        min_eq_left (show 48 + (105 - 2 * x) ≤ 2 * (105 - 2 * x) + 12 by
          linarith)]
      ring
    · rw [oddUpperLossProfile_of_second x (105 - 2 * x) 12 hR hS
        (by linarith) (by linarith),
        oddPrimeLoss_69div2_40 x (by linarith) h40]
      ring
  by_cases h52 : x ≤ 52
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_40_52 x (by linarith) h52
    rw [oddUpperLossProfile_of_second x (65 - x) (52 - x) hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_40_58 x (by linarith) (by linarith)]
    ring
  by_cases h58 : x ≤ 58
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_52_58 x (by linarith) h58
    rw [oddUpperLossProfile_of_second x (117 - 2 * x) (x - 52) hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_40_58 x (by linarith) h58]
    ring
  by_cases h59 : x ≤ 59
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_58_59 x (by linarith) h59
    rw [oddUpperLossProfile_of_second x (59 - x) 6 hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_58_59 x (by linarith) h59]
    ring
  by_cases h65 : x ≤ 65
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_59_65 x (by linarith) h65
    rw [oddUpperLossProfile_of_second x 0 (65 - x) hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_59_65 x (by linarith) h65]
    ring
  obtain ⟨hR, hS⟩ := oddUpperProfiles_of_ge_65 x (by linarith)
  rw [oddUpperLossProfile_of_second x 0 0 hR hS (by norm_num) (by norm_num),
    oddPrimeLoss_of_ge_65 x (by linarith)]
  ring

end InternalCatalan

end



namespace InternalCatalan

theorem oddUpperRankCount_eq_nat (N p : ℕ) :
    oddUpperRankCount N p =
      (L N - p) + (L N - p - A N) +
        (H N - p - max (b N) (L N - p)) := by
  unfold oddUpperRankCount
  omega

theorem oddUpperSimpleCount_eq_nat (N p : ℕ) :
    oddUpperSimpleCount N p =
      (min (A N) (L N - p) - b N) +
        (min (b N) (H N - p) - (L N - p)) := by
  unfold oddUpperSimpleCount
  omega

theorem oddUpperRetainedCount_eq (N p : ℕ) (hN : 0 < N)
    (hp : p ≤ H N) (hhalf : H N ≤ 2 * p) :
    (L N - b N) - (min (A N) (L N - p) - b N) -
        (min p (L N) - max (b N) (H N - p)) =
      oddUpperRankCount N p := by
  rw [oddUpperRankCount_eq_nat]
  unfold L H A b at *
  omega

theorem oddUpperSimplePhysicalCount_eq (N p : ℕ) :
    (min (A N) (L N - p) - b N) +
        (min (b N) (H N - p) - (L N - p)) =
      oddUpperSimpleCount N p :=
  (oddUpperSimpleCount_eq_nat N p).symm





private theorem oddCount_mul_max {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    c * max u v = max (c * u) (c * v) := by
  rcases le_total u v with huv | hvu
  · rw [max_eq_right huv, max_eq_right (mul_le_mul_of_nonneg_left huv hc)]
  · rw [max_eq_left hvu, max_eq_left (mul_le_mul_of_nonneg_left hvu hc)]

private theorem oddCount_mul_min {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    c * min u v = min (c * u) (c * v) := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv, min_eq_left (mul_le_mul_of_nonneg_left huv hc)]
  · rw [min_eq_right hvu, min_eq_right (mul_le_mul_of_nonneg_left hvu hc)]

theorem oddLowerPairCountReal_mul (N : ℕ) (x : ℝ) :
    oddLowerPairCountReal N ((N : ℝ) * x) = (N : ℝ) * oddLowerPairProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddLowerPairCountReal, oddLowerPairProfile, L, A, b, H,
    Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN, oddCount_mul_min hN,
    mul_sub, mul_zero]
  ring_nf

theorem oddLowerCountLossReal_mul (N : ℕ) (x : ℝ) :
    oddLowerCountLossReal N ((N : ℝ) * x) = (N : ℝ) * oddLowerLossProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddLowerCountLossReal, oddLowerPairCountReal_mul, oddLowerLossProfile,
    n, q, Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN,
    mul_sub, mul_zero]
  ring_nf

theorem oddUpperRankCountReal_mul (N : ℕ) (x : ℝ) :
    oddUpperRankCountReal N ((N : ℝ) * x) = (N : ℝ) * oddUpperRankProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddUpperRankCountReal, oddUpperRankProfile, L, A, b, H,
    Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN,
    mul_add, mul_sub, mul_zero]
  ring_nf

theorem oddUpperSimpleCountReal_mul (N : ℕ) (x : ℝ) :
    oddUpperSimpleCountReal N ((N : ℝ) * x) = (N : ℝ) * oddUpperSimpleProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddUpperSimpleCountReal, oddUpperSimpleProfile, L, A, b, H,
    Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN, oddCount_mul_min hN,
    mul_add, mul_sub, mul_zero]
  ring_nf

theorem oddUpperCountLossReal_mul (N : ℕ) (x : ℝ) :
    oddUpperCountLossReal N ((N : ℝ) * x) = (N : ℝ) * oddUpperLossProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddUpperCountLossReal, oddUpperRankCountReal_mul,
    oddUpperSimpleCountReal_mul, oddUpperLossProfile, n, Nat.cast_mul,
    Nat.cast_ofNat, oddCount_mul_min hN, mul_add]
  ring_nf

private theorem oddCount_scale_cancel (N : ℕ) (hN : 0 < N) (p : ℝ) :
    (N : ℝ) * (p / (N : ℝ)) = p := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN']




theorem oddLowerCountLossReal_eq (N : ℕ) (p : ℝ) (hN : 0 < N)
    (hp : 2 * p ≤ (H N : ℝ)) :
    oddLowerCountLossReal N p = (N : ℝ) * oddPrimeLoss (p / (N : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : p / (N : ℝ) ≤ 65 / 2 := by
    apply (div_le_iff₀ hN').2
    simp only [H, Nat.cast_mul, Nat.cast_ofNat] at hp
    linarith
  have h := oddLowerCountLossReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p, oddLowerLossProfile_eq _ hx] at h
  exact h

theorem oddUpperCountLossReal_eq (N : ℕ) (p : ℝ) (hN : 0 < N)
    (hp : (H N : ℝ) ≤ 2 * p) :
    oddUpperCountLossReal N p = (N : ℝ) * oddPrimeLoss (p / (N : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 65 / 2 ≤ p / (N : ℝ) := by
    apply (le_div_iff₀ hN').2
    simp only [H, Nat.cast_mul, Nat.cast_ofNat] at hp
    linarith
  have h := oddUpperCountLossReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p, oddUpperLossProfile_eq _ hx] at h
  exact h








theorem oddLowerCountLoss_eq (N p : ℕ) (hN : 0 < N) (hp : 2 * p ≤ H N) :
    (oddLowerCountLoss N p : ℝ) =
      (N : ℝ) * oddPrimeLoss ((p : ℝ) / (N : ℝ)) := by
  rw [oddLowerCountLoss_cast]
  apply oddLowerCountLossReal_eq N p hN
  exact_mod_cast hp

theorem oddUpperCountLoss_eq (N p : ℕ) (hN : 0 < N) (hp : H N ≤ 2 * p) :
    (oddUpperCountLoss N p : ℝ) =
      (N : ℝ) * oddPrimeLoss ((p : ℝ) / (N : ℝ)) := by
  rw [oddUpperCountLoss_cast]
  apply oddUpperCountLossReal_eq N p hN
  exact_mod_cast hp



end InternalCatalan



noncomputable section

namespace InternalCatalan

open Classical

def oddLowerPairSet (N p : ℕ) : Finset ℕ :=
  Finset.Ico (max (b N) (H N - 2 * p)) (min (min p (L N - p)) (A N))

def oddLowerHighSet (N p : ℕ) : Finset ℕ :=
  (oddLowerPairSet N p).image (fun ell => p + ell)

def oddLowerRetainedSet (N p : ℕ) : Finset ℕ :=
  Finset.Ico (b N) (L N) \ oddLowerHighSet N p

theorem oddLower_prime_lt_L {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N) :
    p < L N := by unfold H L at *; omega

theorem oddLowerPairSet_bounds {N p ell : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) (hell : ell ∈ oddLowerPairSet N p) :
    b N ≤ ell ∧ ell < p ∧ H N ≤ ell + 2 * p ∧
      p + ell < L N ∧ ell < A N := by
  have hpL := oddLower_prime_lt_L hN hp
  dsimp [oddLowerPairSet] at hell
  simp only [Finset.mem_Ico, max_le_iff, lt_min_iff] at hell
  omega

theorem oddLowerPairSet_mem_pool {N p ell : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) (hell : ell ∈ oddLowerPairSet N p) :
    ell ∈ Finset.Ico (b N) (L N) := by
  have h := oddLowerPairSet_bounds hN hp hell
  exact Finset.mem_Ico.mpr ⟨h.1, by omega⟩

theorem oddLowerHighSet_subset_pool {N p : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) : oddLowerHighSet N p ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hj
  have h := oddLowerPairSet_bounds hN hp hell
  exact Finset.mem_Ico.mpr ⟨by omega, h.2.2.2.1⟩

theorem oddLowerPairSet_mem_retained {N p ell : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) (hell : ell ∈ oddLowerPairSet N p) :
    ell ∈ oddLowerRetainedSet N p := by
  refine Finset.mem_sdiff.mpr ⟨oddLowerPairSet_mem_pool hN hp hell, ?_⟩
  intro hhigh
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hhigh
  have h := oddLowerPairSet_bounds hN hp hell
  omega

theorem oddLowerHighSet_card (N p : ℕ) :
    (oddLowerHighSet N p).card = (oddLowerPairSet N p).card := by
  apply Finset.card_image_of_injective
  intro i j hij
  change p + i = p + j at hij
  omega

theorem oddLowerPairSet_card {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N) :
    (oddLowerPairSet N p).card = oddLowerPairCount N p := by
  have hpL := oddLower_prime_lt_L hN hp
  rw [oddLowerPairSet, Nat.card_Ico]
  unfold oddLowerPairCount
  omega

theorem oddLowerRetainedSet_card {N p : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) :
    (oddLowerRetainedSet N p).card = n N + q N - oddLowerPairCount N p := by
  rw [oddLowerRetainedSet, Finset.card_sdiff_of_subset (oddLowerHighSet_subset_pool hN hp),
    oddLowerHighSet_card, oddLowerPairSet_card hN hp, Nat.card_Ico,
    L_eq_n_add_b_add_q]
  omega

theorem oddLowerPairCount_le_pool {N p : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) : oddLowerPairCount N p ≤ n N + q N := by
  have h := Finset.card_le_card (oddLowerHighSet_subset_pool hN hp)
  rw [oddLowerHighSet_card, oddLowerPairSet_card hN hp, Nat.card_Ico,
    L_eq_n_add_b_add_q] at h
  omega

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.OddPhysicalCombination
namespace OAI


noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPhysicalCombination_expansion {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (g : oddPhysicalIndex R B C → Fin n → ℚ) :
    Matrix.det (Matrix.of fun r k : Fin n =>
      ∑ j, oddPhysicalColumn p U W I V a j r * g j k) =
      ∑ c : Fin n → oddPhysicalIndex R B C,
        (∏ k, g (c k) k) *
          Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) := by
  calc
    _ = ∑ c : Fin n → oddPhysicalIndex R B C,
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k, oddPhysicalColumn p U W I V a (c k) (σ k) * g (c k) k := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem oddPhysicalMinor_eq_zero_of_not_injective {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (c : Fin n → oddPhysicalIndex R B C)
    (hc : ¬ Function.Injective c) :
    Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) = 0 := by
  simp only [Function.Injective] at hc
  push Not at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply, hij]

theorem oddPhysicalCombination_valuation_lower {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (g : oddPhysicalIndex R B C → Fin n → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (ha : ∀ j l, ((a j l).den : ZMod p) ≠ 0)
    (hg : ∀ j k, ((g j k).den : ZMod p) ≠ 0) :
    -((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ) ≤
      padicValRat p (Matrix.det (Matrix.of fun r k : Fin n =>
        ∑ j, oddPhysicalColumn p U W I V a j r * g j k)) := by
  rw [oddPhysicalCombination_expansion]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro c hc
  by_cases hcinj : Function.Injective c
  · have hm := oddPhysicalMinor_valuation_lower U W I V a hU hW hI hV ha c hcinj
    have hgprod : 0 ≤ padicValRat p (∏ k, g (c k) k) := by
      simpa only [mul_zero] using prime_prod_valuation_lower Finset.univ
        (fun k => g (c k) k) 0 (by omega)
        (fun k _ => rational_valuation_nonneg_of_den_ne_zero (hg (c k) k))
    simpa only [zero_add] using prime_mul_valuation_lower
      (∏ k, g (c k) k)
      (Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r))
      0 (-((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ))
      (by omega) hgprod hm
  · rw [oddPhysicalMinor_eq_zero_of_not_injective p U W I V a c hcinj,
      mul_zero, padicValRat.zero]
    omega

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.OddLowerMinorTransfer
namespace OAI


noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddLowerRetainedSize (N p : ℕ) := Fintype.card ↥(oddLowerRetainedSet N p)
abbrev oddLowerPairedSize (N p : ℕ) := Fintype.card ↥(oddLowerPairSet N p)
abbrev oddLowerPhysicalIndex (N p : ℕ) :=
  oddPhysicalIndex (oddLowerRetainedSize N p) (oddLowerPairedSize N p) 0

def oddLowerRetainedTag {N p : ℕ} (j : ↥(oddLowerRetainedSet N p)) :
    oddLowerPhysicalIndex N p := Sum.inl ((Fintype.equivFin _) j)

def oddLowerPairedTag {N p : ℕ} (ell : ↥(oddLowerPairSet N p)) :
    oddLowerPhysicalIndex N p := Sum.inr (Sum.inl ((Fintype.equivFin _) ell))

def oddLowerRetainedVector (z : ℚ) (N p : ℕ)
    (j : Fin (oddLowerRetainedSize N p)) (r : Fin (n N)) : ℚ :=
  (p : ℚ) ^ 2 * rawEntryRat z N r.val
    (((Fintype.equivFin ↥(oddLowerRetainedSet N p)).symm j).val)

def oddLowerPairedVector (z : ℚ) (N p : ℕ)
    (j : Fin (oddLowerPairedSize N p)) (r : Fin (n N)) : ℚ :=
  let ell := ((Fintype.equivFin ↥(oddLowerPairSet N p)).symm j).val
  (p : ℚ) * (rawEntryRat z N r.val ell + rawEntryRat z N r.val (p + ell))

def oddLowerPhysicalColumn (z : ℚ) (N p : ℕ)
    (j : oddLowerPhysicalIndex N p) (r : Fin (n N)) : ℚ :=
  oddPhysicalColumn p (oddLowerRetainedVector z N p) (oddLowerPairedVector z N p)
    (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j)
    (fun j : Fin 0 => Fin.elim0 j) j r

theorem oddLowerPhysicalColumn_retained {N p : ℕ} [hpPrime : Fact p.Prime]
    (z : ℚ) (j : ↥(oddLowerRetainedSet N p)) (r : Fin (n N)) :
    oddLowerPhysicalColumn z N p (oddLowerRetainedTag j) r = rawEntryRat z N r.val j.val := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
  simp only [oddLowerPhysicalColumn, oddLowerRetainedTag, oddPhysicalColumn,
    oddLowerRetainedVector, Equiv.symm_apply_apply]
  field_simp [hpq]

theorem oddLowerPhysicalColumn_paired {N p : ℕ} [hpPrime : Fact p.Prime]
    (z : ℚ) (ell : ↥(oddLowerPairSet N p)) (r : Fin (n N)) :
    oddLowerPhysicalColumn z N p (oddLowerPairedTag ell) r =
      rawEntryRat z N r.val ell.val + rawEntryRat z N r.val (p + ell.val) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
  simp only [oddLowerPhysicalColumn, oddLowerPairedTag, oddPhysicalColumn,
    oddLowerPairedVector, Equiv.symm_apply_apply]
  field_simp [hpq]

theorem oddLowerRetainedVector_den_ne_zero {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddLowerRetainedSize N p)) (r : Fin (n N)) :
    ((oddLowerRetainedVector z N p j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddLowerRetainedSet N p)).symm j
  have hv := (Finset.mem_sdiff.mp v.property).1
  have hvL := (Finset.mem_Ico.mp hv).2
  have hvH : v.val < H N := by unfold L H at *; omega
  exact (rawEntryRat_prime_digit_reduction hp2 hH hvH z hz).1

theorem oddLowerPairedVector_den_ne_zero {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddLowerPairedSize N p)) (r : Fin (n N)) :
    ((oddLowerPairedVector z N p j r).den : ZMod p) ≠ 0 := by
  let ell := (Fintype.equivFin ↥(oddLowerPairSet N p)).symm j
  have hb := oddLowerPairSet_bounds hN hp ell.property
  have hhigh : p + ell.val < H N := by have := hb.2.2.2.1; unfold L H at *; omega
  exact rawEntryRat_pair_prime_scaled_den_ne_zero hp2 hN r.isLt hb.2.1
    hb.2.2.1 hhigh (Nat.le_of_lt hb.2.2.2.2) z hz

theorem oddLowerHighSet_sub_mem_pair {N p j : ℕ} (hj : j ∈ oddLowerHighSet N p) :
    j - p ∈ oddLowerPairSet N p ∧ p + (j - p) = j := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hj
  simpa using And.intro hell (rfl : p + ell = p + ell)

def oddLowerInverseCoeff {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N)
    (i : oddLowerPhysicalIndex N p) (j : ↥(Finset.Ico (b N) (L N))) : ℤ :=
  if hj : j.val ∈ oddLowerHighSet N p then
    let ell : ↥(oddLowerPairSet N p) := ⟨j.val - p, (oddLowerHighSet_sub_mem_pair hj).1⟩
    let low : ↥(oddLowerRetainedSet N p) :=
      ⟨ell.val, oddLowerPairSet_mem_retained hN hp ell.property⟩
    (if i = oddLowerPairedTag ell then 1 else 0) -
      (if i = oddLowerRetainedTag low then 1 else 0)
  else
    let keep : ↥(oddLowerRetainedSet N p) := ⟨j.val, Finset.mem_sdiff.mpr ⟨j.property, hj⟩⟩
    if i = oddLowerRetainedTag keep then 1 else 0

theorem rawEntryRat_eq_lower_physical_sum {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hp : 2 * p ≤ H N) (z : ℚ)
    (j : ↥(Finset.Ico (b N) (L N))) (r : Fin (n N)) :
    rawEntryRat z N r.val j.val =
      ∑ i : oddLowerPhysicalIndex N p,
        oddLowerPhysicalColumn z N p i r * (oddLowerInverseCoeff hN hp i j : ℚ) := by
  by_cases hj : j.val ∈ oddLowerHighSet N p
  · simp only [oddLowerInverseCoeff, dif_pos hj, Int.cast_sub, Int.cast_ite,
      Int.cast_one, Int.cast_zero, mul_sub, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [oddLowerPhysicalColumn_paired, oddLowerPhysicalColumn_retained,
      (oddLowerHighSet_sub_mem_pair hj).2]
    ring
  · simp only [oddLowerInverseCoeff, dif_neg hj, Int.cast_ite, Int.cast_one,
      Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, oddLowerPhysicalColumn_retained]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddLowerPhysical_loss_eq {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N) :
    min (2 * n N) (min (n N + oddLowerRetainedSize N p)
      (2 * oddLowerRetainedSize N p + oddLowerPairedSize N p + 0)) =
        oddLowerCountLoss N p := by
  have hd := oddLowerPairCount_le_pool hN hp
  simp only [oddLowerRetainedSize, oddLowerPairedSize, Fintype.card_coe,
    oddLowerRetainedSet_card hN hp, oddLowerPairSet_card hN hp, add_zero]
  unfold oddLowerCountLoss
  omega

theorem oddLowerPhysicalCombination_valuation_lower {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (g : oddLowerPhysicalIndex N p → Fin (n N) → ℤ) :
    -(oddLowerCountLoss N p : ℤ) ≤ padicValRat p
      (Matrix.det (Matrix.of fun r k : Fin (n N) =>
        ∑ i, oddLowerPhysicalColumn z N p i r * (g i k : ℚ))) := by
  have h := oddPhysicalCombination_valuation_lower
    (p := p) (n := n N) (R := oddLowerRetainedSize N p)
    (B := oddLowerPairedSize N p) (C := 0) (e := 0)
    (oddLowerRetainedVector z N p) (oddLowerPairedVector z N p)
    (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j)
    (fun j : Fin 0 => Fin.elim0 j) (fun i k => (g i k : ℚ))
    (oddLowerRetainedVector_den_ne_zero hp2 hH z hz)
    (oddLowerPairedVector_den_ne_zero hp2 hN hp z hz)
    (by intro j; exact Fin.elim0 j) (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)
    (by intro i k; simp only [Rat.den_intCast, Nat.cast_one]; exact one_ne_zero)
  simpa only [oddLowerPhysical_loss_eq hN hp, oddLowerPhysicalColumn] using h

theorem rawMinorRat_odd_lower_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    -(oddLowerCountLoss N p : ℤ) ≤ padicValRat p (rawMinorRat z N c) := by
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => rawEntryRat z N r.val (c k).val) =
        (Matrix.of fun r k : Fin (n N) => ∑ i : oddLowerPhysicalIndex N p,
          oddLowerPhysicalColumn z N p i r * (oddLowerInverseCoeff hN hp i (c k) : ℚ)) := by
    ext r k
    exact rawEntryRat_eq_lower_physical_sum hN hp z (c k) r
  rw [rawMinorRat, hmatrix]
  exact oddLowerPhysicalCombination_valuation_lower hp2 hN hp hH z hz
    (fun i k => oddLowerInverseCoeff hN hp i (c k))

theorem determinantRat_odd_lower_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(oddLowerCountLoss N p : ℤ) ≤ padicValRat p (determinantRat z N) := by
  rw [determinantRat_eq_sum_raw_choices]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro c hc
  have hminor := rawMinorRat_odd_lower_valuation hp2 hN hp hH z hz c
  have hint := int_prime_valuation_nonneg p (∏ k, rawFilterInt N (c k) k)
  simpa only [zero_add] using prime_mul_valuation_lower
    (((∏ k, rawFilterInt N (c k) k : ℤ) : ℚ)) (rawMinorRat z N c)
    0 (-(oddLowerCountLoss N p : ℤ)) (by omega) hint hminor

theorem determinantRat_odd_lower_loss {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hv : -(oddLowerCountLoss N p : ℝ) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
    exact_mod_cast determinantRat_odd_lower_valuation hp2 hN hp hH z hz
  rw [oddLowerCountLoss_eq N p hN hp] at hv
  simpa only [neg_mul] using hv

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.FinitePlaceAssembly
namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

def momentStartingRat (i j : ℕ) : ℚ :=
  if j ≤ i then boundaryMinus (i - j) else boundaryPlus (j - i)

theorem momentRat_reverse_diagonal (i j : ℕ) :
    momentRat i j = momentStartingRat i j -
      ∑ ell ∈ Finset.range (min i j),
        momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ) := by
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji, momentStartingRat, if_pos hji, min_eq_right hji]
    congr 1
    calc
      _ = ∑ ell ∈ Finset.range j,
          momentScalar (i - j + (j - 1 - ell)) / (((j - 1 - ell) + 1 : ℕ) : ℚ) :=
        (Finset.sum_range_reflect
          (fun k => momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ)) j).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        have he := Finset.mem_range.mp hell
        rw [momentScalarPred, if_neg (by omega : i - ell ≠ 0)]
        congr 2 <;> omega
  · have hij : i < j := by omega
    rw [momentRat_of_lt hij, momentStartingRat, if_neg hji, min_eq_left (Nat.le_of_lt hij)]
    congr 1
    calc
      _ = ∑ ell ∈ Finset.range i,
          momentScalar (i - 1 - ell) / ((j - i + (i - 1 - ell) + 1 : ℕ) : ℚ) :=
        (Finset.sum_range_reflect
          (fun k => momentScalar k / ((j - i + k + 1 : ℕ) : ℚ)) i).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        have he := Finset.mem_range.mp hell
        rw [momentScalarPred, if_neg (by omega : i - ell ≠ 0)]
        congr 2 <;> omega

theorem momentScalarPred_central_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < 2 * p) :
    (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * momentScalarPred z) =
        if p ≤ z then 2 * (oddPrimeWeight p).coeff (2 * p - 1 - z) else 0 := by
  have hz2 : z < p ^ 2 := by nlinarith [hp.out.two_le]
  have h := momentScalarPred_prime_digit_reduction hp2 hz2
  refine ⟨h.1, ?_⟩
  have hres : palindromicRatResidue p ((p : ℚ) * momentScalarPred z) =
      (oddPrimeWeight p).coeff (p - 1 - z % p) *
        palindromicRatResidue p (momentScalarPred (z / p)) := h.2.2
  rw [hres]
  by_cases hpz : p ≤ z
  · have hq : z / p = 1 := by
      rw [show z = p * 1 + (z - p) by omega, Nat.mul_add_div hp.out.pos,
        Nat.div_eq_of_lt (by omega : z - p < p), add_zero]
    have hr : z % p = z - p := by
      have he := Nat.mod_add_div z p
      rw [hq, Nat.mul_one] at he
      omega
    have he : p - 1 - (z - p) = 2 * p - 1 - z := by omega
    rw [if_pos hpz, hq, hr, he]
    have hs : palindromicRatResidue p (momentScalarPred 1) = 2 := by
      norm_num [momentScalarPred, momentScalar_zero, palindromicRatResidue]
    rw [hs, mul_comm]
  · rw [if_neg hpz, Nat.div_eq_of_lt (by omega : z < p), momentScalarPred_zero]
    norm_num [palindromicRatResidue]

theorem momentStartingRat_central_den_ne_zero {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) :
    ((momentStartingRat i j).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  unfold momentStartingRat
  split_ifs with hji
  · exact boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ (by omega)
  · exact boundaryPlus_odd_prime_valuation_nonneg hp.out hp2 _ (by omega)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem momentScalarPred_central_div_reduction {p i j ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) (hell : ell < min i j) :
    (((p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))) =
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0 := by
  have helli : ell < i := lt_of_lt_of_le hell (Nat.min_le_left i j)
  have hellj : ell < j := lt_of_lt_of_le hell (Nat.min_le_right i j)
  have hden0 : 0 < j - ell := by omega
  have hdenlt : j - ell < p := by omega
  have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hden0 hdenlt)
      ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
  have hscalar := momentScalarPred_central_reduction hp2
    (show i - ell < 2 * p by omega)
  have hrecip := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
  have hrecipden : ((1 / ((j - ell : ℕ) : ℚ)).den : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_one] using hrecip.1
  have hrecipR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
      1 / ((j - ell : ℕ) : ZMod p) := by
    simpa only [palindromicRatResidue, Nat.cast_one] using hrecip.2
  have hprod := rational_residue_mul hscalar.1 hrecipden
  have heq : (p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (i - ell)) * (1 / ((j - ell : ℕ) : ℚ)) := by ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hprod.1
  · rw [heq, palindromicRatResidue_mul hscalar.1 hrecipden, hscalar.2, hrecipR]
    by_cases hle : p + ell ≤ i
    · have hscalarle : p ≤ i - ell := by omega
      have hindex : 2 * p - 1 - (i - ell) = 2 * p + ell - 1 - i := by omega
      rw [if_pos hle, if_pos hscalarle, hindex]
      ring
    · have hscalarnot : ¬p ≤ i - ell := by omega
      rw [if_neg hle, if_neg hscalarnot, zero_mul]

theorem momentRat_central_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) :
    (((p : ℚ) * momentRat i j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * momentRat i j) =
        -(∑ ell ∈ Finset.range (min i j),
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0) := by
  let f : ℕ → ℚ := fun ell =>
    (p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (min i j)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0 :=
    momentScalarPred_central_div_reduction hp2 hj hi (Finset.mem_range.mp hell)
  have hsum := rational_residue_sum (Finset.range (min i j)) f
    (fun ell hell => (hterm ell hell).1)
  have hstart := momentStartingRat_central_den_ne_zero hp2 hj hi
  have hstartmul := rational_residue_mul (a := (p : ℚ)) (by simp) hstart
  have hstartR : palindromicRatResidue p ((p : ℚ) * momentStartingRat i j) = 0 := by
    rw [palindromicRatResidue_mul (by simp) hstart]
    simp [palindromicRatResidue]
  have hstrip : (p : ℚ) * momentRat i j =
      (p : ℚ) * momentStartingRat i j - ∑ ell ∈ Finset.range (min i j), f ell := by
    simp only [momentRat_reverse_diagonal, mul_sub, Finset.mul_sum, f]
  have hdiff := rational_residue_sub hstartmul.1 hsum.1
  refine ⟨?_, ?_⟩
  · rw [hstrip]
    exact hdiff.1
  · rw [hstrip, palindromicRatResidue_sub hstartmul.1 hsum.1, hstartR, zero_sub]
    congr 1
    calc
      palindromicRatResidue p (∑ ell ∈ Finset.range (min i j), f ell) =
          ∑ ell ∈ Finset.range (min i j), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrime_central_strip_range {R : Type*} [Semiring R] {p H i j : ℕ}
    (hp : 0 < p) (hpH : p ≤ H) (hi : i < H) (hj : H - p ≤ j) (f : ℕ → R) :
    (∑ ell ∈ Finset.range (min i j), if p + ell ≤ i then f ell else 0) =
      ∑ ell ∈ Finset.range (H - p), if p + ell ≤ i then f ell else 0 := by
  classical
  refine Finset.sum_bij_ne_zero (fun ell _ _ => ell) ?_ ?_ ?_ ?_
  · intro ell hell hf
    have hactive : p + ell ≤ i := by
      by_contra h
      exact hf (if_neg h)
    exact Finset.mem_range.mpr (by omega)
  · intro ell hell hf ell' hell' hf' heq
    exact heq
  · intro ell hell hf
    have hactive : p + ell ≤ i := by
      by_contra h
      exact hf (if_neg h)
    have hell' := Finset.mem_range.mp hell
    refine ⟨ell, Finset.mem_range.mpr (by omega), hf, rfl⟩
  · intro ell hell hf
    rfl

theorem rowP_momentRat_central_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) * (∑ t ∈ Finset.range (H N),
      ((rowP N r).coeff t : ℚ) * momentRat t j)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * (∑ t ∈ Finset.range (H N),
        ((rowP N r).coeff t : ℚ) * momentRat t j)) =
        -(∑ ell ∈ Finset.range (H N - p),
          (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun t => ((rowP N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)
  let c : ℕ → ℕ → ZMod p := fun t ell =>
    if p + ell ≤ t then (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
      ((j - ell : ℕ) : ZMod p) else 0
  have hterm (t : ℕ) (ht : t ∈ Finset.range (H N)) :
      ((f t).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f t) = ((rowP N r).coeff t : ZMod p) *
        (-(∑ ell ∈ Finset.range (H N - p), c t ell)) := by
    have ht' := Finset.mem_range.mp ht
    have hm := momentRat_central_reduction hp2 hj (show t < p + j by omega)
    have hprod := rational_residue_mul (p := p) (a := ((rowP N r).coeff t : ℚ))
      (by simp) hm.1
    have htrim := oddPrime_central_strip_range hp.out.pos hpH ht' hjlo
      (fun ell => (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
        ((j - ell : ℕ) : ZMod p))
    refine ⟨hprod.1, ?_⟩
    change palindromicRatResidue p
      (((rowP N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)) = _
    rw [palindromicRatResidue_mul (by simp) hm.1, palindromicRatResidue_intCast,
      hm.2, htrim]
  have hs := rational_residue_sum (Finset.range (H N)) f (fun t ht => (hterm t ht).1)
  have hscale : (p : ℚ) * (∑ t ∈ Finset.range (H N),
      ((rowP N r).coeff t : ℚ) * momentRat t j) = ∑ t ∈ Finset.range (H N), f t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [f]
    ring
  let P : (ZMod p)[X] := (rowP N r).map (Int.castRingHom (ZMod p))
  have hP : ∀ t, H N ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, rowP_coeff_eq_zero_of_ge hN ht, map_zero]
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a = (a : ZMod p) := rfl
  have hcoefficient (ell : ℕ) :
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) * c t ell) =
        (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p) := by
    have hcoef := oddPrime_central_P_coefficient (ell := ell) hp.out.pos hH P hP
    have hcoef' :
        (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
          (if p + ell ≤ t then 2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t) else 0)) =
          2 * oddPrimeExtractedP p N r ell 2 := by
      simpa only [P, coeff_map, hcast, oddPrimeExtractedP] using hcoef
    rw [← hcoef']
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [c]
    split_ifs <;> ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hs.1
  · rw [hscale]
    calc
      palindromicRatResidue p (∑ t ∈ Finset.range (H N), f t) =
          ∑ t ∈ Finset.range (H N), palindromicRatResidue p (f t) := hs.2
      _ = ∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
          (-(∑ ell ∈ Finset.range (H N - p), c t ell)) :=
        Finset.sum_congr rfl (fun t ht => (hterm t ht).2)
      _ = -(∑ ell ∈ Finset.range (H N - p), ∑ t ∈ Finset.range (H N),
          ((rowP N r).coeff t : ZMod p) * c t ell) := by
        simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro ell hell
        exact hcoefficient ell

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeLeadingV (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2 * oddPrimeExtractedP p N r ell 2 -
    (3 / 2 : ZMod p) * oddPrimeExtractedD p N r ell 1

theorem rawCatalanTerm_prime_reduction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * z * rawCatalanCoeffRat N r j) = 0 := by
  have hpz := rational_residue_mul (p := p) (a := (p : ℚ)) (by simp) hz
  have hfull := rational_residue_mul hpz.1
    (rawCatalanCoeffRat_odd_prime_den_ne_zero hp2 N r j)
  refine ⟨hfull.1, ?_⟩
  change (((p : ℚ) * z * rawCatalanCoeffRat N r j).num : ZMod p) /
    (((p : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0
  rw [hfull.2, hpz.2]
  simp

theorem rawEntryRat_central_layer {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * rawEntryRat z N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * rawEntryRat z N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)) := by
  let A : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (H N),
    ((rowP N r).coeff t : ℚ) * momentRat t j)
  let B : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (H N),
    ((rowD N r).coeff t : ℚ) * zetaRat t j)
  let C : ℚ := (p : ℚ) * z * rawCatalanCoeffRat N r j
  have hA := rowP_momentRat_central_reduction (r := r) hp2 hN hpH hH hjlo hj
  have hB := rowD_zetaRat_central_reduction (r := r) hN hpH hH hjlo hj
  have hC := rawCatalanTerm_prime_reduction hp2 z hz N r j
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpgt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hpgt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hsum := rational_residue_add hdiff.1 hC.1
  have hsplit : (p : ℚ) * rawEntryRat z N r j = A - (3 / 2 : ℚ) * B + C := by
    dsimp only [A, B, C]
    rw [rawEntryRat_affine, rawEntryRat_zero]
    ring
  have hAR : palindromicRatResidue p A =
      -(∑ ell ∈ Finset.range (H N - p),
        (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p)) := hA.2
  have hBR : palindromicRatResidue p B =
      -(∑ ell ∈ Finset.range (H N - p),
        oddPrimeExtractedD p N r ell 1 / ((j - ell : ℕ) : ZMod p)) := hB.2
  have hCR : palindromicRatResidue p C = 0 := hC.2
  have h32R : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hsumR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B + C) =
      palindromicRatResidue p (A - (3 / 2 : ℚ) * B) + palindromicRatResidue p C := hsum.2
  have hdiffR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B) =
      palindromicRatResidue p A - palindromicRatResidue p ((3 / 2 : ℚ) * B) := hdiff.2
  have hprodR : palindromicRatResidue p ((3 / 2 : ℚ) * B) =
      palindromicRatResidue p (3 / 2 : ℚ) * palindromicRatResidue p B := hBprod.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hsum.1
  · rw [hsplit, hsumR, hdiffR, hprodR, hAR, hBR, hCR, h32R, add_zero]
    simp only [oddPrimeLeadingV, sub_div, Finset.sum_sub_distrib,
      mul_div_assoc, ← Finset.mul_sum]
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rawEntryRat_low_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r ell) =
        oddPrimeLeadingV p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hH2 : 2 ≤ H N := by unfold H; omega
  have hraw := rawEntryRat_general_column_layer (k := 0) (N := N) (r := r)
    hp2 hN hH hell (by simpa using (show ell < H N by omega)) z hz
  simp only [Nat.zero_mul, zero_add] at hraw
  have hM :
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) =
          2 * oddPrimeExtractedP p N r ell 2 := by
    rw [Finset.sum_eq_single 2]
    · norm_num [palindromicRatResidue, momentRatSigned, momentRat,
        boundaryMinus]
      ring
    · intro v hv hne
      by_cases hv3 : 3 ≤ v
      · rw [oddPrimeExtractedP_eq_zero_of_ge_three hp.out.pos hN hwidth hv3, zero_mul]
      · have hcases : v = 0 ∨ v = 1 := by omega
        rcases hcases with rfl | rfl <;>
          norm_num [palindromicRatResidue, momentRatSigned, momentRatNegOne,
            momentRat, boundaryPlus, boundaryMinus]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega : 2 < H N + 1))).elim
  have hD :
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 0)) = oddPrimeExtractedD p N r ell 1 := by
    rw [Finset.sum_eq_single 1]
    · norm_num [palindromicRatResidue, zetaRat, harmonicRat, Finset.sum_range_succ]
    · intro u hu hne
      by_cases hu2 : 2 ≤ u
      · rw [oddPrimeExtractedD_eq_zero_of_ge_two hN hwidth hu2, zero_mul]
      · have hu0 : u = 0 := by omega
        subst u
        norm_num [palindromicRatResidue, zetaRat, harmonicRat]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega : 1 < H N))).elim
  refine ⟨hraw.1, ?_⟩
  rw [hraw.2, hM, hD]
  rfl

theorem rawEntryRat_high_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
        oddPrimeLeadingU p N r ell - oddPrimeLeadingV p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hlo := rawEntryRat_low_leading (r := r) hp2 hN hell hwidth hhigh z hz
  have hhi := rawEntryRat_prime_digit_reduction (N := N) (r := r) hp2 hH hhigh z hz
  have hpair := rawEntryRat_pair_leading (r := r) hp2 hN hell hwidth hhigh z hz
  have hadd := palindromicRatResidue_add hlo.1 hhi.1
  have hsum : oddPrimeLeadingV p N r ell +
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
        oddPrimeLeadingU p N r ell := by
    rw [← hlo.2, ← hadd, ← mul_add]
    exact hpair.2
  refine ⟨hhi.1, ?_⟩
  calc
    _ = (oddPrimeLeadingV p N r ell +
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell))) -
          oddPrimeLeadingV p N r ell := by ring
    _ = _ := by rw [hsum]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

def oddPrimeRepresented (p N ell : ℕ) : Prop :=
  b N ≤ ell ∨ ell < L N - p

instance oddPrimeRepresented_decidable (p N ell : ℕ) : Decidable (oddPrimeRepresented p N ell) :=
  inferInstanceAs (Decidable (b N ≤ ell ∨ ell < L N - p))

def oddPrimeRepresentativeRat (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if b N ≤ ell then rawEntryRat z N r ell else -rawEntryRat z N r (p + ell)

theorem oddPrimeRepresentativeRat_scaled_reduction {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p) (hell : ell < H N - p)
    (_hrep : oddPrimeRepresented p N ell) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell) =
        oddPrimeLeadingV p N r ell := by
  have hellp : ell < p := by omega
  have hwidth : H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < H N := by omega
  by_cases hb : b N ≤ ell
  · rw [oddPrimeRepresentativeRat, if_pos hb]
    exact rawEntryRat_low_leading (r := r) hp2 hN hellp hwidth hhigh z hz
  · have hellA : ell ≤ A N := by
      unfold b A at *
      omega
    have hU := oddPrimeLeadingU_eq_zero (p := p) hp.out.pos hN hr hellA
    have hraw := rawEntryRat_high_leading (r := r) hp2 hN hellp hwidth hhigh z hz
    rw [oddPrimeRepresentativeRat, if_neg hb, mul_neg]
    refine ⟨?_, ?_⟩
    · simpa only [Rat.neg_den] using hraw.1
    · have hneg :
          palindromicRatResidue p (-((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell))) =
            -palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) := by
        simp only [palindromicRatResidue, Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_div]
      rw [hneg, hraw.2, hU, zero_sub, neg_neg]







open scoped BigOperators

def oddPrimeShearedRat (z : ℚ) (p N r j : ℕ) : ℚ := by
  classical
  exact rawEntryRat z N r j + (p : ℚ) *
    ∑ ell ∈ Finset.range (H N - p),
      if oddPrimeRepresented p N ell then
        oddPrimeRepresentativeRat z p N r ell / ((j - ell : ℕ) : ℚ)
      else 0

theorem oddPrimeShearedRat_scaled_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * oddPrimeShearedRat z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * oddPrimeShearedRat z p N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0) := by
  classical
  let f : ℕ → ℚ := fun ell =>
    if oddPrimeRepresented p N ell then
      (p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell /
        ((j - ell : ℕ) : ℚ)
    else 0
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0 := by
    by_cases hrep : oddPrimeRepresented p N ell
    · have hellJ := Finset.mem_range.mp hell
      have hrepR := oddPrimeRepresentativeRat_scaled_reduction
        hp2 hN hr hpH hH hellJ hrep z hz
      have hellj : ell < j := hellJ.trans_le hjlo
      have hdpos : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
          ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
      have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
      simp only [Nat.cast_one] at hinv
      have hinvR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hinv.2
      have hprod := rational_residue_mul hrepR.1 hinv.1
      have heq : f ell =
          ((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell) *
            (1 / ((j - ell : ℕ) : ℚ)) := by
        dsimp only [f]
        rw [if_pos hrep]
        ring
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hprod.1
      · rw [heq, palindromicRatResidue_mul hrepR.1 hinv.1,
          hrepR.2, hinvR, if_pos hrep]
        ring
    · simp [f, hrep, palindromicRatResidue]
  have hsum := rational_residue_sum (Finset.range (H N - p)) f
    (fun ell hell => (hterm ell hell).1)
  have hsumR : palindromicRatResidue p (∑ ell ∈ Finset.range (H N - p), f ell) =
      ∑ ell ∈ Finset.range (H N - p),
        if oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
        else 0 := by
    calc
      _ = ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)
  have hcentral := rawEntryRat_central_layer (r := r) hp2 hN hpH hH hjlo hj z hz
  have hadd := rational_residue_add hcentral.1 hsum.1
  have hscale : (p : ℚ) * oddPrimeShearedRat z p N r j =
      (p : ℚ) * rawEntryRat z N r j + ∑ ell ∈ Finset.range (H N - p), f ell := by
    unfold oddPrimeShearedRat
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ell hell
    dsimp only [f]
    split_ifs <;> ring
  have hpartition :
      (∑ ell ∈ Finset.range (H N - p),
        oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)) =
      (∑ ell ∈ Finset.range (H N - p),
        if oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) +
      (∑ ell ∈ Finset.range (H N - p),
        if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ell hell
    by_cases hrep : oddPrimeRepresented p N ell <;> simp [hrep]
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hadd.1
  · rw [hscale, palindromicRatResidue_add hcentral.1 hsum.1,
      hcentral.2, hsumR, hpartition]
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeLeadingLiftRat (p N r ell : ℕ) [Fact p.Prime] : ℚ :=
  ((oddPrimeLeadingV p N r ell).val : ℚ)

def oddPrimeExceptionalPartRat (_z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ := by
  classical
  exact ∑ ell ∈ Finset.range (H N - p),
    if ¬oddPrimeRepresented p N ell then
      -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) else 0

def oddPrimeCentralRemainderRat (z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ :=
  oddPrimeShearedRat z p N r j - oddPrimeExceptionalPartRat z p N r j / (p : ℚ)

theorem oddPrimeLeadingLiftRat_reduction {p N r ell : ℕ} [Fact p.Prime] :
    ((oddPrimeLeadingLiftRat p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (oddPrimeLeadingLiftRat p N r ell) =
        oddPrimeLeadingV p N r ell :=
  zmod_val_rat_reduction (oddPrimeLeadingV p N r ell)

theorem oddPrimeExceptionalPartRat_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) :
    ((oddPrimeExceptionalPartRat z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (oddPrimeExceptionalPartRat z p N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
  classical
  let f : ℕ → ℚ := fun ell => if ¬oddPrimeRepresented p N ell then
    -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) else 0
  have ht (ell : ℕ) (hell : ell ∈ Finset.range (H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f ell) =
        -(if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    by_cases hex : ¬oddPrimeRepresented p N ell
    · have hell' : ell < H N - p := Finset.mem_range.mp hell
      have hd0 : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hd0 hdlt)
          ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
      have hf := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
      simp only [Nat.cast_one] at hf
      have hl := oddPrimeLeadingLiftRat_reduction (p := p) (N := N) (r := r) (ell := ell)
      have hm := rational_residue_mul hl.1 hf.1
      have hn := rational_residue_sub (p := p) (a := 0) (by norm_num) hm.1
      have heq : -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) =
          0 - oddPrimeLeadingLiftRat p N r ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      have hfr : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hf.2
      refine ⟨?_, ?_⟩
      · dsimp only [f]
        rw [if_pos hex, heq]
        exact hn.1
      · dsimp only [f]
        rw [if_pos hex, if_pos hex, heq,
          palindromicRatResidue_sub (by norm_num) hm.1,
          palindromicRatResidue_mul hl.1 hf.1, hl.2, hfr]
        norm_num [palindromicRatResidue]
        ring
    · simp only [f, if_neg hex]
      norm_num [palindromicRatResidue]
  have hs := rational_residue_sum (Finset.range (H N - p)) f (fun ell hell => (ht ell hell).1)
  refine ⟨hs.1, ?_⟩
  change palindromicRatResidue p (∑ ell ∈ Finset.range (H N - p), f ell) = _
  calc
    _ = ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f ell) := hs.2
    _ = ∑ ell ∈ Finset.range (H N - p),
        -(if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) :=
      Finset.sum_congr rfl (fun ell hell => (ht ell hell).2)
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem oddPrimeCentralRemainderRat_den_ne_zero {p N r j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hpH : p ≤ H N)
    (hH : H N ≤ 2 * p) (hjlo : H N - p ≤ j) (hj : j < p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    ((oddPrimeCentralRemainderRat z p N r j).den : ZMod p) ≠ 0 := by
  have hc := oddPrimeShearedRat_scaled_reduction hp2 hN hr hpH hH hjlo hj z hz
  have he := oddPrimeExceptionalPartRat_reduction (r := r) hjlo hj z
  exact rational_remainder_den_ne_zero_of_scaled_residue_eq hc.1 he.1
    (hc.2.trans he.2.symm)

theorem oddPrimeShearedRat_eq_remainder_add_exceptional
    {p : ℕ} [Fact p.Prime] (z : ℚ) (N r j : ℕ) :
    oddPrimeShearedRat z p N r j = oddPrimeCentralRemainderRat z p N r j +
      (p : ℚ)⁻¹ * oddPrimeExceptionalPartRat z p N r j := by
  unfold oddPrimeCentralRemainderRat
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeUpperPairIndex (p N j : ℕ) : Prop :=
  p + b N ≤ j ∧ j < p + min (A N) (L N - p)

def oddPrimeUpperCentralIndex (p N j : ℕ) : Prop :=
  max (b N) (H N - p) ≤ j ∧ j < min p (L N)

instance oddPrimeUpperPairIndex_decidable (p N j : ℕ) :
    Decidable (oddPrimeUpperPairIndex p N j) :=
  inferInstanceAs (Decidable (p + b N ≤ j ∧ j < p + min (A N) (L N - p)))

instance oddPrimeUpperCentralIndex_decidable (p N j : ℕ) :
    Decidable (oddPrimeUpperCentralIndex p N j) :=
  inferInstanceAs (Decidable (max (b N) (H N - p) ≤ j ∧ j < min p (L N)))

def oddPrimeUpperPoolRat (z : ℚ) (p N r j : ℕ) : ℚ :=
  if oddPrimeUpperPairIndex p N j then
    rawEntryRat z N r j + rawEntryRat z N r (j - p)
  else if oddPrimeUpperCentralIndex p N j then oddPrimeShearedRat z p N r j
  else rawEntryRat z N r j

def oddPrimeUpperRepresentativePoolRat (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if b N ≤ ell then oddPrimeUpperPoolRat z p N r ell
  else -oddPrimeUpperPoolRat z p N r (p + ell)

theorem oddPrimeUpperPoolRat_pair_low {p N j : ℕ} (hH : H N ≤ 2 * p)
    (hpair : oddPrimeUpperPairIndex p N j) (z : ℚ) (r : ℕ) :
    oddPrimeUpperPoolRat z p N r (j - p) = rawEntryRat z N r (j - p) := by
  have hpair' := hpair
  unfold oddPrimeUpperPairIndex at hpair'
  have hLH : L N ≤ H N := by unfold L H; omega
  have hKJ : L N - p ≤ H N - p := Nat.sub_le_sub_right hLH p
  have hellJ : j - p < H N - p := by omega
  have hellp : j - p < p := by omega
  have hnotpair : ¬oddPrimeUpperPairIndex p N (j - p) := by
    unfold oddPrimeUpperPairIndex
    omega
  have hnotcentral : ¬oddPrimeUpperCentralIndex p N (j - p) := by
    unfold oddPrimeUpperCentralIndex
    omega
  rw [oddPrimeUpperPoolRat, if_neg hnotpair, if_neg hnotcentral]

theorem oddPrimeUpperRepresentativePoolRat_eq {p N ell : ℕ}
    (hH : H N ≤ 2 * p) (hell : ell < H N - p) (z : ℚ) (r : ℕ) :
    oddPrimeUpperRepresentativePoolRat z p N r ell =
      oddPrimeRepresentativeRat z p N r ell := by
  have hellp : ell < p := by omega
  by_cases hb : b N ≤ ell
  · have hpnot : ¬oddPrimeUpperPairIndex p N ell := by
      unfold oddPrimeUpperPairIndex
      omega
    have hcnot : ¬oddPrimeUpperCentralIndex p N ell := by
      unfold oddPrimeUpperCentralIndex
      omega
    rw [oddPrimeUpperRepresentativePoolRat, if_pos hb, oddPrimeUpperPoolRat,
      if_neg hpnot, if_neg hcnot, oddPrimeRepresentativeRat, if_pos hb]
  · have hpnot : ¬oddPrimeUpperPairIndex p N (p + ell) := by
      unfold oddPrimeUpperPairIndex
      omega
    have hcnot : ¬oddPrimeUpperCentralIndex p N (p + ell) := by
      unfold oddPrimeUpperCentralIndex
      omega
    rw [oddPrimeUpperRepresentativePoolRat, if_neg hb, oddPrimeUpperPoolRat,
      if_neg hpnot, if_neg hcnot, oddPrimeRepresentativeRat, if_neg hb]

theorem rawEntryRat_eq_upper_pool_inverse {p N : ℕ} (hH : H N ≤ 2 * p)
    (z : ℚ) (r j : ℕ) :
    rawEntryRat z N r j = oddPrimeUpperPoolRat z p N r j -
      (if oddPrimeUpperPairIndex p N j then oddPrimeUpperPoolRat z p N r (j - p) else 0) -
      (if oddPrimeUpperCentralIndex p N j then
        (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
          if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r ell / ((j - ell : ℕ) : ℚ)
          else 0
        else 0) := by
  classical
  by_cases hpair : oddPrimeUpperPairIndex p N j
  · have hcentral : ¬oddPrimeUpperCentralIndex p N j := by
      unfold oddPrimeUpperPairIndex at hpair
      unfold oddPrimeUpperCentralIndex
      omega
    rw [if_pos hpair, if_neg hcentral, oddPrimeUpperPoolRat, if_pos hpair,
      oddPrimeUpperPoolRat_pair_low hH hpair, sub_zero]
    ring
  · by_cases hcentral : oddPrimeUpperCentralIndex p N j
    · have hsum :
          (∑ ell ∈ Finset.range (H N - p), if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r ell / ((j - ell : ℕ) : ℚ) else 0) =
          ∑ ell ∈ Finset.range (H N - p), if oddPrimeRepresented p N ell then
            oddPrimeRepresentativeRat z p N r ell / ((j - ell : ℕ) : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [oddPrimeUpperRepresentativePoolRat_eq hH (Finset.mem_range.mp hell)]
      rw [if_neg hpair, if_pos hcentral, sub_zero, hsum,
        oddPrimeUpperPoolRat, if_neg hpair, if_pos hcentral, oddPrimeShearedRat]
      ring
    · rw [if_neg hpair, if_neg hcentral, sub_zero, sub_zero,
        oddPrimeUpperPoolRat, if_neg hpair, if_neg hcentral]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddPrimeUpperExceptionalSize (p N : ℕ) :=
  Fintype.card ↥(oddPrimeUpperExceptionalSet p N)

theorem oddPrimeUpperExceptional_sum_eq (p N : ℕ) (f : ℕ → ℚ) :
    (∑ l : Fin (oddPrimeUpperExceptionalSize p N),
      f (((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm l).val)) =
        ∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then f ell else 0 := by
  have hs : oddPrimeUpperExceptionalSet p N =
      (Finset.range (H N - p)).filter (fun ell => ¬oddPrimeRepresented p N ell) := by
    ext ell
    constructor
    · intro h
      have he := (oddPrimeUpperExceptionalSet_mem_iff p N ell).mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he.1, he.2⟩
    · intro h
      have he := Finset.mem_filter.mp h
      exact (oddPrimeUpperExceptionalSet_mem_iff p N ell).mpr
        ⟨Finset.mem_range.mp he.1, he.2⟩
  calc
    _ = ∑ ell : ↥(oddPrimeUpperExceptionalSet p N), f ell.val :=
      Equiv.sum_comp (Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm
        (fun ell => f ell.val)
    _ = ∑ ell ∈ oddPrimeUpperExceptionalSet p N, f ell :=
      Finset.sum_coe_sort (oddPrimeUpperExceptionalSet p N) f
    _ = _ := by rw [hs, Finset.sum_filter]

theorem oddPrimeUpperExceptional_combination_eq {p : ℕ} [Fact p.Prime]
    (z : ℚ) (N r j : ℕ) :
    (∑ l : Fin (oddPrimeUpperExceptionalSize p N),
      (-1 / ((j - ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm l).val : ℕ) : ℚ)) *
        oddPrimeLeadingLiftRat p N r
          ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm l).val) =
      oddPrimeExceptionalPartRat z p N r j := by
  rw [oddPrimeUpperExceptional_sum_eq p N
    (fun ell => (-1 / ((j - ell : ℕ) : ℚ)) * oddPrimeLeadingLiftRat p N r ell)]
  unfold oddPrimeExceptionalPartRat
  apply Finset.sum_congr rfl
  intro ell hell
  by_cases hex : ¬oddPrimeRepresented p N ell
  · rw [if_pos hex, if_pos hex]
    ring
  · rw [if_neg hex, if_neg hex]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddPrimeUpperRetainedSize (p N : ℕ) := Fintype.card ↥(oddPrimeUpperRetainedSet p N)
abbrev oddPrimeUpperPairedSize (p N : ℕ) := Fintype.card ↥(oddPrimeUpperPairHighSet p N)
abbrev oddPrimeUpperCentralSize (p N : ℕ) := Fintype.card ↥(oddPrimeUpperCentralSet p N)
abbrev oddPrimeUpperPhysicalIndex (p N : ℕ) :=
  oddPhysicalIndex (oddPrimeUpperRetainedSize p N) (oddPrimeUpperPairedSize p N)
    (oddPrimeUpperCentralSize p N)

def oddPrimeUpperRetainedVector (z : ℚ) (p N : ℕ)
    (j : Fin (oddPrimeUpperRetainedSize p N)) (r : Fin (n N)) : ℚ :=
  (p : ℚ) ^ 2 * rawEntryRat z N r.val
    (((Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j).val)

def oddPrimeUpperPairedVector (z : ℚ) (p N : ℕ)
    (j : Fin (oddPrimeUpperPairedSize p N)) (r : Fin (n N)) : ℚ :=
  let v := ((Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j).val
  (p : ℚ) * (rawEntryRat z N r.val v + rawEntryRat z N r.val (v - p))

def oddPrimeUpperIntegralVector (z : ℚ) (p N : ℕ) [Fact p.Prime]
    (j : Fin (oddPrimeUpperCentralSize p N)) (r : Fin (n N)) : ℚ :=
  oddPrimeCentralRemainderRat z p N r.val
    (((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val)

def oddPrimeUpperExceptionalVector (p N : ℕ) [Fact p.Prime]
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) (r : Fin (n N)) : ℚ :=
  oddPrimeLeadingLiftRat p N r.val
    (((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell).val)

def oddPrimeUpperExceptionalCoeff (p N : ℕ)
    (j : Fin (oddPrimeUpperCentralSize p N))
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) : ℚ :=
  let v := ((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val
  let l := ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell).val
  (-1 : ℚ) / ((v - l : ℕ) : ℚ)

def oddPrimeUpperPhysicalColumn (z : ℚ) (p N : ℕ) [Fact p.Prime]
    (j : oddPrimeUpperPhysicalIndex p N) (r : Fin (n N)) : ℚ :=
  oddPhysicalColumn p (oddPrimeUpperRetainedVector z p N)
    (oddPrimeUpperPairedVector z p N) (oddPrimeUpperIntegralVector z p N)
    (oddPrimeUpperExceptionalVector p N) (oddPrimeUpperExceptionalCoeff p N) j r

theorem oddPrimeUpperRetainedVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddPrimeUpperRetainedSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperRetainedVector z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j
  have hraw := oddPrimeUpperRetainedSet_subset_raw p N v.property
  have hvL := (Finset.mem_Ico.mp hraw).2
  have hvH : v.val < H N := by unfold L H at *; omega
  exact (rawEntryRat_prime_digit_reduction (r := r.val) hp2 hHsq hvH z hz).1

theorem oddPrimeUpperPairedVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddPrimeUpperPairedSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperPairedVector z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j
  obtain ⟨ell, hb, hell, hveq⟩ :=
    (oddPrimeUpperPairHighSet_mem_iff p N v.val).mp v.property
  have hbounds := oddPrimeUpperPairIndex_bounds hN hpH hH
    (Finset.mem_Ico.mpr ⟨hb, hell⟩)
  have hsub : v.val - p = ell := by omega
  have hwidth : H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < H N := by have := hbounds.2.2.2; omega
  have hA : ell ≤ A N := by omega
  have hpair := rawEntryRat_pair_prime_scaled_den_ne_zero hp2 hN r.isLt
    hbounds.2.2.1 hwidth hhigh hA z hz
  change (((p : ℚ) * (rawEntryRat z N r.val v.val +
    rawEntryRat z N r.val (v.val - p))).den : ZMod p) ≠ 0
  rw [hsub, hveq, add_comm (rawEntryRat z N r.val (p + ell)) (rawEntryRat z N r.val ell)]
  exact hpair

theorem oddPrimeUpperIntegralVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddPrimeUpperCentralSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperIntegralVector z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j
  have hv := (oddPrimeUpperCentralSet_mem_iff p N v.val).mp v.property
  exact oddPrimeCentralRemainderRat_den_ne_zero hp2 hN r.isLt hpH hH
    hv.2.2.1 hv.2.2.2 z hz

theorem oddPrimeUpperExceptionalVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperExceptionalVector p N ell r).den : ZMod p) ≠ 0 :=
  (oddPrimeLeadingLiftRat_reduction (p := p) (N := N) (r := r.val)
    (ell := ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell).val)).1

theorem oddPrimeUpperExceptionalCoeff_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (j : Fin (oddPrimeUpperCentralSize p N))
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) :
    ((oddPrimeUpperExceptionalCoeff p N j ell).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j
  let l := (Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell
  have hv := (oddPrimeUpperCentralSet_mem_iff p N v.val).mp v.property
  have hl := (oddPrimeUpperExceptionalSet_mem_iff p N l.val).mp l.property
  have hdpos : 0 < v.val - l.val := by omega
  have hdlt : v.val - l.val < p := by omega
  have hd : ((v.val - l.val : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hf := nat_fraction_reduced_residue (p := p) 1 (v.val - l.val) hd
  change (((-1 : ℚ) / ((v.val - l.val : ℕ) : ℚ)).den : ZMod p) ≠ 0
  simpa only [Nat.cast_one, neg_div, Rat.neg_den] using hf.1

theorem oddPrimeUpperExceptionalVector_combination {p N : ℕ} [Fact p.Prime]
    (z : ℚ) (j : Fin (oddPrimeUpperCentralSize p N)) (r : Fin (n N)) :
    (∑ ell : Fin (oddPrimeUpperExceptionalSize p N),
      oddPrimeUpperExceptionalCoeff p N j ell * oddPrimeUpperExceptionalVector p N ell r) =
      oddPrimeExceptionalPartRat z p N r.val
        (((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val) := by
  simpa only [oddPrimeUpperExceptionalCoeff, oddPrimeUpperExceptionalVector] using
    oddPrimeUpperExceptional_combination_eq (p := p) z N r.val
      (((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val)

theorem oddPrimeUpperPhysicalColumn_eq_pool {p N : ℕ} [hp : Fact p.Prime]
    (z : ℚ) (phys : oddPrimeUpperPhysicalIndex p N) (r : Fin (n N)) :
    oddPrimeUpperPhysicalColumn z p N phys r =
      oddPrimeUpperPoolRat z p N r.val ((oddPrimeUpperPoolEnumeration p N phys).val) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rcases phys with j | (j | j)
  · let v := (Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j
    have hnot := (Finset.mem_sdiff.mp v.property).2
    have hnotpair : ¬oddPrimeUpperPairIndex p N v.val := by
      intro hpair
      have hmem : v.val ∈ oddPrimeUpperPairHighSet p N := by
        simpa only [oddPrimeUpperPairIndex, oddPrimeUpperPairHighSet, Finset.mem_Ico] using hpair
      exact hnot (Finset.mem_union.mpr (Or.inl hmem))
    have hnotcentral : ¬oddPrimeUpperCentralIndex p N v.val := by
      intro hcentral
      have hmem : v.val ∈ oddPrimeUpperCentralSet p N := by
        simpa only [oddPrimeUpperCentralIndex, oddPrimeUpperCentralSet, Finset.mem_Ico] using hcentral
      exact hnot (Finset.mem_union.mpr (Or.inr hmem))
    simp only [oddPrimeUpperPhysicalColumn, oddPhysicalColumn,
      oddPrimeUpperRetainedVector, oddPrimeUpperPoolEnumeration_retained_val]
    change ((p : ℚ) ^ 2)⁻¹ * ((p : ℚ) ^ 2 * rawEntryRat z N r.val v.val) =
      oddPrimeUpperPoolRat z p N r.val v.val
    rw [oddPrimeUpperPoolRat, if_neg hnotpair, if_neg hnotcentral]
    field_simp [hpq]
  · let v := (Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j
    have hpair : oddPrimeUpperPairIndex p N v.val := by
      simpa only [oddPrimeUpperPairIndex, oddPrimeUpperPairHighSet, Finset.mem_Ico] using v.property
    simp only [oddPrimeUpperPhysicalColumn, oddPhysicalColumn,
      oddPrimeUpperPairedVector, oddPrimeUpperPoolEnumeration_pairHigh_val]
    change (p : ℚ)⁻¹ * ((p : ℚ) * (rawEntryRat z N r.val v.val +
      rawEntryRat z N r.val (v.val - p))) = oddPrimeUpperPoolRat z p N r.val v.val
    rw [oddPrimeUpperPoolRat, if_pos hpair]
    field_simp [hpq]
  · let v := (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j
    have hcentral : oddPrimeUpperCentralIndex p N v.val := by
      simpa only [oddPrimeUpperCentralIndex, oddPrimeUpperCentralSet, Finset.mem_Ico] using v.property
    have hnotpair : ¬oddPrimeUpperPairIndex p N v.val := by
      intro hpair
      have hmem : v.val ∈ oddPrimeUpperPairHighSet p N := by
        simpa only [oddPrimeUpperPairIndex, oddPrimeUpperPairHighSet, Finset.mem_Ico] using hpair
      exact (Finset.disjoint_left.mp (oddPrimeUpperPairHighSet_disjoint_central p N)) hmem v.property
    have hsum := oddPrimeUpperExceptionalVector_combination (p := p) (N := N) z j r
    simp only [oddPrimeUpperPhysicalColumn, oddPhysicalColumn,
      oddPrimeUpperPoolEnumeration_central_val]
    rw [hsum]
    change oddPrimeCentralRemainderRat z p N r.val v.val +
      (p : ℚ)⁻¹ * oddPrimeExceptionalPartRat z p N r.val v.val =
        oddPrimeUpperPoolRat z p N r.val v.val
    rw [oddPrimeUpperPoolRat, if_neg hnotpair, if_pos hcentral]
    exact (oddPrimeShearedRat_eq_remainder_add_exceptional (p := p) z N r.val v.val).symm

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

def oddPrimeUpperDelta (p N : ℕ) (phys : oddPrimeUpperPhysicalIndex p N)
    (j : ℕ) : ℚ :=
  if (oddPrimeUpperPoolEnumeration p N phys).val = j then 1 else 0

def oddPrimeUpperRepresentativeNumber (p N ell : ℕ) : ℕ :=
  if b N ≤ ell then ell else p + ell

def oddPrimeUpperRepresentativeSign (N ell : ℕ) : ℚ :=
  if b N ≤ ell then 1 else -1

def oddPrimeUpperShearCoeff (p N : ℕ) (phys : oddPrimeUpperPhysicalIndex p N)
    (j ell : ℕ) : ℚ :=
  if oddPrimeRepresented p N ell then
    (oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ)) *
      oddPrimeUpperDelta p N phys (oddPrimeUpperRepresentativeNumber p N ell)
  else 0

def oddPrimeUpperInverseCoeff (p N : ℕ) (phys : oddPrimeUpperPhysicalIndex p N)
    (j : ℕ) : ℚ :=
  oddPrimeUpperDelta p N phys j -
    (if oddPrimeUpperPairIndex p N j then oddPrimeUpperDelta p N phys (j - p) else 0) -
    (if oddPrimeUpperCentralIndex p N j then
      (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
        oddPrimeUpperShearCoeff p N phys j ell
    else 0)

end InternalCatalan

end



namespace InternalCatalan

open Classical
open scoped BigOperators

private theorem upper_delta_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (phys : oddPrimeUpperPhysicalIndex p N) (j : ℕ) :
    ((oddPrimeUpperDelta p N phys j).den : ZMod p) ≠ 0 := by
  unfold oddPrimeUpperDelta
  split_ifs <;> norm_num

private theorem upper_sign_den_ne_zero {p : ℕ} [Fact p.Prime] (N ell : ℕ) :
    ((oddPrimeUpperRepresentativeSign N ell).den : ZMod p) ≠ 0 := by
  unfold oddPrimeUpperRepresentativeSign
  split_ifs <;> norm_num

private theorem upper_shearCoeff_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (phys : oddPrimeUpperPhysicalIndex p N) (j ell : ℕ)
    (hc : oddPrimeUpperCentralIndex p N j) (hell : ell ∈ Finset.range (H N - p)) :
    ((oddPrimeUpperShearCoeff p N phys j ell).den : ZMod p) ≠ 0 := by
  have hc' : max (b N) (H N - p) ≤ j ∧ j < min p (L N) := hc
  have he : ell < H N - p := Finset.mem_range.mp hell
  have hjlo : H N - p ≤ j := (Nat.le_max_right _ _).trans hc'.1
  have hj : j < p := hc'.2.trans_le (Nat.min_le_left _ _)
  have hdpos : 0 < j - ell := by omega
  have hdlt : j - ell < p := by omega
  have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  unfold oddPrimeUpperShearCoeff
  split_ifs with hrep
  · have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
    simp only [Nat.cast_one] at hinv
    have hsign := upper_sign_den_ne_zero (p := p) N ell
    have hmul := rational_residue_mul hsign hinv.1
    have hfrac :
        ((oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ)).den : ZMod p) ≠ 0 := by
      have heq : oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ) =
          oddPrimeUpperRepresentativeSign N ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      rw [heq]
      exact hmul.1
    exact (rational_residue_mul hfrac
      (upper_delta_den_ne_zero phys (oddPrimeUpperRepresentativeNumber p N ell))).1
  · norm_num

theorem oddPrimeUpperInverseCoeff_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (phys : oddPrimeUpperPhysicalIndex p N) (j : ℕ) :
    ((oddPrimeUpperInverseCoeff p N phys j).den : ZMod p) ≠ 0 := by
  have hbase := upper_delta_den_ne_zero phys j
  have hpair :
      ((if oddPrimeUpperPairIndex p N j then oddPrimeUpperDelta p N phys (j - p)
        else 0).den : ZMod p) ≠ 0 := by
    split_ifs
    · exact upper_delta_den_ne_zero phys (j - p)
    · norm_num
  have hleft := rational_residue_sub hbase hpair
  have hcentral :
      ((if oddPrimeUpperCentralIndex p N j then
          (p : ℚ) * ∑ ell ∈ Finset.range (H N - p), oddPrimeUpperShearCoeff p N phys j ell
        else 0).den : ZMod p) ≠ 0 := by
    split_ifs with hc
    · have hsum := rational_residue_sum (Finset.range (H N - p))
        (fun ell => oddPrimeUpperShearCoeff p N phys j ell)
        (fun ell hell => upper_shearCoeff_den_ne_zero phys j ell hc hell)
      exact (rational_residue_mul (a := (p : ℚ)) (by simp) hsum.1).1
    · norm_num
  exact (rational_residue_sub hleft.1 hcentral).1

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPrimeUpperDelta_sum {p N : ℕ} [Fact p.Prime]
    (z : ℚ) (r : Fin (n N)) (j : ℕ) (hj : j ∈ Finset.Ico (b N) (L N)) :
    (∑ phys : oddPrimeUpperPhysicalIndex p N,
      oddPrimeUpperPhysicalColumn z p N phys r * oddPrimeUpperDelta p N phys j) =
        oddPrimeUpperPoolRat z p N r.val j := by
  let e := oddPrimeUpperPoolEnumeration p N
  let v : ↥(Finset.Ico (b N) (L N)) := ⟨j, hj⟩
  have htag (phys : oddPrimeUpperPhysicalIndex p N) :
      (oddPrimeUpperPoolEnumeration p N phys).val = j ↔ phys = e.symm v := by
    constructor
    · intro h
      have he : e phys = v := Subtype.ext h
      calc
        phys = e.symm (e phys) := (e.symm_apply_apply phys).symm
        _ = e.symm v := congrArg e.symm he
    · rintro rfl
      exact congrArg Subtype.val (e.apply_symm_apply v)
  simp only [oddPrimeUpperDelta, htag, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa only [e, Equiv.apply_symm_apply] using
    oddPrimeUpperPhysicalColumn_eq_pool z (e.symm v) r

theorem oddPrimeUpperRepresentativeNumber_mem {p N ell : ℕ}
    (hN : 0 < N) (hH : H N ≤ 2 * p) (hell : ell < H N - p)
    (hrep : oddPrimeRepresented p N ell) :
    oddPrimeUpperRepresentativeNumber p N ell ∈ Finset.Ico (b N) (L N) := by
  have hbp : b N < p := by unfold b H at *; omega
  have hJL : H N - p ≤ L N := by unfold H L at *; omega
  unfold oddPrimeUpperRepresentativeNumber
  by_cases hb : b N ≤ ell
  · rw [if_pos hb]
    exact Finset.mem_Ico.mpr ⟨hb, by omega⟩
  · rw [if_neg hb]
    unfold oddPrimeRepresented at hrep
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem oddPrimeUpperRepresentativePoolRat_eq_sign (z : ℚ) (p N r ell : ℕ) :
    oddPrimeUpperRepresentativePoolRat z p N r ell =
      oddPrimeUpperRepresentativeSign N ell *
        oddPrimeUpperPoolRat z p N r (oddPrimeUpperRepresentativeNumber p N ell) := by
  by_cases hb : b N ≤ ell <;>
    simp only [oddPrimeUpperRepresentativePoolRat, oddPrimeUpperRepresentativeSign,
      oddPrimeUpperRepresentativeNumber, hb, ite_true, ite_false, one_mul, neg_one_mul]

theorem oddPrimeUpperShearCoeff_sum {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hH : H N ≤ 2 * p) (z : ℚ) (r : Fin (n N))
    (j ell : ℕ) (hell : ell < H N - p) :
    (∑ phys : oddPrimeUpperPhysicalIndex p N,
      oddPrimeUpperPhysicalColumn z p N phys r * oddPrimeUpperShearCoeff p N phys j ell) =
      if oddPrimeRepresented p N ell then
        oddPrimeUpperRepresentativePoolRat z p N r.val ell / ((j - ell : ℕ) : ℚ)
      else 0 := by
  by_cases hrep : oddPrimeRepresented p N ell
  · simp only [oddPrimeUpperShearCoeff, if_pos hrep]
    calc
      _ = (oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ)) *
          ∑ phys : oddPrimeUpperPhysicalIndex p N,
            oddPrimeUpperPhysicalColumn z p N phys r *
              oddPrimeUpperDelta p N phys (oddPrimeUpperRepresentativeNumber p N ell) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro phys _
        ring
      _ = _ := by
        rw [oddPrimeUpperDelta_sum z r _
          (oddPrimeUpperRepresentativeNumber_mem hN hH hell hrep),
          oddPrimeUpperRepresentativePoolRat_eq_sign]
        ring
  · simp only [oddPrimeUpperShearCoeff, if_neg hrep, mul_zero, Finset.sum_const_zero]

theorem rawEntryRat_eq_upper_physical_sum {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hH : H N ≤ 2 * p) (z : ℚ)
    (j : ↥(Finset.Ico (b N) (L N))) (r : Fin (n N)) :
    rawEntryRat z N r.val j.val =
      ∑ phys : oddPrimeUpperPhysicalIndex p N,
        oddPrimeUpperPhysicalColumn z p N phys r * oddPrimeUpperInverseCoeff p N phys j.val := by
  have hpairSum :
      (∑ phys : oddPrimeUpperPhysicalIndex p N,
        oddPrimeUpperPhysicalColumn z p N phys r *
          (if oddPrimeUpperPairIndex p N j.val then
            oddPrimeUpperDelta p N phys (j.val - p) else 0)) =
      if oddPrimeUpperPairIndex p N j.val then
        oddPrimeUpperPoolRat z p N r.val (j.val - p) else 0 := by
    by_cases hp : oddPrimeUpperPairIndex p N j.val
    · simp only [if_pos hp]
      apply oddPrimeUpperDelta_sum
      have hj := Finset.mem_Ico.mp j.property
      unfold oddPrimeUpperPairIndex at hp
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · simp only [if_neg hp, mul_zero, Finset.sum_const_zero]
  have hcentralSum :
      (∑ phys : oddPrimeUpperPhysicalIndex p N,
        oddPrimeUpperPhysicalColumn z p N phys r *
          (if oddPrimeUpperCentralIndex p N j.val then
            (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
              oddPrimeUpperShearCoeff p N phys j.val ell else 0)) =
      if oddPrimeUpperCentralIndex p N j.val then
        (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
          if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r.val ell / ((j.val - ell : ℕ) : ℚ)
          else 0
      else 0 := by
    by_cases hc : oddPrimeUpperCentralIndex p N j.val
    · simp only [if_pos hc]
      calc
        _ = (p : ℚ) * ∑ phys : oddPrimeUpperPhysicalIndex p N,
              ∑ ell ∈ Finset.range (H N - p),
                oddPrimeUpperPhysicalColumn z p N phys r *
                  oddPrimeUpperShearCoeff p N phys j.val ell := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro phys _
          apply Finset.sum_congr rfl
          intro ell _
          ring
        _ = (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
              ∑ phys : oddPrimeUpperPhysicalIndex p N,
                oddPrimeUpperPhysicalColumn z p N phys r *
                  oddPrimeUpperShearCoeff p N phys j.val ell := by
          rw [Finset.sum_comm]
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro ell hell
          exact oddPrimeUpperShearCoeff_sum hN hH z r j.val ell (Finset.mem_range.mp hell)
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]
  rw [rawEntryRat_eq_upper_pool_inverse hH]
  symm
  simp only [oddPrimeUpperInverseCoeff, mul_sub, Finset.sum_sub_distrib]
  rw [oddPrimeUpperDelta_sum z r j.val j.property, hpairSum, hcentralSum]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPrimeUpperPhysical_loss_eq {N p : ℕ} (hN : 0 < N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p) :
    min (2 * n N) (min (n N + oddPrimeUpperRetainedSize p N)
      (2 * oddPrimeUpperRetainedSize p N + oddPrimeUpperPairedSize p N +
        oddPrimeUpperExceptionalSize p N)) = oddUpperCountLoss N p := by
  have hR : oddPrimeUpperRetainedSize p N = oddUpperRankCount N p := by
    simpa only [oddPrimeUpperRetainedSize, Fintype.card_coe,
      oddPrimeUpperRetainedSet_card] using oddUpperRetainedCount_eq N p hN hpH hH
  have hS : oddPrimeUpperPairedSize p N + oddPrimeUpperExceptionalSize p N =
      oddUpperSimpleCount N p := by
    simpa only [oddPrimeUpperPairedSize, oddPrimeUpperExceptionalSize, Fintype.card_coe,
      oddPrimeUpperPairHighSet_card, oddPrimeUpperExceptionalSet_card] using
        oddUpperSimplePhysicalCount_eq N p
  unfold oddUpperCountLoss
  omega

theorem oddPrimeUpperPhysicalCombination_valuation_lower {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (g : oddPrimeUpperPhysicalIndex p N → Fin (n N) → ℚ)
    (hg : ∀ i k, ((g i k).den : ZMod p) ≠ 0) :
    -(oddUpperCountLoss N p : ℤ) ≤ padicValRat p
      (Matrix.det (Matrix.of fun r k : Fin (n N) =>
        ∑ i, oddPrimeUpperPhysicalColumn z p N i r * g i k)) := by
  have h := oddPhysicalCombination_valuation_lower
    (p := p) (n := n N) (R := oddPrimeUpperRetainedSize p N)
    (B := oddPrimeUpperPairedSize p N) (C := oddPrimeUpperCentralSize p N)
    (e := oddPrimeUpperExceptionalSize p N)
    (oddPrimeUpperRetainedVector z p N) (oddPrimeUpperPairedVector z p N)
    (oddPrimeUpperIntegralVector z p N) (oddPrimeUpperExceptionalVector p N)
    (oddPrimeUpperExceptionalCoeff p N) g
    (oddPrimeUpperRetainedVector_den_ne_zero hp2 hHsq z hz)
    (oddPrimeUpperPairedVector_den_ne_zero hp2 hN hpH hH z hz)
    (oddPrimeUpperIntegralVector_den_ne_zero hp2 hN hpH hH z hz)
    oddPrimeUpperExceptionalVector_den_ne_zero
    oddPrimeUpperExceptionalCoeff_den_ne_zero hg
  simpa only [oddPrimeUpperPhysical_loss_eq hN hpH hH, oddPrimeUpperPhysicalColumn] using h

theorem rawMinorRat_odd_upper_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    -(oddUpperCountLoss N p : ℤ) ≤ padicValRat p (rawMinorRat z N c) := by
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => rawEntryRat z N r.val (c k).val) =
        (Matrix.of fun r k : Fin (n N) => ∑ i : oddPrimeUpperPhysicalIndex p N,
          oddPrimeUpperPhysicalColumn z p N i r * oddPrimeUpperInverseCoeff p N i (c k).val) := by
    ext r k
    exact rawEntryRat_eq_upper_physical_sum hN hH z (c k) r
  rw [rawMinorRat, hmatrix]
  exact oddPrimeUpperPhysicalCombination_valuation_lower hp2 hN hpH hH hHsq z hz
    (fun i k => oddPrimeUpperInverseCoeff p N i (c k).val)
    (fun i k => oddPrimeUpperInverseCoeff_den_ne_zero i (c k).val)

theorem determinantRat_odd_upper_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(oddUpperCountLoss N p : ℤ) ≤ padicValRat p (determinantRat z N) := by
  rw [determinantRat_eq_sum_raw_choices]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro c hc
  have hminor := rawMinorRat_odd_upper_valuation hp2 hN hpH hH hHsq z hz c
  have hint := int_prime_valuation_nonneg p (∏ k, rawFilterInt N (c k) k)
  simpa only [zero_add] using prime_mul_valuation_lower
    (((∏ k, rawFilterInt N (c k) k : ℤ) : ℚ)) (rawMinorRat z N c)
    0 (-(oddUpperCountLoss N p : ℤ)) (by omega) hint hminor

theorem determinantRat_odd_prime_loss_upper {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hv : -(oddUpperCountLoss N p : ℝ) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
    exact_mod_cast determinantRat_odd_upper_valuation hp2 hN hpH hH hHsq z hz
  rw [oddUpperCountLoss_eq N p hN hH] at hv
  simpa only [neg_mul] using hv

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open Filter
open scoped Topology BigOperators

theorem determinantRat_odd_prime_large_loss_lower {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N)
    (hcut : 2 * Real.sqrt (H N) < (p : ℝ))
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hsquare : H N < p ^ 2 := by
    have h := large_prime_cutoff_square hcut
    omega
  by_cases hbelow : p ≤ H N
  · by_cases hlower : 2 * p ≤ H N
    · exact determinantRat_odd_lower_loss hp2 hN hlower hsquare z hz
    · exact determinantRat_odd_prime_loss_upper hp2 hN hbelow (by omega) hsquare z hz
  · exact determinantRat_odd_prime_loss_above_degrees hp2 hN (by omega) z hz

theorem largeOddPrimeContribution_eventually_lower (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -(8609 / 4608 : ℝ) - ε ≤ largeOddPrimeContribution z N / (n N : ℝ) ^ 2 := by
  filter_upwards [large_prime_witness_den_eventually z,
    oddPrimeLoss_large_prime_normalized_eventually_upper hε,
    eventually_gt_atTop (0 : ℕ)] with N hden hloss hN
  have hn : 0 < (n N : ℝ) ^ 2 := by unfold n; positivity
  have hsum : -(N : ℝ) *
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
        (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log p) ≤ largeOddPrimeContribution z N := by
    unfold largeOddPrimeContribution
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨_, hprime, hcut⟩ := Finset.mem_filter.mp hp
    have : Fact p.Prime := ⟨hprime⟩
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      have h := (smallOddPrimeCutoff_bounds hN).1
      norm_num only [Nat.cast_ofNat] at hcut
      linarith
    have hv := determinantRat_odd_prime_large_loss_lower hp2 hN hcut z (hden p hcut)
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hv hlog
  have hnorm := div_le_div_of_nonneg_right hsum hn.le
  have heq : -(N : ℝ) *
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
        (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log p) / (n N : ℝ) ^ 2 =
      -((N : ℝ) *
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
        (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log p) / (n N : ℝ) ^ 2) := by ring
  rw [heq] at hnorm
  linarith

end InternalCatalan

end



namespace InternalCatalan
open Filter
open scoped Topology

theorem determinantRat_finite_place_eventually_lower (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(8609 / 4608 : ℝ) - (505 / 4608 : ℝ) * Real.log 2 - ε ≤
        Real.log |(determinantRat z N : ℝ)| / (n N : ℝ) ^ 2 := by
  have he : (0 : ℝ) < ε / 2 := by positivity
  filter_upwards [determinantRat_without_large_primes_eventually_lower z he,
    largeOddPrimeContribution_eventually_lower z he] with N hpartial hlarge
  intro hdet
  have h := hpartial hdet
  rw [sub_div] at h
  linarith

theorem determinantRat_finite_place_threshold (z : ℚ) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(229084 / 100000 : ℝ) <
        Real.log |(determinantRat z N : ℝ)| / (n N : ℝ) ^ 2 -
          (1 / 2 : ℝ) * Real.log 2 := by
  let gap : ℝ := -(8609 / 4608 : ℝ) -
    ((1 / 2 : ℝ) + (505 / 4608 : ℝ)) * Real.log 2 + 229084 / 100000
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [finitePlace_constant_gt_threshold]
  filter_upwards [determinantRat_finite_place_eventually_lower z
    (show 0 < gap / 2 by positivity)] with N hN
  intro hdet
  have h := hN hdet
  dsimp [gap] at hgap h
  nlinarith

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan
open Filter
open scoped Topology

theorem solution (z : ℚ) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(229084 / 100000 : ℝ) <
        Real.log |(determinantRat z N : ℝ)| / (n N : ℝ) ^ 2 -
          (1 / 2 : ℝ) * Real.log 2 := by
  first
  | exact @OAI.InternalCatalan.determinantRat_finite_place_threshold
  | (apply OAI.InternalCatalan.determinantRat_finite_place_threshold <;> assumption)

end
