-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_0_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:10:41.648252+00:00
-- url     : https://prove2.me/submissions/b62856cf-c0c0-4ae3-aec5-954bd0014b16

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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






theorem rowD_eq_zero_of_distance_zero {N r : ℕ} (hd : rowDistance N r = 0) :
    rowD N r = 0 := by
  simp [rowD, hd]





















theorem fixed_rowDistance_le44 (r : Fin 49) : rowDistance 1 r.val ≤ 44 := by
  have hr := r.isLt
  unfold rowDistance rowOffset g
  omega

theorem fixed_rowP_coeff_eq_zero_below18 (r : Fin 49) {i : ℕ} (hi : i < 18) :
    (rowP 1 r.val).coeff i = 0 := by
  have hdist := fixed_rowDistance_le44 r
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ 18 _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance 1 r.val) _
  · simp [Chebyshev.natDegree_T]
  · change rowDistance 1 r.val < 63
    omega
  · change j < 63 - 1 - rowDistance 1 r.val
    omega

theorem fixed_rowD_coeff_eq_zero_below19 (r : Fin 49) {i : ℕ} (hi : i < 19) :
    (rowD 1 r.val).coeff i = 0 := by
  by_cases hd : rowDistance 1 r.val = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · have hdist := fixed_rowDistance_le44 r
    unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ 19 _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance 1 r.val - 1) _
    · simp [Chebyshev.natDegree_U]
    · change rowDistance 1 r.val - 1 < 63
      omega
    · change j < 63 - 1 - (rowDistance 1 r.val - 1)
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

def fixedFilteredMomentRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 5, filterCoeffRat 1 v * momentRat i (7 + k + v)

def fixedFilteredZetaRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 5, filterCoeffRat 1 v * zetaRat i (7 + k + v)

theorem fixedBaseEntry_dot_filtered (r : Fin 49) (k : Fin 48) :
    fixedBaseEntryRat r k =
      (∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
        fixedFilteredMomentRat i k.val) -
      (3 / 2 : ℚ) * ∑ i ∈ Finset.range 65,
        ((rowD 1 r.val).coeff i : ℚ) * fixedFilteredZetaRat i k.val := by
  change (∑ v ∈ Finset.range 5,
    filterCoeffRat 1 v * rawEntryRat 0 1 r.val (7 + k.val + v)) = _
  simp_rw [rawEntryRat_zero]
  change (∑ v ∈ Finset.range 5, filterCoeffRat 1 v *
    ((∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
      momentRat i (7 + k.val + v)) -
    (3 / 2 : ℚ) * ∑ i ∈ Finset.range 65, ((rowD 1 r.val).coeff i : ℚ) *
      zetaRat i (7 + k.val + v))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  unfold fixedFilteredMomentRat fixedFilteredZetaRat
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan



















open scoped BigOperators


























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
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn0
namespace OAI


noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment0_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 0 = (fixedClearedMoment0 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 0 = (fixedClearedMoment0 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn1
namespace OAI


noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment1_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 1 = (fixedClearedMoment1 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 1 = (fixedClearedMoment1 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn10
namespace OAI


noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment10_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 10 = (fixedClearedMoment10 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 10 = (fixedClearedMoment10 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn11
namespace OAI


noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment11_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 11 = (fixedClearedMoment11 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 11 = (fixedClearedMoment11 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn2
namespace OAI


noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment2_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 2 = (fixedClearedMoment2 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 2 = (fixedClearedMoment2 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn3
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment3_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 3 = (fixedClearedMoment3 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 3 = (fixedClearedMoment3 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn4
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment4_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 4 = (fixedClearedMoment4 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 4 = (fixedClearedMoment4 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn5
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment5_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 5 = (fixedClearedMoment5 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 5 = (fixedClearedMoment5 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn6
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment6_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 6 = (fixedClearedMoment6 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 6 = (fixedClearedMoment6 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn7
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment7_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 7 = (fixedClearedMoment7 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 7 = (fixedClearedMoment7 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn8
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment8_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 8 = (fixedClearedMoment8 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 8 = (fixedClearedMoment8 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn9
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment9_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 9 = (fixedClearedMoment9 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 9 = (fixedClearedMoment9 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn0
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta0_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 0 = (fixedClearedZeta0 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 0 = (fixedClearedZeta0 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn1
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta1_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 1 = (fixedClearedZeta1 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 1 = (fixedClearedZeta1 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn10
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta10_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 10 = (fixedClearedZeta10 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 10 = (fixedClearedZeta10 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn11
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta11_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 11 = (fixedClearedZeta11 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 11 = (fixedClearedZeta11 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn2
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta2_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 2 = (fixedClearedZeta2 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 2 = (fixedClearedZeta2 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn3
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta3_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 3 = (fixedClearedZeta3 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 3 = (fixedClearedZeta3 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn4
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta4_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 4 = (fixedClearedZeta4 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 4 = (fixedClearedZeta4 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedColumnsAll
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta5_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 5 = (fixedClearedZeta5 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 5 = (fixedClearedZeta5 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta6_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 6 = (fixedClearedZeta6 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 6 = (fixedClearedZeta6 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta7_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 7 = (fixedClearedZeta7 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 7 = (fixedClearedZeta7 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta8_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 8 = (fixedClearedZeta8 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 8 = (fixedClearedZeta8 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta9_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 9 = (fixedClearedZeta9 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 9 = (fixedClearedZeta9 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

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
-- module Solutions.OAICatalan.Split.FixedBase
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): the integrality and the
mod-101 reduction of the fixed matrix, by groups of columns. -/

namespace OAI

namespace InternalCatalan

theorem splitIntegerFractionSum
    (s : Finset ℕ) (p a : ℕ → ℤ) (f : ℕ → ℚ) (d : ℚ)
    (hf : ∀ i ∈ s, (p i : ℚ) * f i = ((p i * a i : ℤ) : ℚ) / d) :
    (∑ i ∈ s, (p i : ℚ) * f i) = ((∑ i ∈ s, p i * a i : ℤ) : ℚ) / d := by
  rw [Int.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [div_eq_mul_inv] using hf i hi


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Split.IntBaseCast
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): integrality of the
fixed integer base, by groups of columns. -/

namespace OAI

namespace InternalCatalan

theorem splitFilteredMoment_cleared_c0_11 (i : ℕ) (k : Fin 48) (hk : 0 ≤ k.val ∧ k.val < 12)
    (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i k.val = (fixedClearedMoment i k : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  obtain ⟨k, hk'⟩ := k
  obtain ⟨hka, hkb⟩ := hk
  simp only at hka hkb
  interval_cases k
  · exact fixedFilteredMoment0_cleared i hlo hhi
  · exact fixedFilteredMoment1_cleared i hlo hhi
  · exact fixedFilteredMoment2_cleared i hlo hhi
  · exact fixedFilteredMoment3_cleared i hlo hhi
  · exact fixedFilteredMoment4_cleared i hlo hhi
  · exact fixedFilteredMoment5_cleared i hlo hhi
  · exact fixedFilteredMoment6_cleared i hlo hhi
  · exact fixedFilteredMoment7_cleared i hlo hhi
  · exact fixedFilteredMoment8_cleared i hlo hhi
  · exact fixedFilteredMoment9_cleared i hlo hhi
  · exact fixedFilteredMoment10_cleared i hlo hhi
  · exact fixedFilteredMoment11_cleared i hlo hhi

theorem splitFilteredZeta_cleared_c0_11 (i : ℕ) (k : Fin 48) (hk : 0 ≤ k.val ∧ k.val < 12)
    (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i k.val = (fixedClearedZeta i k : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  obtain ⟨k, hk'⟩ := k
  obtain ⟨hka, hkb⟩ := hk
  simp only at hka hkb
  interval_cases k
  · exact fixedFilteredZeta0_cleared i hlo hhi
  · exact fixedFilteredZeta1_cleared i hlo hhi
  · exact fixedFilteredZeta2_cleared i hlo hhi
  · exact fixedFilteredZeta3_cleared i hlo hhi
  · exact fixedFilteredZeta4_cleared i hlo hhi
  · exact fixedFilteredZeta5_cleared i hlo hhi
  · exact fixedFilteredZeta6_cleared i hlo hhi
  · exact fixedFilteredZeta7_cleared i hlo hhi
  · exact fixedFilteredZeta8_cleared i hlo hhi
  · exact fixedFilteredZeta9_cleared i hlo hhi
  · exact fixedFilteredZeta10_cleared i hlo hhi
  · exact fixedFilteredZeta11_cleared i hlo hhi

theorem fixedIntegerBaseCanonical_cast_cols_0_11 (r : Fin 49) (k : Fin 48)
    (hk : 0 ≤ k.val ∧ k.val < 12) :
    (fixedIntegerBaseCanonical r k : ℚ) = (854041599922236190937524347070927377276592590715779683450880000 : ℚ) * fixedBaseEntryRat r k := by
  have hP : (∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
      fixedFilteredMomentRat i k.val) =
      ((∑ i ∈ Finset.range 65, (rowP 1 r.val).coeff i * fixedClearedMoment i k : ℤ) : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 := by
    apply splitIntegerFractionSum
    intro i hi
    have hhi : i < 65 := Finset.mem_range.mp hi
    by_cases hlo : 18 ≤ i
    · rw [splitFilteredMoment_cleared_c0_11 i k hk hlo hhi, Int.cast_mul]
      ring
    · have hz := fixed_rowP_coeff_eq_zero_below18 r (i := i) (by omega)
      simp [hz]
  have hD : (∑ i ∈ Finset.range 65, ((rowD 1 r.val).coeff i : ℚ) *
      fixedFilteredZetaRat i k.val) =
      ((∑ i ∈ Finset.range 65, (rowD 1 r.val).coeff i * fixedClearedZeta i k : ℤ) : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 := by
    apply splitIntegerFractionSum
    intro i hi
    have hhi : i < 65 := Finset.mem_range.mp hi
    by_cases hlo : 19 ≤ i
    · rw [splitFilteredZeta_cleared_c0_11 i k hk hlo hhi, Int.cast_mul]
      ring
    · have hz := fixed_rowD_coeff_eq_zero_below19 r (i := i) (by omega)
      simp [hz]
  rw [fixedBaseEntry_dot_filtered, hP, hD]
  simp only [fixedIntegerBaseCanonical, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring











end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (k : Fin 48)
    (hk : 0 ≤ k.val ∧ k.val < 12) :
    (fixedIntegerBaseCanonical r k : ℚ) = (854041599922236190937524347070927377276592590715779683450880000 : ℚ) * fixedBaseEntryRat r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_0_11
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_0_11 <;> assumption)

end
