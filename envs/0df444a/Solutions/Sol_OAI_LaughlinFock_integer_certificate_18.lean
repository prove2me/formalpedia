-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_18
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:25:50.212852+00:00
-- url     : https://prove2.me/submissions/c9787f68-979f-4b29-9b28-086ca7ba7c79

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L026
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_collected

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PolynomialPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Positivity. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators
open Polynomial



theorem real_matrix_posSemidef_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    (M.map (algebraMap ℝ ℂ)).PosSemidef := by
  have hH : (M.map (algebraMap ℝ ℂ)).IsHermitian := by
    apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    have h := Matrix.IsHermitian.ext_iff.mp hM.isHermitian i j
    simpa using congrArg (algebraMap ℝ ℂ) h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  have hRe := hM.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hIm := hM.dotProduct_mulVec_nonneg (fun i => (x i).im)
  apply Complex.nonneg_iff.mpr
  constructor
  · have he : (star x ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ x)).re =
        (fun i => (x i).re) ⬝ᵥ (M *ᵥ fun i => (x i).re) +
        (fun i => (x i).im) ⬝ᵥ (M *ᵥ fun i => (x i).im) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.sum_add_distrib,
        Complex.mul_re, Complex.mul_im, Finset.mul_sum]
    rw [he]
    simpa only [star_trivial, Pi.star_apply] using add_nonneg hRe hIm
  · exact (hH.im_star_dotProduct_mulVec_self x).symm



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LDL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L D L. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem rational_ldl_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : Matrix ι ι ℚ) (d : ι → ℚ)
    (he : M = L * Matrix.diagonal d * Lᵀ) (hd : ∀ i, 0 ≤ d i) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  let Lr := L.map (algebraMap ℚ ℝ)
  have hh : (Matrix.diagonal (fun i => (d i : ℝ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hd i
  have hr : (M.map (algebraMap ℚ ℝ)).PosSemidef := by
    have ht : (Lᵀ).map (algebraMap ℚ ℝ) = Lrᴴ := by
      ext i j
      simp [Lr]
    rw [he, Matrix.map_mul, Matrix.map_mul, ht]
    have he' : (Matrix.diagonal d).map (algebraMap ℚ ℝ) =
        Matrix.diagonal (fun i => (d i : ℝ)) := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [he']
    exact hh.mul_mul_conjTranspose_same Lr
  have hc := real_matrix_posSemidef_complex (M.map (algebraMap ℚ ℝ)) hr
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerCoupling_fast (c : ℤ) (z k p : ℕ) :
    integerCoupling c z k p = fastIntegerCoupling c z k p := by
  simp only [integerCoupling, fastIntegerCoupling, Nat.choose_eq_fast_choose]

theorem integerCopyPolynomial_fast (D T r p j k : ℕ) :
    integerCopyPolynomial D T r p j k = fastIntegerCopyPolynomial D T r p j k := by
  simp only [integerCopyPolynomial, fastIntegerCopyPolynomial, integerCoupling_fast]
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1802
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1802. -/
namespace LaughlinFock

theorem collectedFourChecked_18 : collectedFourTerms 18 = collectedFourData_18 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate18Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_18 : highestFourOccupations 18 = {{0,1,2,16}, {0,1,3,15}, {0,1,4,14}, {0,1,5,13}, {0,1,6,12}, {0,1,7,11}, {0,1,8,10}, {0,2,3,14}, {0,2,4,13}, {0,2,5,12}, {0,2,6,11}, {0,2,7,10}, {0,2,8,9}, {0,3,4,12}, {0,3,5,11}, {0,3,6,10}, {0,3,7,9}, {0,4,5,10}, {0,4,6,9}, {0,4,7,8}, {0,5,6,8}, {1,2,3,13}, {1,2,4,12}, {1,2,5,11}, {1,2,6,10}, {1,2,7,9}, {1,3,4,11}, {1,3,5,10}, {1,3,6,9}, {1,3,7,8}, {1,4,5,9}, {1,4,6,8}, {1,5,6,7}, {2,3,4,10}, {2,3,5,9}, {2,3,6,8}, {2,4,5,8}, {2,4,6,7}, {3,4,5,7}} := by
  decide +kernel

theorem fourYNumber_18_1_1 :
    (collectedFourTrace 18 1 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (-66521135019707973636148739444823/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_18_3_1 :
    (collectedFourTrace 18 3 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (252807337181468791157280462398781/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_18_3_3 :
    (collectedFourTrace 18 3 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (-4007199514466721234466894776687/10485760000000000000000) := by
  decide +kernel

theorem fourYNumber_18_5_1 :
    (collectedFourTrace 18 5 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (-3252673886370851574147845456127/4194304000000000000000) := by
  decide +kernel

theorem fourYNumber_18_5_3 :
    (collectedFourTrace 18 5 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (3372146185937105246632585623/83886080000000000000) := by
  decide +kernel

theorem fourYNumber_18_5_5 :
    (collectedFourTrace 18 5 5 collectedFourData_18 : ℚ) / fourCommonDenominator = (-23486105657561204635588697229/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_18_7_1 :
    (collectedFourTrace 18 7 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (5486362141771333842849073567323/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_18_7_3 :
    (collectedFourTrace 18 7 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (-537252564751161309170239296177/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_18_7_5 :
    (collectedFourTrace 18 7 5 collectedFourData_18 : ℚ) / fourCommonDenominator = (13080008728723829467798462239/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_18_7_7 :
    (collectedFourTrace 18 7 7 collectedFourData_18 : ℚ) / fourCommonDenominator = (-26821902960980170260006245841/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_18_9_1 :
    (collectedFourTrace 18 9 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (-2995000631158705240266068943069/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_18_9_3 :
    (collectedFourTrace 18 9 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (326882437778322963441861875919/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_18_9_5 :
    (collectedFourTrace 18 9 5 collectedFourData_18 : ℚ) / fourCommonDenominator = (-561883338175515088890230073/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_18_9_7 :
    (collectedFourTrace 18 9 7 collectedFourData_18 : ℚ) / fourCommonDenominator = (5261464120361048458016212593/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_18_9_9 :
    (collectedFourTrace 18 9 9 collectedFourData_18 : ℚ) / fourCommonDenominator = (-5378965725447864249453406611/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_18_11_1 :
    (collectedFourTrace 18 11 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (969639349882794261211214675001/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_18_11_3 :
    (collectedFourTrace 18 11 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (-446863114834040129604253847973/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_18_11_5 :
    (collectedFourTrace 18 11 5 collectedFourData_18 : ℚ) / fourCommonDenominator = (13256817221098100127860348967/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_18_11_7 :
    (collectedFourTrace 18 11 7 collectedFourData_18 : ℚ) / fourCommonDenominator = (-38369036592682761923577485019/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_18_11_9 :
    (collectedFourTrace 18 11 9 collectedFourData_18 : ℚ) / fourCommonDenominator = (45327067783268824664031633867/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_18_11_11 :
    (collectedFourTrace 18 11 11 collectedFourData_18 : ℚ) / fourCommonDenominator = (-16696042828466646120838082721/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_1 :
    (collectedFourTrace 18 13 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (-1825892225284111905489652320237/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_3 :
    (collectedFourTrace 18 13 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (94926062405918105309169939717/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_5 :
    (collectedFourTrace 18 13 5 collectedFourData_18 : ℚ) / fourCommonDenominator = (-529685184269295692581892949/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_7 :
    (collectedFourTrace 18 13 7 collectedFourData_18 : ℚ) / fourCommonDenominator = (5710729709386883525559892677/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_9 :
    (collectedFourTrace 18 13 9 collectedFourData_18 : ℚ) / fourCommonDenominator = (-16829807573720669915736782433/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_11 :
    (collectedFourTrace 18 13 11 collectedFourData_18 : ℚ) / fourCommonDenominator = (8083429949860810590580083549/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_18_13_13 :
    (collectedFourTrace 18 13 13 collectedFourData_18 : ℚ) / fourCommonDenominator = (-26274961134789366068159533443/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_1 :
    (collectedFourTrace 18 15 1 collectedFourData_18 : ℚ) / fourCommonDenominator = (-1826945530642202491518005975967/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_3 :
    (collectedFourTrace 18 15 3 collectedFourData_18 : ℚ) / fourCommonDenominator = (-57423478077219023517144295899/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_5 :
    (collectedFourTrace 18 15 5 collectedFourData_18 : ℚ) / fourCommonDenominator = (13124154212646099108768591309/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_7 :
    (collectedFourTrace 18 15 7 collectedFourData_18 : ℚ) / fourCommonDenominator = (-18505980504524000026333045251/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_9 :
    (collectedFourTrace 18 15 9 collectedFourData_18 : ℚ) / fourCommonDenominator = (6451412435501569773360954831/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_11 :
    (collectedFourTrace 18 15 11 collectedFourData_18 : ℚ) / fourCommonDenominator = (-3918367451570737029679703889/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_13 :
    (collectedFourTrace 18 15 13 collectedFourData_18 : ℚ) / fourCommonDenominator = (3426033838439075057449574319/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_18_15_15 :
    (collectedFourTrace 18 15 15 collectedFourData_18 : ℚ) / fourCommonDenominator = (-23010186633185192976943168761/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_18_17_1 :
    (collectedFourTrace 18 17 1 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_3 :
    (collectedFourTrace 18 17 3 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_5 :
    (collectedFourTrace 18 17 5 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_7 :
    (collectedFourTrace 18 17 7 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_9 :
    (collectedFourTrace 18 17 9 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_11 :
    (collectedFourTrace 18 17 11 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_13 :
    (collectedFourTrace 18 17 13 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_15 :
    (collectedFourTrace 18 17 15 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_18_17_17 :
    (collectedFourTrace 18 17 17 collectedFourData_18 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_GramCache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram Cache. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerHighestEntry_kernel (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    integerHighestEntry D r A = kernelHighestEntry D r A := by
  simp only [integerHighestEntry, kernelHighestEntry, integerHighestTerm, kernelHighestTerm,
    integerCopyPolynomial_fast]

theorem integerFourGram_cached (D : ℕ) (xs : List (Occupation 24 × List ℚ))
    (h : ∀ r A, A ∈ highestFourOccupations D →
      kernelHighestEntry D r A = highestLookup xs r.val.val A) :
    integerFourGram D = cachedFourGram D xs := by
  ext r s
  apply Finset.sum_congr rfl
  intro A hA
  rw [integerHighestEntry_kernel, integerHighestEntry_kernel, h r A hA, h s A hA]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TraceSymmetry
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Symmetry. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rationalFourFactor_symm {t : ℕ} (D : ℕ) (b c : RowEntry t) :
    rationalFourFactor D b c = rationalFourFactor D c b := by
  unfold rationalFourFactor
  rw [rowFourLevel_symm b c]
  ring

theorem integerFourTrace_symm (D t : ℕ) (a : RowEntry t → ℚ) (r s : CopyLabel D) :
    integerFourTrace D t a r s = integerFourTrace D t a s r := by
  unfold integerFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b, rationalFourFactor_symm D c b]
  split_ifs <;> ring

theorem integerRowsFourTrace_symm (D : ℕ) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = integerRowsFourTrace D s r := by
  unfold integerRowsFourTrace
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl (fun t _ => integerFourTrace_symm D t.val (certificateAlpha t) r s)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate18
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_18 (r s : CopyLabel 18) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 18 r s = fourYData_18 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_18 collectedFourChecked_18]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_18_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · have h : (11:ℕ) ≤ 1 := hrs
    omega
  · have h : (13:ℕ) ≤ 1 := hrs
    omega
  · have h : (15:ℕ) ≤ 1 := hrs
    omega
  · have h : (17:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_18_3_1
  · exact fourYNumber_18_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · have h : (13:ℕ) ≤ 3 := hrs
    omega
  · have h : (15:ℕ) ≤ 3 := hrs
    omega
  · have h : (17:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_18_5_1
  · exact fourYNumber_18_5_3
  · exact fourYNumber_18_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · have h : (15:ℕ) ≤ 5 := hrs
    omega
  · have h : (17:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_18_7_1
  · exact fourYNumber_18_7_3
  · exact fourYNumber_18_7_5
  · exact fourYNumber_18_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · have h : (17:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_18_9_1
  · exact fourYNumber_18_9_3
  · exact fourYNumber_18_9_5
  · exact fourYNumber_18_9_7
  · exact fourYNumber_18_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_18_11_1
  · exact fourYNumber_18_11_3
  · exact fourYNumber_18_11_5
  · exact fourYNumber_18_11_7
  · exact fourYNumber_18_11_9
  · exact fourYNumber_18_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_18_13_1
  · exact fourYNumber_18_13_3
  · exact fourYNumber_18_13_5
  · exact fourYNumber_18_13_7
  · exact fourYNumber_18_13_9
  · exact fourYNumber_18_13_11
  · exact fourYNumber_18_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_18_15_1
  · exact fourYNumber_18_15_3
  · exact fourYNumber_18_15_5
  · exact fourYNumber_18_15_7
  · exact fourYNumber_18_15_9
  · exact fourYNumber_18_15_11
  · exact fourYNumber_18_15_13
  · exact fourYNumber_18_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_18_17_1
  · exact fourYNumber_18_17_3
  · exact fourYNumber_18_17_5
  · exact fourYNumber_18_17_7
  · exact fourYNumber_18_17_9
  · exact fourYNumber_18_17_11
  · exact fourYNumber_18_17_13
  · exact fourYNumber_18_17_15
  · exact fourYNumber_18_17_17

theorem fourYChecked_18 (r s : CopyLabel 18) :
    integerRowsFourTrace 18 r s = fourYData_18 r s := by
  have hh : ∀ r s : CopyLabel 18, fourYData_18 r s = fourYData_18 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_18 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_18 s r (by omega), hh]

theorem fourHighestNumber_18_1 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 1 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_3 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 3 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_5 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 5 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_7 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 7 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_9 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 9 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_11 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 11 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_13 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 13 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_15 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 15 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_17 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨17,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 17 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_18 : ∀ r : CopyLabel 18, ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 r A = highestLookup fourHighestCache_18 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_18_1
  · exact fourHighestNumber_18_3
  · exact fourHighestNumber_18_5
  · exact fourHighestNumber_18_7
  · exact fourHighestNumber_18_9
  · exact fourHighestNumber_18_11
  · exact fourHighestNumber_18_13
  · exact fourHighestNumber_18_15
  · exact fourHighestNumber_18_17

theorem fourZChecked_18 (r s : CopyLabel 18) :
    integerFourGram 18 r s = fourZData_18 r s := by
  rw [integerFourGram_cached 18 fourHighestCache_18 fourHighestChecked_18]
  have h : ∀ r s : CopyLabel 18, cachedFourGram 18 fourHighestCache_18 r s = fourZData_18 r s := by
    simp only [cachedFourGram, fourOccupations_18]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_18 :
    fourZData_18 * (Matrix.diagonal (fun r : CopyLabel 18 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 18 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val) *
        fourYData_18 * Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val)) *
      fourZData_18 = fourLData_18 * Matrix.diagonal fourPivotData_18 * (fourLData_18)ᵀ := by
  have h : ∀ r s : CopyLabel 18,
      (fourZData_18 * (Matrix.diagonal (fun r : CopyLabel 18 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 18 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val) *
          fourYData_18 * Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val)) *
        fourZData_18 : Matrix (CopyLabel 18) (CopyLabel 18) ℚ) r s =
      (fourLData_18 * Matrix.diagonal fourPivotData_18 * (fourLData_18)ᵀ : Matrix (CopyLabel 18) (CopyLabel 18) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_18 : ∀ r, 0 ≤ fourPivotData_18 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_18, copyDiagonalData]

theorem integer_certificate_18_oai :
    ((integerCompression 18).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_18) (fourPivotData_18) _ fourPivotChecked_18
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 18 = fourYData_18 from Matrix.ext fourYChecked_18,
    show integerFourGram 18 = fourZData_18 from Matrix.ext fourZChecked_18]
  exact fourLDLChecked_18

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_18_oai := @OAI.LaughlinFock.integer_certificate_18_oai
