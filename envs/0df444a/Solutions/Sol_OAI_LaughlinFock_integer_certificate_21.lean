-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:31:34.193227+00:00
-- url     : https://prove2.me/submissions/eec75c7a-17a7-4277-b36a-4b62ce945b30

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_1
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_11
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_13
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_15
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_17
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_19
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_21
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_3
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_5
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_7
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_21_9
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse21. -/
namespace LaughlinFock

theorem collectedFourChecked_21 : collectedFourTerms 21 = collectedFourData_21 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_21 : highestFourOccupations 21 = {{0,1,2,19}, {0,1,3,18}, {0,1,4,17}, {0,1,5,16}, {0,1,6,15}, {0,1,7,14}, {0,1,8,13}, {0,1,9,12}, {0,1,10,11}, {0,2,3,17}, {0,2,4,16}, {0,2,5,15}, {0,2,6,14}, {0,2,7,13}, {0,2,8,12}, {0,2,9,11}, {0,3,4,15}, {0,3,5,14}, {0,3,6,13}, {0,3,7,12}, {0,3,8,11}, {0,3,9,10}, {0,4,5,13}, {0,4,6,12}, {0,4,7,11}, {0,4,8,10}, {0,5,6,11}, {0,5,7,10}, {0,5,8,9}, {0,6,7,9}, {1,2,3,16}, {1,2,4,15}, {1,2,5,14}, {1,2,6,13}, {1,2,7,12}, {1,2,8,11}, {1,2,9,10}, {1,3,4,14}, {1,3,5,13}, {1,3,6,12}, {1,3,7,11}, {1,3,8,10}, {1,4,5,12}, {1,4,6,11}, {1,4,7,10}, {1,4,8,9}, {1,5,6,10}, {1,5,7,9}, {1,6,7,8}, {2,3,4,13}, {2,3,5,12}, {2,3,6,11}, {2,3,7,10}, {2,3,8,9}, {2,4,5,11}, {2,4,6,10}, {2,4,7,9}, {2,5,6,9}, {2,5,7,8}, {3,4,5,10}, {3,4,6,9}, {3,4,7,8}, {3,5,6,8}, {4,5,6,7}} := by
  decide +kernel

theorem fourYNumber_21_1_1 :
    (collectedFourTrace 21 1 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (-234648598012788536548705681690743/83886080000000000000) := by
  decide +kernel

theorem fourYNumber_21_3_1 :
    (collectedFourTrace 21 3 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (128874713188638154430356187885361/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_21_3_3 :
    (collectedFourTrace 21 3 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (-89109343832838073782565478877927/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_21_5_1 :
    (collectedFourTrace 21 5 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (6270682580043219642783111633/16777216000000000000) := by
  decide +kernel

theorem fourYNumber_21_5_3 :
    (collectedFourTrace 21 5 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (140306726251072355149640506041/167772160000000000000) := by
  decide +kernel

theorem fourYNumber_21_5_5 :
    (collectedFourTrace 21 5 5 collectedFourData_21 : ℚ) / fourCommonDenominator = (-5638121704563113630737651779/16777216000000000000) := by
  decide +kernel

theorem fourYNumber_21_7_1 :
    (collectedFourTrace 21 7 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (-6042544634844584151223719109329/671088640000000000000) := by
  decide +kernel

theorem fourYNumber_21_7_3 :
    (collectedFourTrace 21 7 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (803074471330315088847985265223/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_21_7_5 :
    (collectedFourTrace 21 7 5 collectedFourData_21 : ℚ) / fourCommonDenominator = (19891972635951350629406534823/134217728000000000000) := by
  decide +kernel

theorem fourYNumber_21_7_7 :
    (collectedFourTrace 21 7 7 collectedFourData_21 : ℚ) / fourCommonDenominator = (-500887997448748544894883831207/5368709120000000000000) := by
  decide +kernel

theorem fourYNumber_21_9_1 :
    (collectedFourTrace 21 9 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (1187993206113164578676205684027/167772160000000000000) := by
  decide +kernel

theorem fourYNumber_21_9_3 :
    (collectedFourTrace 21 9 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (-320742271871519438351384482509/1677721600000000000000) := by
  decide +kernel

theorem fourYNumber_21_9_5 :
    (collectedFourTrace 21 9 5 collectedFourData_21 : ℚ) / fourCommonDenominator = (-526714179453404230953465801/6710886400000000000) := by
  decide +kernel

theorem fourYNumber_21_9_7 :
    (collectedFourTrace 21 9 7 collectedFourData_21 : ℚ) / fourCommonDenominator = (76124470629698703209013437421/1342177280000000000000) := by
  decide +kernel

theorem fourYNumber_21_9_9 :
    (collectedFourTrace 21 9 9 collectedFourData_21 : ℚ) / fourCommonDenominator = (-12018851946390543258370025583/335544320000000000000) := by
  decide +kernel

theorem fourYNumber_21_11_1 :
    (collectedFourTrace 21 11 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (-1778372107681260395143472115483/335544320000000000000) := by
  decide +kernel

theorem fourYNumber_21_11_3 :
    (collectedFourTrace 21 11 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (562059596029051670113407784941/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_21_11_5 :
    (collectedFourTrace 21 11 5 collectedFourData_21 : ℚ) / fourCommonDenominator = (3299803841527864774758187533/67108864000000000000) := by
  decide +kernel

theorem fourYNumber_21_11_7 :
    (collectedFourTrace 21 11 7 collectedFourData_21 : ℚ) / fourCommonDenominator = (-102710567885345352527324078349/2684354560000000000000) := by
  decide +kernel

theorem fourYNumber_21_11_9 :
    (collectedFourTrace 21 11 9 collectedFourData_21 : ℚ) / fourCommonDenominator = (16508910094239456529035425487/671088640000000000000) := by
  decide +kernel

theorem fourYNumber_21_11_11 :
    (collectedFourTrace 21 11 11 collectedFourData_21 : ℚ) / fourCommonDenominator = (-22859632155862339731192645423/1342177280000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_1 :
    (collectedFourTrace 21 13 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (3421529235582403416771066790023/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_3 :
    (collectedFourTrace 21 13 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (-1160433329158398969375622681761/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_5 :
    (collectedFourTrace 21 13 5 collectedFourData_21 : ℚ) / fourCommonDenominator = (-5728719801694801014637510977/167772160000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_7 :
    (collectedFourTrace 21 13 7 collectedFourData_21 : ℚ) / fourCommonDenominator = (186761849648099558221472372289/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_9 :
    (collectedFourTrace 21 13 9 collectedFourData_21 : ℚ) / fourCommonDenominator = (-30331843016349867488456747787/1677721600000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_11 :
    (collectedFourTrace 21 13 11 collectedFourData_21 : ℚ) / fourCommonDenominator = (42192733869700877570394249963/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_21_13_13 :
    (collectedFourTrace 21 13 13 collectedFourData_21 : ℚ) / fourCommonDenominator = (-78077457933297171053368086423/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_1 :
    (collectedFourTrace 21 15 1 collectedFourData_21 : ℚ) / fourCommonDenominator = (-366368465148827393952514902087/134217728000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_3 :
    (collectedFourTrace 21 15 3 collectedFourData_21 : ℚ) / fourCommonDenominator = (129343096918795330831303876833/1342177280000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_5 :
    (collectedFourTrace 21 15 5 collectedFourData_21 : ℚ) / fourCommonDenominator = (2867595547173532199600893317/134217728000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_7 :
    (collectedFourTrace 21 15 7 collectedFourData_21 : ℚ) / fourCommonDenominator = (-19299770582440975858393235073/1073741824000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_9 :
    (collectedFourTrace 21 15 9 collectedFourData_21 : ℚ) / fourCommonDenominator = (3155784219706520761092961227/268435456000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_11 :
    (collectedFourTrace 21 15 11 collectedFourData_21 : ℚ) / fourCommonDenominator = (-4402799920270527426300877227/536870912000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_13 :
    (collectedFourTrace 21 15 13 collectedFourData_21 : ℚ) / fourCommonDenominator = (8160844785649882576623812439/1342177280000000000000) := by
  decide +kernel

theorem fourYNumber_21_15_15 :
    (collectedFourTrace 21 15 15 collectedFourData_21 : ℚ) / fourCommonDenominator = (-4269467008484810944634153331/1073741824000000000000) := by
  decide +kernel

theorem fourYNumber_21_17_1 :
    (collectedFourTrace 21 17 1 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_3 :
    (collectedFourTrace 21 17 3 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_5 :
    (collectedFourTrace 21 17 5 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_7 :
    (collectedFourTrace 21 17 7 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_9 :
    (collectedFourTrace 21 17 9 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_11 :
    (collectedFourTrace 21 17 11 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_13 :
    (collectedFourTrace 21 17 13 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_15 :
    (collectedFourTrace 21 17 15 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_17_17 :
    (collectedFourTrace 21 17 17 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_1 :
    (collectedFourTrace 21 19 1 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_3 :
    (collectedFourTrace 21 19 3 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_5 :
    (collectedFourTrace 21 19 5 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_7 :
    (collectedFourTrace 21 19 7 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_9 :
    (collectedFourTrace 21 19 9 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_11 :
    (collectedFourTrace 21 19 11 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_13 :
    (collectedFourTrace 21 19 13 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_15 :
    (collectedFourTrace 21 19 15 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_17 :
    (collectedFourTrace 21 19 17 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_19_19 :
    (collectedFourTrace 21 19 19 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_1 :
    (collectedFourTrace 21 21 1 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_3 :
    (collectedFourTrace 21 21 3 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_5 :
    (collectedFourTrace 21 21 5 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_7 :
    (collectedFourTrace 21 21 7 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_9 :
    (collectedFourTrace 21 21 9 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_11 :
    (collectedFourTrace 21 21 11 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_13 :
    (collectedFourTrace 21 21 13 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_15 :
    (collectedFourTrace 21 21 15 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_17 :
    (collectedFourTrace 21 21 17 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_19 :
    (collectedFourTrace 21 21 19 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_21_21_21 :
    (collectedFourTrace 21 21 21 collectedFourData_21 : ℚ) / fourCommonDenominator = 0 := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_21 (r s : CopyLabel 21) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 21 r s = fourYData_21 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_21 collectedFourChecked_21]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_21_1_1
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
  · have h : (19:ℕ) ≤ 1 := hrs
    omega
  · have h : (21:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_21_3_1
  · exact fourYNumber_21_3_3
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
  · have h : (19:ℕ) ≤ 3 := hrs
    omega
  · have h : (21:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_21_5_1
  · exact fourYNumber_21_5_3
  · exact fourYNumber_21_5_5
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
  · have h : (19:ℕ) ≤ 5 := hrs
    omega
  · have h : (21:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_21_7_1
  · exact fourYNumber_21_7_3
  · exact fourYNumber_21_7_5
  · exact fourYNumber_21_7_7
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
  · have h : (19:ℕ) ≤ 7 := hrs
    omega
  · have h : (21:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_21_9_1
  · exact fourYNumber_21_9_3
  · exact fourYNumber_21_9_5
  · exact fourYNumber_21_9_7
  · exact fourYNumber_21_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · have h : (19:ℕ) ≤ 9 := hrs
    omega
  · have h : (21:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_21_11_1
  · exact fourYNumber_21_11_3
  · exact fourYNumber_21_11_5
  · exact fourYNumber_21_11_7
  · exact fourYNumber_21_11_9
  · exact fourYNumber_21_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · have h : (19:ℕ) ≤ 11 := hrs
    omega
  · have h : (21:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_21_13_1
  · exact fourYNumber_21_13_3
  · exact fourYNumber_21_13_5
  · exact fourYNumber_21_13_7
  · exact fourYNumber_21_13_9
  · exact fourYNumber_21_13_11
  · exact fourYNumber_21_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · have h : (21:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_21_15_1
  · exact fourYNumber_21_15_3
  · exact fourYNumber_21_15_5
  · exact fourYNumber_21_15_7
  · exact fourYNumber_21_15_9
  · exact fourYNumber_21_15_11
  · exact fourYNumber_21_15_13
  · exact fourYNumber_21_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · have h : (21:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_21_17_1
  · exact fourYNumber_21_17_3
  · exact fourYNumber_21_17_5
  · exact fourYNumber_21_17_7
  · exact fourYNumber_21_17_9
  · exact fourYNumber_21_17_11
  · exact fourYNumber_21_17_13
  · exact fourYNumber_21_17_15
  · exact fourYNumber_21_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · have h : (21:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_21_19_1
  · exact fourYNumber_21_19_3
  · exact fourYNumber_21_19_5
  · exact fourYNumber_21_19_7
  · exact fourYNumber_21_19_9
  · exact fourYNumber_21_19_11
  · exact fourYNumber_21_19_13
  · exact fourYNumber_21_19_15
  · exact fourYNumber_21_19_17
  · exact fourYNumber_21_19_19
  · have h : (21:ℕ) ≤ 19 := hrs
    omega
  · exact fourYNumber_21_21_1
  · exact fourYNumber_21_21_3
  · exact fourYNumber_21_21_5
  · exact fourYNumber_21_21_7
  · exact fourYNumber_21_21_9
  · exact fourYNumber_21_21_11
  · exact fourYNumber_21_21_13
  · exact fourYNumber_21_21_15
  · exact fourYNumber_21_21_17
  · exact fourYNumber_21_21_19
  · exact fourYNumber_21_21_21

theorem fourYChecked_21 (r s : CopyLabel 21) :
    integerRowsFourTrace 21 r s = fourYData_21 r s := by
  have hh : ∀ r s : CopyLabel 21, fourYData_21 r s = fourYData_21 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_21 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_21 s r (by omega), hh]

theorem fourHighestChecked_21 : ∀ r : CopyLabel 21, ∀ A∈highestFourOccupations 21,
    kernelHighestEntry 21 r A = highestLookup fourHighestCache_21 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_21_1
  · exact fourHighestNumber_21_3
  · exact fourHighestNumber_21_5
  · exact fourHighestNumber_21_7
  · exact fourHighestNumber_21_9
  · exact fourHighestNumber_21_11
  · exact fourHighestNumber_21_13
  · exact fourHighestNumber_21_15
  · exact fourHighestNumber_21_17
  · exact fourHighestNumber_21_19
  · exact fourHighestNumber_21_21

theorem fourZChecked_21 (r s : CopyLabel 21) :
    integerFourGram 21 r s = fourZData_21 r s := by
  rw [integerFourGram_cached 21 fourHighestCache_21 fourHighestChecked_21]
  have h : ∀ r s : CopyLabel 21, cachedFourGram 21 fourHighestCache_21 r s = fourZData_21 r s := by
    simp only [cachedFourGram, fourOccupations_21]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_21 :
    fourZData_21 * (Matrix.diagonal (fun r : CopyLabel 21 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 21 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 21 => rationalCopyDiagonal 21 r.val.val) *
        fourYData_21 * Matrix.diagonal (fun r : CopyLabel 21 => rationalCopyDiagonal 21 r.val.val)) *
      fourZData_21 = fourLData_21 * Matrix.diagonal fourPivotData_21 * (fourLData_21)ᵀ := by
  have h : ∀ r s : CopyLabel 21,
      (fourZData_21 * (Matrix.diagonal (fun r : CopyLabel 21 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 21 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 21 => rationalCopyDiagonal 21 r.val.val) *
          fourYData_21 * Matrix.diagonal (fun r : CopyLabel 21 => rationalCopyDiagonal 21 r.val.val)) *
        fourZData_21 : Matrix (CopyLabel 21) (CopyLabel 21) ℚ) r s =
      (fourLData_21 * Matrix.diagonal fourPivotData_21 * (fourLData_21)ᵀ : Matrix (CopyLabel 21) (CopyLabel 21) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_21 : ∀ r, 0 ≤ fourPivotData_21 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_21, copyDiagonalData]

theorem integer_certificate_21_oai :
    ((integerCompression 21).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_21) (fourPivotData_21) _ fourPivotChecked_21
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 21 = fourYData_21 from Matrix.ext fourYChecked_21,
    show integerFourGram 21 = fourZData_21 from Matrix.ext fourZChecked_21]
  exact fourLDLChecked_21

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_21_oai := @OAI.LaughlinFock.integer_certificate_21_oai
