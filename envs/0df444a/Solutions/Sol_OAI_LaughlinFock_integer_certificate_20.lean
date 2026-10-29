-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:26:56.166566+00:00
-- url     : https://prove2.me/submissions/8c24f005-c086-4d78-897a-0a4a9c1ad518

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L035
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_1
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_11
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_13
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_15
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_17
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_19
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_3
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_5
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_7
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_20_9
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse20. -/
namespace LaughlinFock

theorem collectedFourChecked_20 : collectedFourTerms 20 = collectedFourData_20 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_20 : highestFourOccupations 20 = {{0,1,2,18}, {0,1,3,17}, {0,1,4,16}, {0,1,5,15}, {0,1,6,14}, {0,1,7,13}, {0,1,8,12}, {0,1,9,11}, {0,2,3,16}, {0,2,4,15}, {0,2,5,14}, {0,2,6,13}, {0,2,7,12}, {0,2,8,11}, {0,2,9,10}, {0,3,4,14}, {0,3,5,13}, {0,3,6,12}, {0,3,7,11}, {0,3,8,10}, {0,4,5,12}, {0,4,6,11}, {0,4,7,10}, {0,4,8,9}, {0,5,6,10}, {0,5,7,9}, {0,6,7,8}, {1,2,3,15}, {1,2,4,14}, {1,2,5,13}, {1,2,6,12}, {1,2,7,11}, {1,2,8,10}, {1,3,4,13}, {1,3,5,12}, {1,3,6,11}, {1,3,7,10}, {1,3,8,9}, {1,4,5,11}, {1,4,6,10}, {1,4,7,9}, {1,5,6,9}, {1,5,7,8}, {2,3,4,12}, {2,3,5,11}, {2,3,6,10}, {2,3,7,9}, {2,4,5,10}, {2,4,6,9}, {2,4,7,8}, {2,5,6,8}, {3,4,5,9}, {3,4,6,8}, {3,5,6,7}} := by
  decide +kernel

theorem fourYNumber_20_1_1 :
    (collectedFourTrace 20 1 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (-5425434932455263271311794102417343/2097152000000000000000) := by
  decide +kernel

theorem fourYNumber_20_3_1 :
    (collectedFourTrace 20 3 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (179418905051802025654157882778009/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_20_3_3 :
    (collectedFourTrace 20 3 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (-834115719323087675418764349012483/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_20_5_1 :
    (collectedFourTrace 20 5 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (-11723708051921673633253439432421/419430400000000000000) := by
  decide +kernel

theorem fourYNumber_20_5_3 :
    (collectedFourTrace 20 5 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (12881735552398269417898166992863/4194304000000000000000) := by
  decide +kernel

theorem fourYNumber_20_5_5 :
    (collectedFourTrace 20 5 5 collectedFourData_20 : ℚ) / fourCommonDenominator = (-118469950634932051982395097529/209715200000000000000) := by
  decide +kernel

theorem fourYNumber_20_7_1 :
    (collectedFourTrace 20 7 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (13864922655913073136265005303171/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_20_7_3 :
    (collectedFourTrace 20 7 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (-20662582833925800835803040061757/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_20_7_5 :
    (collectedFourTrace 20 7 5 collectedFourData_20 : ℚ) / fourCommonDenominator = (469185654095355642726736632177/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_20_7_7 :
    (collectedFourTrace 20 7 7 collectedFourData_20 : ℚ) / fourCommonDenominator = (-1108741085510629637805875018883/26843545600000000000000) := by
  decide +kernel

theorem fourYNumber_20_9_1 :
    (collectedFourTrace 20 9 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (-13277763324745580223308038293/167772160000000000000) := by
  decide +kernel

theorem fourYNumber_20_9_3 :
    (collectedFourTrace 20 9 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (923018611270173374732366614023/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_20_9_5 :
    (collectedFourTrace 20 9 5 collectedFourData_20 : ℚ) / fourCommonDenominator = (-31129257954026396319571959543/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_20_9_7 :
    (collectedFourTrace 20 9 7 collectedFourData_20 : ℚ) / fourCommonDenominator = (90944316095019535880541746937/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_20_9_9 :
    (collectedFourTrace 20 9 9 collectedFourData_20 : ℚ) / fourCommonDenominator = (-9010857355442849356413184683/1677721600000000000000) := by
  decide +kernel

theorem fourYNumber_20_11_1 :
    (collectedFourTrace 20 11 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (-5957610413352344509215553231131/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_20_11_3 :
    (collectedFourTrace 20 11 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (503718895711039797688496710113/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_20_11_5 :
    (collectedFourTrace 20 11 5 collectedFourData_20 : ℚ) / fourCommonDenominator = (931665634290193477885889679/335544320000000000000) := by
  decide +kernel

theorem fourYNumber_20_11_7 :
    (collectedFourTrace 20 11 7 collectedFourData_20 : ℚ) / fourCommonDenominator = (-40083328549786255395843422241/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_20_11_9 :
    (collectedFourTrace 20 11 9 collectedFourData_20 : ℚ) / fourCommonDenominator = (6156096576995889112242847347/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_20_11_11 :
    (collectedFourTrace 20 11 11 collectedFourData_20 : ℚ) / fourCommonDenominator = (-36159738791356336455643126167/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_1 :
    (collectedFourTrace 20 13 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (683874918374867258301621850491/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_3 :
    (collectedFourTrace 20 13 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (-3562452616542808964288980155489/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_5 :
    (collectedFourTrace 20 13 5 collectedFourData_20 : ℚ) / fourCommonDenominator = (59811152248639925369457400179/4194304000000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_7 :
    (collectedFourTrace 20 13 7 collectedFourData_20 : ℚ) / fourCommonDenominator = (-96834753595294023711234063231/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_9 :
    (collectedFourTrace 20 13 9 collectedFourData_20 : ℚ) / fourCommonDenominator = (2488970661229237488568173909/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_11 :
    (collectedFourTrace 20 13 11 collectedFourData_20 : ℚ) / fourCommonDenominator = (9179254744275982446329067819/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_20_13_13 :
    (collectedFourTrace 20 13 13 collectedFourData_20 : ℚ) / fourCommonDenominator = (-41690584097328109332167065287/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_1 :
    (collectedFourTrace 20 15 1 collectedFourData_20 : ℚ) / fourCommonDenominator = (-2091544795318033449783795052647/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_3 :
    (collectedFourTrace 20 15 3 collectedFourData_20 : ℚ) / fourCommonDenominator = (3405146765776144196267117498841/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_5 :
    (collectedFourTrace 20 15 5 collectedFourData_20 : ℚ) / fourCommonDenominator = (-78411052632888756633548076381/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_7 :
    (collectedFourTrace 20 15 7 collectedFourData_20 : ℚ) / fourCommonDenominator = (177472155556961120068579204839/26843545600000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_9 :
    (collectedFourTrace 20 15 9 collectedFourData_20 : ℚ) / fourCommonDenominator = (-12165091907974821838928406501/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_11 :
    (collectedFourTrace 20 15 11 collectedFourData_20 : ℚ) / fourCommonDenominator = (-194619785792343914883807927/2684354560000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_13 :
    (collectedFourTrace 20 15 13 collectedFourData_20 : ℚ) / fourCommonDenominator = (39976011044472042963992972403/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_20_15_15 :
    (collectedFourTrace 20 15 15 collectedFourData_20 : ℚ) / fourCommonDenominator = (-50456789410054114597827183867/26843545600000000000000) := by
  decide +kernel

theorem fourYNumber_20_17_1 :
    (collectedFourTrace 20 17 1 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_3 :
    (collectedFourTrace 20 17 3 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_5 :
    (collectedFourTrace 20 17 5 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_7 :
    (collectedFourTrace 20 17 7 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_9 :
    (collectedFourTrace 20 17 9 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_11 :
    (collectedFourTrace 20 17 11 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_13 :
    (collectedFourTrace 20 17 13 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_15 :
    (collectedFourTrace 20 17 15 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_17_17 :
    (collectedFourTrace 20 17 17 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_1 :
    (collectedFourTrace 20 19 1 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_3 :
    (collectedFourTrace 20 19 3 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_5 :
    (collectedFourTrace 20 19 5 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_7 :
    (collectedFourTrace 20 19 7 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_9 :
    (collectedFourTrace 20 19 9 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_11 :
    (collectedFourTrace 20 19 11 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_13 :
    (collectedFourTrace 20 19 13 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_15 :
    (collectedFourTrace 20 19 15 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_17 :
    (collectedFourTrace 20 19 17 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_20_19_19 :
    (collectedFourTrace 20 19 19 collectedFourData_20 : ℚ) / fourCommonDenominator = 0 := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_20 (r s : CopyLabel 20) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 20 r s = fourYData_20 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_20 collectedFourChecked_20]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_20_1_1
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
  · exact fourYNumber_20_3_1
  · exact fourYNumber_20_3_3
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
  · exact fourYNumber_20_5_1
  · exact fourYNumber_20_5_3
  · exact fourYNumber_20_5_5
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
  · exact fourYNumber_20_7_1
  · exact fourYNumber_20_7_3
  · exact fourYNumber_20_7_5
  · exact fourYNumber_20_7_7
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
  · exact fourYNumber_20_9_1
  · exact fourYNumber_20_9_3
  · exact fourYNumber_20_9_5
  · exact fourYNumber_20_9_7
  · exact fourYNumber_20_9_9
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
  · exact fourYNumber_20_11_1
  · exact fourYNumber_20_11_3
  · exact fourYNumber_20_11_5
  · exact fourYNumber_20_11_7
  · exact fourYNumber_20_11_9
  · exact fourYNumber_20_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · have h : (19:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_20_13_1
  · exact fourYNumber_20_13_3
  · exact fourYNumber_20_13_5
  · exact fourYNumber_20_13_7
  · exact fourYNumber_20_13_9
  · exact fourYNumber_20_13_11
  · exact fourYNumber_20_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_20_15_1
  · exact fourYNumber_20_15_3
  · exact fourYNumber_20_15_5
  · exact fourYNumber_20_15_7
  · exact fourYNumber_20_15_9
  · exact fourYNumber_20_15_11
  · exact fourYNumber_20_15_13
  · exact fourYNumber_20_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_20_17_1
  · exact fourYNumber_20_17_3
  · exact fourYNumber_20_17_5
  · exact fourYNumber_20_17_7
  · exact fourYNumber_20_17_9
  · exact fourYNumber_20_17_11
  · exact fourYNumber_20_17_13
  · exact fourYNumber_20_17_15
  · exact fourYNumber_20_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_20_19_1
  · exact fourYNumber_20_19_3
  · exact fourYNumber_20_19_5
  · exact fourYNumber_20_19_7
  · exact fourYNumber_20_19_9
  · exact fourYNumber_20_19_11
  · exact fourYNumber_20_19_13
  · exact fourYNumber_20_19_15
  · exact fourYNumber_20_19_17
  · exact fourYNumber_20_19_19

theorem fourYChecked_20 (r s : CopyLabel 20) :
    integerRowsFourTrace 20 r s = fourYData_20 r s := by
  have hh : ∀ r s : CopyLabel 20, fourYData_20 r s = fourYData_20 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_20 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_20 s r (by omega), hh]

theorem fourHighestChecked_20 : ∀ r : CopyLabel 20, ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 r A = highestLookup fourHighestCache_20 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_20_1
  · exact fourHighestNumber_20_3
  · exact fourHighestNumber_20_5
  · exact fourHighestNumber_20_7
  · exact fourHighestNumber_20_9
  · exact fourHighestNumber_20_11
  · exact fourHighestNumber_20_13
  · exact fourHighestNumber_20_15
  · exact fourHighestNumber_20_17
  · exact fourHighestNumber_20_19

theorem fourZChecked_20 (r s : CopyLabel 20) :
    integerFourGram 20 r s = fourZData_20 r s := by
  rw [integerFourGram_cached 20 fourHighestCache_20 fourHighestChecked_20]
  have h : ∀ r s : CopyLabel 20, cachedFourGram 20 fourHighestCache_20 r s = fourZData_20 r s := by
    simp only [cachedFourGram, fourOccupations_20]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_20 :
    fourZData_20 * (Matrix.diagonal (fun r : CopyLabel 20 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 20 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val) *
        fourYData_20 * Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val)) *
      fourZData_20 = fourLData_20 * Matrix.diagonal fourPivotData_20 * (fourLData_20)ᵀ := by
  have h : ∀ r s : CopyLabel 20,
      (fourZData_20 * (Matrix.diagonal (fun r : CopyLabel 20 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 20 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val) *
          fourYData_20 * Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val)) *
        fourZData_20 : Matrix (CopyLabel 20) (CopyLabel 20) ℚ) r s =
      (fourLData_20 * Matrix.diagonal fourPivotData_20 * (fourLData_20)ᵀ : Matrix (CopyLabel 20) (CopyLabel 20) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_20 : ∀ r, 0 ≤ fourPivotData_20 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_20, copyDiagonalData]

theorem integer_certificate_20_oai :
    ((integerCompression 20).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_20) (fourPivotData_20) _ fourPivotChecked_20
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 20 = fourYData_20 from Matrix.ext fourYChecked_20,
    show integerFourGram 20 = fourZData_20 from Matrix.ext fourZChecked_20]
  exact fourLDLChecked_20

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_20_oai := @OAI.LaughlinFock.integer_certificate_20_oai
