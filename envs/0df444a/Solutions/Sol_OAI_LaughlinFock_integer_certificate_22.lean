-- Prove2me | solution 1 for OAI.LaughlinFock.integer_certificate_22
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:32:15.689829+00:00
-- url     : https://prove2.me/submissions/7d433699-9073-41a2-9fba-beac802b48d0

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L040
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_1
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_11
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_13
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_15
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_17
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_19
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_21
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_3
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_5
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_7
import Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_22_9
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse22. -/
namespace LaughlinFock

theorem collectedFourChecked_22 : collectedFourTerms 22 = collectedFourData_22 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_22 : highestFourOccupations 22 = {{0,1,2,20}, {0,1,3,19}, {0,1,4,18}, {0,1,5,17}, {0,1,6,16}, {0,1,7,15}, {0,1,8,14}, {0,1,9,13}, {0,1,10,12}, {0,2,3,18}, {0,2,4,17}, {0,2,5,16}, {0,2,6,15}, {0,2,7,14}, {0,2,8,13}, {0,2,9,12}, {0,2,10,11}, {0,3,4,16}, {0,3,5,15}, {0,3,6,14}, {0,3,7,13}, {0,3,8,12}, {0,3,9,11}, {0,4,5,14}, {0,4,6,13}, {0,4,7,12}, {0,4,8,11}, {0,4,9,10}, {0,5,6,12}, {0,5,7,11}, {0,5,8,10}, {0,6,7,10}, {0,6,8,9}, {1,2,3,17}, {1,2,4,16}, {1,2,5,15}, {1,2,6,14}, {1,2,7,13}, {1,2,8,12}, {1,2,9,11}, {1,3,4,15}, {1,3,5,14}, {1,3,6,13}, {1,3,7,12}, {1,3,8,11}, {1,3,9,10}, {1,4,5,13}, {1,4,6,12}, {1,4,7,11}, {1,4,8,10}, {1,5,6,11}, {1,5,7,10}, {1,5,8,9}, {1,6,7,9}, {2,3,4,14}, {2,3,5,13}, {2,3,6,12}, {2,3,7,11}, {2,3,8,10}, {2,4,5,12}, {2,4,6,11}, {2,4,7,10}, {2,4,8,9}, {2,5,6,10}, {2,5,7,9}, {2,6,7,8}, {3,4,5,11}, {3,4,6,10}, {3,4,7,9}, {3,5,6,9}, {3,5,7,8}, {4,5,6,8}} := by
  decide +kernel

theorem fourYNumber_22_1_1 :
    (collectedFourTrace 22 1 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (-215945136211697789352769368338283/1310720000000000000) := by
  decide +kernel

theorem fourYNumber_22_3_1 :
    (collectedFourTrace 22 3 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (215945136211697789352769368338283/13107200000000000000) := by
  decide +kernel

theorem fourYNumber_22_3_3 :
    (collectedFourTrace 22 3 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (-215945136211697789352769368338283/131072000000000000000) := by
  decide +kernel

theorem fourYNumber_22_5_1 :
    (collectedFourTrace 22 5 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (-3788511161608733146539813479619/1310720000000000000) := by
  decide +kernel

theorem fourYNumber_22_5_3 :
    (collectedFourTrace 22 5 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (3788511161608733146539813479619/13107200000000000000) := by
  decide +kernel

theorem fourYNumber_22_5_5 :
    (collectedFourTrace 22 5 5 collectedFourData_22 : ℚ) / fourCommonDenominator = (-66465108098398827132277429467/1310720000000000000) := by
  decide +kernel

theorem fourYNumber_22_7_1 :
    (collectedFourTrace 22 7 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (1559975184191831295634040844549/2097152000000000000) := by
  decide +kernel

theorem fourYNumber_22_7_3 :
    (collectedFourTrace 22 7 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (-1559975184191831295634040844549/20971520000000000000) := by
  decide +kernel

theorem fourYNumber_22_7_5 :
    (collectedFourTrace 22 7 5 collectedFourData_22 : ℚ) / fourCommonDenominator = (27367985687575987642702470957/2097152000000000000) := by
  decide +kernel

theorem fourYNumber_22_7_7 :
    (collectedFourTrace 22 7 7 collectedFourData_22 : ℚ) / fourCommonDenominator = (-11269170577237171382289252747/3355443200000000000) := by
  decide +kernel

theorem fourYNumber_22_9_1 :
    (collectedFourTrace 22 9 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (-668560793225070555271731790521/2621440000000000000) := by
  decide +kernel

theorem fourYNumber_22_9_3 :
    (collectedFourTrace 22 9 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (668560793225070555271731790521/26214400000000000000) := by
  decide +kernel

theorem fourYNumber_22_9_5 :
    (collectedFourTrace 22 9 5 collectedFourData_22 : ℚ) / fourCommonDenominator = (-11729136723246851846872487553/2621440000000000000) := by
  decide +kernel

theorem fourYNumber_22_9_7 :
    (collectedFourTrace 22 9 7 collectedFourData_22 : ℚ) / fourCommonDenominator = (4829644533101644878123965463/4194304000000000000) := by
  decide +kernel

theorem fourYNumber_22_9_9 :
    (collectedFourTrace 22 9 9 collectedFourData_22 : ℚ) / fourCommonDenominator = (-2069847657043562090624556627/5242880000000000000) := by
  decide +kernel

theorem fourYNumber_22_11_1 :
    (collectedFourTrace 22 11 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (565705286575059700614542284287/5242880000000000000) := by
  decide +kernel

theorem fourYNumber_22_11_3 :
    (collectedFourTrace 22 11 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (-565705286575059700614542284287/52428800000000000000) := by
  decide +kernel

theorem fourYNumber_22_11_5 :
    (collectedFourTrace 22 11 5 collectedFourData_22 : ℚ) / fourCommonDenominator = (9924654150439643870430566391/5242880000000000000) := by
  decide +kernel

theorem fourYNumber_22_11_7 :
    (collectedFourTrace 22 11 7 collectedFourData_22 : ℚ) / fourCommonDenominator = (-4086622297239853358412586161/8388608000000000000) := by
  decide +kernel

theorem fourYNumber_22_11_9 :
    (collectedFourTrace 22 11 9 collectedFourData_22 : ℚ) / fourCommonDenominator = (1751409555959937153605394069/10485760000000000000) := by
  decide +kernel

theorem fourYNumber_22_11_11 :
    (collectedFourTrace 22 11 11 collectedFourData_22 : ℚ) / fourCommonDenominator = (-1481961931966100668435333443/20971520000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_1 :
    (collectedFourTrace 22 13 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (-668560793225070555271731790521/13107200000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_3 :
    (collectedFourTrace 22 13 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (668560793225070555271731790521/131072000000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_5 :
    (collectedFourTrace 22 13 5 collectedFourData_22 : ℚ) / fourCommonDenominator = (-11729136723246851846872487553/13107200000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_7 :
    (collectedFourTrace 22 13 7 collectedFourData_22 : ℚ) / fourCommonDenominator = (4829644533101644878123965463/20971520000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_9 :
    (collectedFourTrace 22 13 9 collectedFourData_22 : ℚ) / fourCommonDenominator = (-2069847657043562090624556627/26214400000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_11 :
    (collectedFourTrace 22 13 11 collectedFourData_22 : ℚ) / fourCommonDenominator = (1751409555959937153605394069/52428800000000000000) := by
  decide +kernel

theorem fourYNumber_22_13_13 :
    (collectedFourTrace 22 13 13 collectedFourData_22 : ℚ) / fourCommonDenominator = (-2069847657043562090624556627/131072000000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_1 :
    (collectedFourTrace 22 15 1 collectedFourData_22 : ℚ) / fourCommonDenominator = (222853597741690185090577263507/10485760000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_3 :
    (collectedFourTrace 22 15 3 collectedFourData_22 : ℚ) / fourCommonDenominator = (-222853597741690185090577263507/104857600000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_5 :
    (collectedFourTrace 22 15 5 collectedFourData_22 : ℚ) / fourCommonDenominator = (3909712241082283948957495851/10485760000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_7 :
    (collectedFourTrace 22 15 7 collectedFourData_22 : ℚ) / fourCommonDenominator = (-1609881511033881626041321821/16777216000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_9 :
    (collectedFourTrace 22 15 9 collectedFourData_22 : ℚ) / fourCommonDenominator = (689949219014520696874852209/20971520000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_11 :
    (collectedFourTrace 22 15 11 collectedFourData_22 : ℚ) / fourCommonDenominator = (-583803185319979051201798023/41943040000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_13 :
    (collectedFourTrace 22 15 13 collectedFourData_22 : ℚ) / fourCommonDenominator = (689949219014520696874852209/104857600000000000000) := by
  decide +kernel

theorem fourYNumber_22_15_15 :
    (collectedFourTrace 22 15 15 collectedFourData_22 : ℚ) / fourCommonDenominator = (-229983073004840232291617403/83886080000000000000) := by
  decide +kernel

theorem fourYNumber_22_17_1 :
    (collectedFourTrace 22 17 1 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_3 :
    (collectedFourTrace 22 17 3 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_5 :
    (collectedFourTrace 22 17 5 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_7 :
    (collectedFourTrace 22 17 7 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_9 :
    (collectedFourTrace 22 17 9 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_11 :
    (collectedFourTrace 22 17 11 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_13 :
    (collectedFourTrace 22 17 13 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_15 :
    (collectedFourTrace 22 17 15 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_17_17 :
    (collectedFourTrace 22 17 17 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_1 :
    (collectedFourTrace 22 19 1 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_3 :
    (collectedFourTrace 22 19 3 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_5 :
    (collectedFourTrace 22 19 5 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_7 :
    (collectedFourTrace 22 19 7 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_9 :
    (collectedFourTrace 22 19 9 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_11 :
    (collectedFourTrace 22 19 11 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_13 :
    (collectedFourTrace 22 19 13 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_15 :
    (collectedFourTrace 22 19 15 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_17 :
    (collectedFourTrace 22 19 17 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_19_19 :
    (collectedFourTrace 22 19 19 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_1 :
    (collectedFourTrace 22 21 1 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_3 :
    (collectedFourTrace 22 21 3 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_5 :
    (collectedFourTrace 22 21 5 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_7 :
    (collectedFourTrace 22 21 7 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_9 :
    (collectedFourTrace 22 21 9 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_11 :
    (collectedFourTrace 22 21 11 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_13 :
    (collectedFourTrace 22 21 13 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_15 :
    (collectedFourTrace 22 21 15 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_17 :
    (collectedFourTrace 22 21 17 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_19 :
    (collectedFourTrace 22 21 19 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_22_21_21 :
    (collectedFourTrace 22 21 21 collectedFourData_22 : ℚ) / fourCommonDenominator = 0 := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_22 (r s : CopyLabel 22) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 22 r s = fourYData_22 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_22 collectedFourChecked_22]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_22_1_1
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
  · exact fourYNumber_22_3_1
  · exact fourYNumber_22_3_3
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
  · exact fourYNumber_22_5_1
  · exact fourYNumber_22_5_3
  · exact fourYNumber_22_5_5
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
  · exact fourYNumber_22_7_1
  · exact fourYNumber_22_7_3
  · exact fourYNumber_22_7_5
  · exact fourYNumber_22_7_7
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
  · exact fourYNumber_22_9_1
  · exact fourYNumber_22_9_3
  · exact fourYNumber_22_9_5
  · exact fourYNumber_22_9_7
  · exact fourYNumber_22_9_9
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
  · exact fourYNumber_22_11_1
  · exact fourYNumber_22_11_3
  · exact fourYNumber_22_11_5
  · exact fourYNumber_22_11_7
  · exact fourYNumber_22_11_9
  · exact fourYNumber_22_11_11
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
  · exact fourYNumber_22_13_1
  · exact fourYNumber_22_13_3
  · exact fourYNumber_22_13_5
  · exact fourYNumber_22_13_7
  · exact fourYNumber_22_13_9
  · exact fourYNumber_22_13_11
  · exact fourYNumber_22_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · have h : (21:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_22_15_1
  · exact fourYNumber_22_15_3
  · exact fourYNumber_22_15_5
  · exact fourYNumber_22_15_7
  · exact fourYNumber_22_15_9
  · exact fourYNumber_22_15_11
  · exact fourYNumber_22_15_13
  · exact fourYNumber_22_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · have h : (21:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_22_17_1
  · exact fourYNumber_22_17_3
  · exact fourYNumber_22_17_5
  · exact fourYNumber_22_17_7
  · exact fourYNumber_22_17_9
  · exact fourYNumber_22_17_11
  · exact fourYNumber_22_17_13
  · exact fourYNumber_22_17_15
  · exact fourYNumber_22_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · have h : (21:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_22_19_1
  · exact fourYNumber_22_19_3
  · exact fourYNumber_22_19_5
  · exact fourYNumber_22_19_7
  · exact fourYNumber_22_19_9
  · exact fourYNumber_22_19_11
  · exact fourYNumber_22_19_13
  · exact fourYNumber_22_19_15
  · exact fourYNumber_22_19_17
  · exact fourYNumber_22_19_19
  · have h : (21:ℕ) ≤ 19 := hrs
    omega
  · exact fourYNumber_22_21_1
  · exact fourYNumber_22_21_3
  · exact fourYNumber_22_21_5
  · exact fourYNumber_22_21_7
  · exact fourYNumber_22_21_9
  · exact fourYNumber_22_21_11
  · exact fourYNumber_22_21_13
  · exact fourYNumber_22_21_15
  · exact fourYNumber_22_21_17
  · exact fourYNumber_22_21_19
  · exact fourYNumber_22_21_21

theorem fourYChecked_22 (r s : CopyLabel 22) :
    integerRowsFourTrace 22 r s = fourYData_22 r s := by
  have hh : ∀ r s : CopyLabel 22, fourYData_22 r s = fourYData_22 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_22 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_22 s r (by omega), hh]

theorem fourHighestChecked_22 : ∀ r : CopyLabel 22, ∀ A∈highestFourOccupations 22,
    kernelHighestEntry 22 r A = highestLookup fourHighestCache_22 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_22_1
  · exact fourHighestNumber_22_3
  · exact fourHighestNumber_22_5
  · exact fourHighestNumber_22_7
  · exact fourHighestNumber_22_9
  · exact fourHighestNumber_22_11
  · exact fourHighestNumber_22_13
  · exact fourHighestNumber_22_15
  · exact fourHighestNumber_22_17
  · exact fourHighestNumber_22_19
  · exact fourHighestNumber_22_21

theorem fourZChecked_22 (r s : CopyLabel 22) :
    integerFourGram 22 r s = fourZData_22 r s := by
  rw [integerFourGram_cached 22 fourHighestCache_22 fourHighestChecked_22]
  have h : ∀ r s : CopyLabel 22, cachedFourGram 22 fourHighestCache_22 r s = fourZData_22 r s := by
    simp only [cachedFourGram, fourOccupations_22]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_22 :
    fourZData_22 * (Matrix.diagonal (fun r : CopyLabel 22 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 22 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 22 => rationalCopyDiagonal 22 r.val.val) *
        fourYData_22 * Matrix.diagonal (fun r : CopyLabel 22 => rationalCopyDiagonal 22 r.val.val)) *
      fourZData_22 = fourLData_22 * Matrix.diagonal fourPivotData_22 * (fourLData_22)ᵀ := by
  have h : ∀ r s : CopyLabel 22,
      (fourZData_22 * (Matrix.diagonal (fun r : CopyLabel 22 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 22 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 22 => rationalCopyDiagonal 22 r.val.val) *
          fourYData_22 * Matrix.diagonal (fun r : CopyLabel 22 => rationalCopyDiagonal 22 r.val.val)) *
        fourZData_22 : Matrix (CopyLabel 22) (CopyLabel 22) ℚ) r s =
      (fourLData_22 * Matrix.diagonal fourPivotData_22 * (fourLData_22)ᵀ : Matrix (CopyLabel 22) (CopyLabel 22) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_22 : ∀ r, 0 ≤ fourPivotData_22 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_22, copyDiagonalData]

theorem integer_certificate_22_oai :
    ((integerCompression 22).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_22) (fourPivotData_22) _ fourPivotChecked_22
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 22 = fourYData_22 from Matrix.ext fourYChecked_22,
    show integerFourGram 22 = fourZData_22 from Matrix.ext fourZChecked_22]
  exact fourLDLChecked_22

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.integer_certificate_22_oai := @OAI.LaughlinFock.integer_certificate_22_oai
