-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:27.687802+00:00
-- url     : https://prove2.me/submissions/816d40f7-ca6a-4822-896d-e86735907b73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K] [NormedCommRing L]
namespace GlobalTheory.MvPoly
theorem _root_.solution [NormOneClass K] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1Norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1Norm_nonneg _))
end GlobalTheory.MvPoly
