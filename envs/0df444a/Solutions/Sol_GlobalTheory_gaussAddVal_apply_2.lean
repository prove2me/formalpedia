-- Prove2me | solution 2 for GlobalTheory.gaussAddVal_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:59.656996+00:00
-- url     : https://prove2.me/submissions/f54814e5-8c5f-41c2-afed-43b77480a6a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_gaussAddVal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial σ R) :
    gaussAddVal v f = f.support.inf fun m => v (coeff m f) := by
  refine eq_of_forall_le_iff fun γ => ?_
  rw [le_gaussAddVal_iff, Finset.le_inf_iff]
  refine ⟨fun h m _ => h m, fun h m => ?_⟩
  by_cases hm : m ∈ f.support
  · exact h m hm
  · rw [notMem_support_iff.mp hm, v.map_zero]; exact le_top
end GlobalTheory
