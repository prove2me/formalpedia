-- Prove2me | solution 1 for GlobalTheory.TopForm.dForm_eq_det_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:15.281691+00:00
-- url     : https://prove2.me/submissions/995d5626-814e-44f7-8832-e0325eeb42af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_TopForm_dForm_eq
import Theorems.Thm_GlobalTheory_alternating_map_sum_smul_eq_det_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
namespace GlobalTheory.TopForm
theorem _root_.solution (f x : Fin D → A) (a : Matrix (Fin D) (Fin D) A)
    (h : ∀ i, dFun α (f i) = ∑ j, a i j • dFun α (x j)) : dForm α f = a.det • dForm α x := by
  rw [dForm_eq, dForm_eq, ← alternating_map_sum_smul_eq_det_smul]
  exact congrArg _ (funext h)
end GlobalTheory.TopForm
