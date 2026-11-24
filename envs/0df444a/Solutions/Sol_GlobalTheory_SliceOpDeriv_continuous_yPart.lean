-- Prove2me | solution 1 for GlobalTheory.SliceOpDeriv.continuous_yPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:17.208026+00:00
-- url     : https://prove2.me/submissions/ffa36216-bf81-42aa-b32c-b54e3c205d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
import Theorems.Thm_GlobalTheory_SliceOpDeriv_continuous_elim_pair
import Theorems.Thm_GlobalTheory_SliceOpDeriv_qOp_elim
import Theorems.Thm_GlobalTheory_SliceOp_continuous_qOp
import Theorems.Thm_GlobalTheory_SliceOp_pd_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
namespace GlobalTheory.SliceOpDeriv
theorem _root_.solution (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2) := by
  refine continuous_clm_apply.2 fun w => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2 w) =
      fun p => qOp ((pd w).comp P) f (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, ContinuousLinearMap.comp_apply, pd_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' _ _).comp continuous_elim_pair
end GlobalTheory.SliceOpDeriv
