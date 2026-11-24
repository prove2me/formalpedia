-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.norm_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:46:07.430142+00:00
-- url     : https://prove2.me/submissions/d04df80b-8df0-41ab-a73b-8b93260ec2ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : RSp F) :
    ‖v‖ ≤ ∑ τ, |v τ| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun τ => |v τ|) fun _ _ => abs_nonneg _
end GlobalTheory.LipschitzTR
