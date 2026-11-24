-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.inner_remb_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:20.049589+00:00
-- url     : https://prove2.me/submissions/bbb08afa-a083-44ad-9d88-a0b1b59e88e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
import Theorems.Thm_GlobalTheory_trace_eq_sum_realEmbeddings
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
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (a b : F) :
    ⟪remb F a, remb F b⟫ = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by
  rw [GlobalTheory.trace_eq_sum_realEmbeddings, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [map_mul, mul_comm]
end GlobalTheory.LipschitzTR
