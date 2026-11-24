-- Prove2me | solution 1 for GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:30.823133+00:00
-- url     : https://prove2.me/submissions/b4aa6420-7c88-49c8-b8e7-5553da49e174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDualStatement
import Theorems.Thm_GlobalTheory_LipschitzTR_dual_latOf_eq_latOf_traceDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  first | exact @GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | exact GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | (intros; apply GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual <;> assumption)
end _root_.GlobalTheory.T
