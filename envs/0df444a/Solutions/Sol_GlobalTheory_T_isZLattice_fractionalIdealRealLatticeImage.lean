-- Prove2me | solution 1 for GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:06.951329+00:00
-- url     : https://prove2.me/submissions/a7e91e94-dbce-45d2-84a0-1e811772b684

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImageStatement
import Theorems.Thm_GlobalTheory_LipschitzTR_isZLattice_latOf


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)], IsZLattice ℝ (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.isZLattice_latOf | exact GlobalTheory.LipschitzTR.isZLattice_latOf | (intros; apply GlobalTheory.LipschitzTR.isZLattice_latOf <;> assumption)
end _root_.GlobalTheory.T
