-- Prove2me | solution 1 for GlobalTheory.T.covolume_fractionalIdealRealLatticeImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:36.475559+00:00
-- url     : https://prove2.me/submissions/3b0d0e38-6aa6-4174-ae9d-a8b5bc6c448d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImageStatement
import Theorems.Thm_GlobalTheory_LipschitzCovol_covolume_latOf


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)], ZLattice.covolume (latOf N) = covol N := by
  first | exact @GlobalTheory.LipschitzCovol.covolume_latOf | exact GlobalTheory.LipschitzCovol.covolume_latOf | (intros; apply GlobalTheory.LipschitzCovol.covolume_latOf <;> assumption)
end _root_.GlobalTheory.T
