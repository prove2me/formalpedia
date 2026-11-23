-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:31.930109+00:00
-- url     : https://prove2.me/submissions/8c55e09c-b3e0-45ce-a316-77e6b425cf89

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand

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
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR.LhsSum
theorem _root_.solution (m : ℤ) : 0 ≤ wt m := by unfold wt; positivity
end GlobalTheory.LipschitzTR.LhsSum
