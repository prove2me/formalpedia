-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.dual_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:00.199871+00:00
-- url     : https://prove2.me/submissions/faf14a79-ce5b-4366-9c53-1cba34ccf353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzFormulaTotallyRealPoisson
import Theorems.Thm_GlobalTheory_T_dual_latticeImage_eq_latticeImage_traceDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR
theorem _root_.solution [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual F N hN
end GlobalTheory.LipschitzTR
