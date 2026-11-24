-- Prove2me | solution 1 for GlobalTheory.LipschitzCovol.toMixed_remb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:00:42.212359+00:00
-- url     : https://prove2.me/submissions/a42a27e4-4ed5-4858-a6ca-b754f337952e

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Theorems.Thm_GlobalTheory_LipschitzCovol_embPlace_symm_apply
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
open GlobalTheory GlobalTheory.LipschitzCovol
open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.LipschitzCovol
theorem _root_.solution (a : F) : toMixed (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
  simp [toMixed, embPlace_symm_apply]
end GlobalTheory.LipschitzCovol
