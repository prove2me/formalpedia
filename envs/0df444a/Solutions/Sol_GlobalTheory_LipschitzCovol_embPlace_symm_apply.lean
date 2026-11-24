-- Prove2me | solution 1 for GlobalTheory.LipschitzCovol.embPlace_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:05.749808+00:00
-- url     : https://prove2.me/submissions/caaba62a-1aa3-499f-9b9f-4fae783042d4

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage

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
open GlobalTheory GlobalTheory.LipschitzCovol
open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.LipschitzCovol
theorem _root_.solution (w : {w : InfinitePlace F // IsReal w}) :
    (embPlace.symm w : F →+* ℝ) = embedding_of_isReal w.2 := rfl
end GlobalTheory.LipschitzCovol
