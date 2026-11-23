-- Prove2me | solution 1 for GlobalTheory.RealWeil.schwartzToL2_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:42.984713+00:00
-- url     : https://prove2.me/submissions/341fbd66-20a3-4eb5-aa90-fe319ba626fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
omit [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (f : Sch l) : schwartzToL2 l f = f.toLp 2 volume := rfl
end GlobalTheory.RealWeil
