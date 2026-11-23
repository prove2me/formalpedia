-- Prove2me | solution 1 for GlobalTheory.RegSS.CycAlg.toGen_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:39.934802+00:00
-- url     : https://prove2.me/submissions/d3b05e2f-9e20-4ba8-a365-098bce59d4f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS.CycAlg
theorem _root_.solution (M : Matrix n n A) (p : A[X]) :
    toGen M (AdjoinRoot.mk _ p) = aeval (gen M) p :=
  AdjoinRoot.liftAlgHom_mk _ _ _ _ p
end GlobalTheory.RegSS.CycAlg
