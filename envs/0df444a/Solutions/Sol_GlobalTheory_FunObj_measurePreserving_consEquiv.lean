-- Prove2me | solution 1 for GlobalTheory.FunObj.measurePreserving_consEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:11.184425+00:00
-- url     : https://prove2.me/submissions/ae1722d8-42eb-41ea-8f4f-d3fcde444339

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
namespace GlobalTheory.FunObj
theorem _root_.solution {n : ℕ} {E : Fin (n + 1) → Type} [∀ j, MeasurableSpace (E j)]
    (μ : ∀ j, Measure (E j)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (consEquiv E) ((μ 0).prod (Measure.pi fun j => μ j.succ)) (Measure.pi μ) :=
  (measurePreserving_piFinSuccAbove μ 0).symm
end GlobalTheory.FunObj
