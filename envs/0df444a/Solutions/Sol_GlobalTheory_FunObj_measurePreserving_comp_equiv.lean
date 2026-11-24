-- Prove2me | solution 1 for GlobalTheory.FunObj.measurePreserving_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:55.083918+00:00
-- url     : https://prove2.me/submissions/9f170ea5-92c3-48b8-bc34-09f52d60db92

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
  {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure]
omit [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [ν.IsAddHaarMeasure]
namespace GlobalTheory.FunObj
theorem _root_.solution {A B : Type} [Fintype A] [Fintype B] [SigmaFinite ν] (e : A ≃ B) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : B => k) e).symm (Measure.pi fun _ => ν)
      (Measure.pi fun _ => ν) := (measurePreserving_piCongrLeft (fun _ : B => ν) e).symm
end GlobalTheory.FunObj
