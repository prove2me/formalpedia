-- Prove2me | solution 1 for Kac.measurableSet_notYet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:04:40.822875+00:00
-- url     : https://prove2.me/submissions/f064bce8-ea0a-4889-aa62-9f0d99123ca4

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (hf : Measurable f) (hA : MeasurableSet A) :
    ∀ n, MeasurableSet (notYet f A n)
  | 0 => MeasurableSet.univ
  | n + 1 => hA.compl.inter (hf (solution hf hA n))
end Kac
