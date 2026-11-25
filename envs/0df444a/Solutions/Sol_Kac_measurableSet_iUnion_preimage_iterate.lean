-- Prove2me | solution 1 for Kac.measurableSet_iUnion_preimage_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:07:47.999472+00:00
-- url     : https://prove2.me/submissions/f8586a05-8dd0-453e-945f-d2384627656a

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
    MeasurableSet (⋃ k : ℕ, f^[k] ⁻¹' A) :=
  MeasurableSet.iUnion fun k => hf.iterate k hA
end Kac
