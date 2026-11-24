-- Prove2me | solution 1 for MeasureTheory.measurableSet_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:32:49.613837+00:00
-- url     : https://prove2.me/submissions/b3c8bd66-5eb5-4e29-8071-d566541d7a51

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
public import Theorems.Thm_MeasureTheory_measurePreserving_flipSet

set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    MeasurableSet (saturation E) :=
  .iUnion fun s ↦ (measurePreserving_flipSet s).measurable hE
end MeasureTheory
