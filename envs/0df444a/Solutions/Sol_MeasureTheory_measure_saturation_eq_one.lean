-- Prove2me | solution 1 for MeasureTheory.measure_saturation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:43:14.022554+00:00
-- url     : https://prove2.me/submissions/cc172a0c-fc21-4976-8c84-7cd78b1e6637

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
public import Theorems.Thm_MeasureTheory_measure_eq_zero_or_one_of_flipSet_invariant
public import Theorems.Thm_MeasureTheory_subset_saturation
public import Theorems.Thm_MeasureTheory_measurableSet_saturation
public import Theorems.Thm_MeasureTheory_flipSet_preimage_saturation

set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {E : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hpos : cantorMeasure E ≠ 0) : cantorMeasure (saturation E) = 1 :=
  (measure_eq_zero_or_one_of_flipSet_invariant (measurableSet_saturation hE)
    (flipSet_preimage_saturation E)).resolve_left
      fun h0 ↦ hpos (measure_mono_null (subset_saturation E) h0)
end MeasureTheory
