-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.measurable_rem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:49.427335+00:00
-- url     : https://prove2.me/submissions/2de8e7c2-d720-42fb-b438-fea0ea3cf7cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution :
    Measurable fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x :=
  ((measurable_from_top (f := fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, 𝓕.aChi χ n)).comp
    Nat.measurable_floor).sub (measurable_ofReal.const_mul _)
end GlobalTheory.Hk.RayCont
