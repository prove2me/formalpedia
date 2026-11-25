-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_normTrace_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:15.363881+00:00
-- url     : https://prove2.me/submissions/a40b5d21-6a5c-417c-a112-7472a0e69aa8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_normTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution [CharZero Ω] [Algebra.IsIntegral B₀ Ω]
    {k E : IntermediateField B₀ Ω} (h : k ≤ E) [FiniteDimensional B₀ E] (y : Ω) :
    normTrace k (normTrace E y) = normTrace k y := by
  haveI : CharZero k := (algebraMap k Ω).charZero
  haveI : Algebra.IsIntegral k Ω := Algebra.IsIntegral.tower_top B₀
  letI : Algebra k E := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B₀ k E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite B₀ k E
  exact normTrace_normTrace k E y
end GroundTheory.PAdicHodge
