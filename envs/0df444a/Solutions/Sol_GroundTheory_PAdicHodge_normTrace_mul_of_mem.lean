-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:01.321145+00:00
-- url     : https://prove2.me/submissions/170ec537-9821-45e7-81cf-e26c1c9015a9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_algebraMap_mul

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
theorem _root_.solution [CharZero Ω] [Algebra.IsIntegral B₀ Ω] (k : IntermediateField B₀ Ω)
    {a : Ω} (ha : a ∈ k) (y : Ω) : normTrace k (a * y) = a * normTrace k y := by
  haveI : CharZero k := (algebraMap k Ω).charZero
  haveI : Algebra.IsIntegral k Ω := Algebra.IsIntegral.tower_top B₀
  exact normTrace_algebraMap_mul k ⟨a, ha⟩ y
end GroundTheory.PAdicHodge
