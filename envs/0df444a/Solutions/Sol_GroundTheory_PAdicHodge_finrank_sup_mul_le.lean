-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_sup_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:51.879925+00:00
-- url     : https://prove2.me/submissions/200c6e67-af00-42cc-b219-b9ef31b966a6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_eq_mul_finrank_extendScalars

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
theorem _root_.solution {k X Y : IntermediateField B₀ Ω} (hX : k ≤ X) (hY : k ≤ Y) :
    finrank B₀ ↥(X ⊔ Y) * finrank B₀ k ≤ finrank B₀ X * finrank B₀ Y := by
  rw [finrank_eq_mul_finrank_extendScalars hX, finrank_eq_mul_finrank_extendScalars hY,
    finrank_eq_mul_finrank_extendScalars (le_sup_of_le_left hX : k ≤ X ⊔ Y),
    ← extendScalars_sup hX hY]
  have := IntermediateField.finrank_sup_le (extendScalars hX) (extendScalars hY)
  calc finrank B₀ k * finrank k ↥(extendScalars hX ⊔ extendScalars hY) * finrank B₀ k
      = finrank B₀ k * finrank B₀ k * finrank k ↥(extendScalars hX ⊔ extendScalars hY) := by ring
    _ ≤ finrank B₀ k * finrank B₀ k *
        (finrank k (extendScalars hX) * finrank k (extendScalars hY)) := Nat.mul_le_mul_left _ this
    _ = _ := by ring
end GroundTheory.PAdicHodge
