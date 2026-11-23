-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_sup_adjoin_simple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:34.978715+00:00
-- url     : https://prove2.me/submissions/c0e15276-1b7d-4389-9672-5e8202e931cd

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
theorem _root_.solution (F : IntermediateField B₀ Ω) {z : Ω} (hz : IsIntegral F z) :
    finrank B₀ ↥(F ⊔ adjoin B₀ {z}) = finrank B₀ F * (minpoly F z).natDegree := by
  rw [finrank_eq_mul_finrank_extendScalars (le_sup_left : F ≤ F ⊔ adjoin B₀ {z})]
  have : extendScalars (le_sup_left : F ≤ F ⊔ adjoin B₀ {z}) = adjoin F {z} :=
    restrictScalars_injective B₀ (by rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup])
  rw [this, IntermediateField.adjoin.finrank hz]
end GroundTheory.PAdicHodge
