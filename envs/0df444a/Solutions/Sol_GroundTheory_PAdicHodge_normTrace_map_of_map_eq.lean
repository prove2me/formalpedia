-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_map_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:06.169686+00:00
-- url     : https://prove2.me/submissions/a0c64447-ba55-46ee-9e1d-a9137f6985fe

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_ringEquiv

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
variable {Ω : Type*} [Field Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {B₀ : Type*} [Field B₀] [Algebra B₀ Ω] [Algebra.IsIntegral B₀ Ω]
    (k : IntermediateField B₀ Ω) (σ : Ω ≃ₐ[B₀] Ω) (hk : k.map (σ : Ω →ₐ[B₀] Ω) = k) (y : Ω) :
    normTrace k (σ y) = σ (normTrace k y) := by
  have hy : IsIntegral k y := (Algebra.IsIntegral.isIntegral (R := B₀) y).tower_top
  let τ : k ≃+* k := ((k.equivMap (σ : Ω →ₐ[B₀] Ω)).trans (IntermediateField.equivOfEq hk)).toRingEquiv
  exact normTrace_map_ringEquiv τ σ.toRingEquiv (fun a => rfl) hy
end GroundTheory.PAdicHodge
