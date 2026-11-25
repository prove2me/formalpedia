-- Prove2me | solution 1 for GroundTheory.Global.mul_sup_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:37.311818+00:00
-- url     : https://prove2.me/submissions/618307bb-b586-4f81-9f10-8313d3da9058

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {R : Type*} [CommRing R] {I J B₁ B₂ : Ideal R} (hIJ : I ⊔ J = ⊤)
    (h₁ : I ≤ B₁) (h₂ : J ≤ B₂) : B₁ * B₂ ⊔ I = B₁ := by
  have hB₂ : B₂ ⊔ I = ⊤ := top_le_iff.1 (hIJ ▸ sup_le (le_sup_of_le_right le_rfl)
    (le_sup_of_le_left h₂))
  refine le_antisymm (sup_le Ideal.mul_le_left h₁) ?_
  calc B₁ = B₁ * (B₂ ⊔ I) := by rw [hB₂, Ideal.mul_top]
    _ = B₁ * B₂ ⊔ B₁ * I := Ideal.mul_sup _ _ _
    _ ≤ B₁ * B₂ ⊔ I := sup_le_sup_left Ideal.mul_le_right _
end GroundTheory.Global
