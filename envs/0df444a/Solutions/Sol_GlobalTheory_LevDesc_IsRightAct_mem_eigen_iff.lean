-- Prove2me | solution 1 for GlobalTheory.LevDesc.IsRightAct.mem_eigen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:43.349935+00:00
-- url     : https://prove2.me/submissions/ba7752be-4b3b-4cf4-abe4-ee9c7ff96ec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_leftRep_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)
namespace GlobalTheory.LevDesc
namespace IsRightAct
theorem _root_.solution {st : G → R →ₐ[K] R} (hs : IsRightAct st) {χ : G →* Kˣ} {F : R} :
    F ∈ eigen st χ ↔ ∀ g, hs.leftRep g F = ((χ⁻¹ g : Kˣ) : K) • F :=
  ⟨fun h g => by rw [hs.leftRep_apply, h g⁻¹, map_inv]; rfl,
    fun h g => by have := h g⁻¹; rwa [hs.leftRep_apply, inv_inv, MonoidHom.inv_apply, map_inv, inv_inv] at this⟩
end IsRightAct
end GlobalTheory.LevDesc
