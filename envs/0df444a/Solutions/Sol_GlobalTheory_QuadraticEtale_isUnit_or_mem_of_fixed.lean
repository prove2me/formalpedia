-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.isUnit_or_mem_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:05.20216+00:00
-- url     : https://prove2.me/submissions/7423d024-ecb0-452e-be3f-cb763f3c39b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
variable [IsLocalRing R]
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range)
    {x : S} (hx : σ x = x) :
    IsUnit x ∨ x ∈ (maximalIdeal R).map (algebraMap R S) := by
  obtain ⟨r, rfl⟩ := hfix x hx
  by_cases hr : IsUnit r
  · exact Or.inl (hr.map _)
  · exact Or.inr (Ideal.mem_map_of_mem _ hr)
end GlobalTheory.QuadraticEtale
