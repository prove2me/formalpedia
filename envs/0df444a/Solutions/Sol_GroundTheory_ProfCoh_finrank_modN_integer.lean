-- Prove2me | solution 1 for GroundTheory.ProfCoh.finrank_modN_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:49.786877+00:00
-- url     : https://prove2.me/submissions/26495c14-00d0-4f64-90d3-0f6f30260305

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}
variable [Fact p.Prime]
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E]
namespace GroundTheory.ProfCoh
theorem _root_.solution {n : ℕ} (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n) :
    Finite (ModN 𝒪[E] p) ∧ Module.finrank (ZMod p) (ModN 𝒪[E] p) = n := by
  have hp := (Fact.out : p.Prime)
  have hcard : Nat.card (ModN 𝒪[E] p) = p ^ n := (Nat.card_congr modNIntegerEquiv.toEquiv).trans hn
  have hfin : Finite (ModN 𝒪[E] p) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite (ModN 𝒪[E] p)
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := ModN 𝒪[E] p)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
  exact (Nat.pow_right_injective hp.two_le h).symm
end GroundTheory.ProfCoh
