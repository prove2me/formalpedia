-- Prove2me | solution 1 for GlobalTheory.ringHom_injective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:43.989693+00:00
-- url     : https://prove2.me/submissions/cfa8829c-e17e-4f09-be15-1a248c126c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A : Type*} [CommRing A]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] (φ : A →+* A)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  let c : ℕ →o Ideal A := ⟨fun n => RingHom.ker (φ ^ n), monotone_nat_of_le_succ fun n x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hx, map_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherianRing A› c
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, (φ ^ n) y = x := by
    rw [RingHom.coe_pow]
    exact hφ.iterate n x
  have : y ∈ c (n + 1) := by
    change (φ ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hx]
  rw [← hn (n + 1) n.le_succ] at this
  exact this
end GlobalTheory
