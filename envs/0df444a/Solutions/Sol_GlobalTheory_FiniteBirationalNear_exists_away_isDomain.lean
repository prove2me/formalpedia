-- Prove2me | solution 1 for GlobalTheory.FiniteBirationalNear.exists_away_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:08:01.175882+00:00
-- url     : https://prove2.me/submissions/6bcacd21-516f-4199-8dea-4b9621e9f4c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
import Theorems.Thm_GlobalTheory_FiniteBirationalNear_exists_common_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.FiniteBirationalNear
namespace GlobalTheory.FiniteBirationalNear
theorem _root_.solution {A O : Type*} [CommRing A] [IsNoetherianRing A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] :
    ∃ s ∈ S, ∀ (P : Type) [CommRing P] [Algebra A P] [IsLocalization.Away s P], IsDomain P := by
  obtain ⟨s, hs, h⟩ := exists_common_smul_mem S
    (IsNoetherian.noetherian (RingHom.ker (algebraMap A O))) ⊥ fun m hm => by
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff S O m).1 hm
      exact ⟨c, c.2, hc⟩
  refine ⟨s, hs, fun P _ _ _ => ?_⟩
  have hu : IsUnit (algebraMap A O s) := IsLocalization.map_units O ⟨s, hs⟩
  refine Function.Injective.isDomain (IsLocalization.Away.lift (S := P) s hu) ?_
  rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro e
    have := congrArg (IsLocalization.Away.lift (S := P) s hu) e
    simpa using this
  · intro e
    have h1 : x - y ∈ RingHom.ker (algebraMap A O) := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 : s * (x - y) = 0 := h _ h1
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalization.map_eq_zero_iff (.powers s) P _).2 ⟨⟨s, Submonoid.mem_powers s⟩, h2⟩
end GlobalTheory.FiniteBirationalNear
