-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_torsN_uliftInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:38.917233+00:00
-- url     : https://prove2.me/submissions/81a64f33-6091-473c-8bdc-f097fb6f1f8c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10


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
namespace GroundTheory.ProfCoh
theorem _root_.solution (l : ℕ) [NeZero l] : Finite (TorsN (ULift.{u} ℤ) l) := by
  have : Subsingleton (TorsN (ULift.{u} ℤ) l) := ⟨fun x y ↦ by
    have hx := (mem_ker_lsmul_iff l (x : ULift.{u} ℤ)).mp x.2
    have hy := (mem_ker_lsmul_iff l (y : ULift.{u} ℤ)).mp y.2
    have h0 : ∀ z : ULift.{u} ℤ, l • z = 0 → z = 0 := fun z hz ↦ by
      have h := congrArg (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ) hz
      rw [map_nsmul, map_zero, nsmul_eq_mul, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h (by exact_mod_cast NeZero.ne l)
      · exact AddEquiv.ulift.injective (h.trans (map_zero _).symm)
    exact Subtype.ext ((h0 _ hx).trans (h0 _ hy).symm)⟩
  infer_instance
end GroundTheory.ProfCoh
