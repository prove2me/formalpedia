-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommStep.comm_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:12:12.843859+00:00
-- url     : https://prove2.me/submissions/a0df7ed7-bca2-48c0-83bd-7212926c94dc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Theorems.Thm_GlobalTheory_CompanionTheory_CommStep_finrank_map_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommStep
open Module
namespace GlobalTheory.CompanionTheory.CommStep
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
    (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) → ∀ x : ℕ,
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      x * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        Module.finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ x))) := by
  intro V _ _ _ l a hc x
  induction x with
  | zero =>
    have hid : LinearMap.mulRight ℂ (a 0 ^ 0) = LinearMap.id :=
      LinearMap.ext fun b => by simp
    rw [hid, Submodule.map_id, Nat.zero_mul, Nat.zero_add, Subalgebra.finrank_toSubmodule]
  | succ x ih =>
    have h := GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le a hc x
    rw [add_mul, one_mul]
    omega
end GlobalTheory.CompanionTheory.CommStep
