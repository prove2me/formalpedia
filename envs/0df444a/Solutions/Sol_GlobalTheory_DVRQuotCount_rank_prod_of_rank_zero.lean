-- Prove2me | solution 1 for GlobalTheory.DVRQuotCount.rank_prod_of_rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:37.304673+00:00
-- url     : https://prove2.me/submissions/b55b9a58-cd3b-4065-a649-ef6ca0f68855

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open GlobalTheory GlobalTheory.DVRQuotCount
open scoped TensorProduct DirectSum
namespace GlobalTheory.DVRQuotCount
theorem _root_.solution {R A B : Type} [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (hB : ∀ x : B, ∃ a : R, a ≠ 0 ∧ a • x = 0) :
    Module.rank R (A × B) = Module.rank R A := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst R A B)
  have hk : Module.rank R (LinearMap.ker (LinearMap.fst R A B)) = 0 := by
    rw [rank_eq_zero_iff]
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, hax⟩ := hB x.2
    refine ⟨a, ha, ?_⟩
    ext
    · simpa using congrArg (a • ·) (show x.1 = 0 from hx)
    · simpa using hax
  rw [LinearMap.range_eq_top.2 (fun a => ⟨(a, 0), rfl⟩), rank_top, hk, add_zero] at h
  exact h.symm
end GlobalTheory.DVRQuotCount
