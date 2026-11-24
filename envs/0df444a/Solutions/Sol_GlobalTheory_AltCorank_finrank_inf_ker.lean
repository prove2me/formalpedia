-- Prove2me | solution 1 for GlobalTheory.AltCorank.finrank_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:57:41.13965+00:00
-- url     : https://prove2.me/submissions/7f0de371-da7f-4483-9cc6-77dac7d8b164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.AltCorank
theorem _root_.solution [Module.Finite K V] (S : Submodule K V) (φ : V →ₗ[K] K) (u : V)
    (hu : u ∈ S) (hφ : φ u = 1) :
    finrank K (S ⊓ LinearMap.ker φ : Submodule K V) + 1 = finrank K S := by
  have hne : (φ.domRestrict S : Module.Dual K S) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h ⟨u, hu⟩
    simp [hφ] at this
  rw [← Module.Dual.finrank_ker_add_one_of_ne_zero hne, LinearMap.ker_domRestrict,
    ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
end GlobalTheory.AltCorank
