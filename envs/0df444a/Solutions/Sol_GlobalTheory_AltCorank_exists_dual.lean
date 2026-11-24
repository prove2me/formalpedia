-- Prove2me | solution 1 for GlobalTheory.AltCorank.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:57:40.416111+00:00
-- url     : https://prove2.me/submissions/79a33a04-54e7-42ee-81b5-ade76aa43bbd

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
theorem _root_.solution (S : Submodule K V) (u : V) (hu : u ∉ S) :
    ∃ φ : V →ₗ[K] K, φ u = 1 ∧ ∀ x ∈ S, φ x = 0 := by
  obtain ⟨f, hf, hS⟩ := S.exists_dual_map_eq_bot_of_notMem hu inferInstance
  refine ⟨(f u)⁻¹ • f, by simp [hf], fun x hx => ?_⟩
  have : f x ∈ S.map f := ⟨x, hx, rfl⟩
  rw [hS] at this
  simp [(Submodule.mem_bot K).1 this]
end GlobalTheory.AltCorank
