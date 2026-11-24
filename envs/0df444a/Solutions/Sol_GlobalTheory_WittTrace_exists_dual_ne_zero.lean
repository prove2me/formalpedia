-- Prove2me | solution 1 for GlobalTheory.WittTrace.exists_dual_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:47.688641+00:00
-- url     : https://prove2.me/submissions/cb822e9d-e998-4a6d-bbff-0a2f249f750d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.WittTrace
theorem _root_.solution (H : Submodule E V) {x y : V} (hx : x ∉ H) (hy : y ∉ H) :
    ∃ ψ : V →ₗ[E] E, (∀ h ∈ H, ψ h = 0) ∧ ψ x ≠ 0 ∧ ψ y ≠ 0 := by
  have kill : ∀ f : Module.Dual E V, H.map f = ⊥ → ∀ h ∈ H, f h = 0 := by
    intro f hf h hh
    have hm : f h ∈ H.map f := Submodule.mem_map_of_mem hh
    rw [hf] at hm
    exact (Submodule.mem_bot E).1 hm
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  obtain ⟨g, hgy, hg⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have hf0 := kill f hf
  have hg0 := kill g hg
  by_cases hfy : f y = 0
  · by_cases hgx : g x = 0
    · refine ⟨f + g, fun h hh => ?_, ?_, ?_⟩
      · simp [hf0 h hh, hg0 h hh]
      · simpa [hgx] using hfx
      · simpa [hfy] using hgy
    · exact ⟨g, hg0, hgx, hgy⟩
  · exact ⟨f, hf0, hfx, hfy⟩
end GlobalTheory.WittTrace
