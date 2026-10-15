-- Prove2me | solution 1 for OAI.ParityWL.binary_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:08:41.794991+00:00
-- url     : https://prove2.me/submissions/a7d8f207-077f-4627-96f4-266a74e86d41

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean:L235-L254
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.binary_alternative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

-- ---- from OAI.Combinatorics.ParityLifts.LiftCounts ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

end Lifts

section LiftCounts

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

end LiftCounts

section BinaryDuality

variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

lemma bit_zero_or_one (b : Bit) : b = 0 ∨ b = 1 := by
  have h : ∀ b : Bit, b = 0 ∨ b = 1 := by decide
  exact h b

/-- Linear-algebra separation without a rank assumption. -/
theorem binary_alternative (L : E →ₗ[Bit] H) (c : H) :
    (¬ ∃ z, L z = c) ↔
      ∃ f : H →ₗ[Bit] Bit, (∀ z, f (L z) = 0) ∧ f c = 1 := by
  classical
  constructor
  · intro h
    have hc : c ∉ LinearMap.range L := h
    obtain ⟨f, hf, hmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
    refine ⟨f, ?_, ?_⟩
    · intro z
      have hz : f (L z) ∈ (LinearMap.range L).map f :=
        ⟨L z, ⟨z, rfl⟩, rfl⟩
      rwa [hmap, Submodule.mem_bot] at hz
    · exact (bit_zero_or_one (f c)).resolve_left hf
  · rintro ⟨f, hf, hc⟩ ⟨z, hz⟩
    have h := hf z
    rw [hz, hc] at h
    exact one_ne_zero h

end BinaryDuality

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ParityWL.binary_alternative := @_root_.OAI.ParityWL.binary_alternative
