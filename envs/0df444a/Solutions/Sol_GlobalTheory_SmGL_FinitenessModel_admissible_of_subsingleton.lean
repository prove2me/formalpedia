-- Prove2me | solution 1 for GlobalTheory.SmGL.FinitenessModel.admissible_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:15.360816+00:00
-- url     : https://prove2.me/submissions/59c11da6-86dd-4a5f-a0dc-0403a7e0ba48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.FinitenessModel
namespace GlobalTheory.SmGL.FinitenessModel
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [Subsingleton G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hs : IsSmooth π)
    (h : π.IsIrreducible) : IsAdmissible π := by
  haveI : IsSimpleOrder (Subrepresentation π) := h
  have hfin : FiniteDimensional ℂ V := by
    by_cases hV : ∃ v : V, v ≠ 0
    · obtain ⟨v, hv⟩ := hV
      let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by
        rw [Subsingleton.elim g 1, map_one]; exact hw⟩
      rcases eq_bot_or_eq_top S with hS | hS
      · have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
        rw [hS] at this
        exact absurd this hv
      · have h2 : Submodule.span ℂ {v} = ⊤ := congrArg Subrepresentation.toSubmodule hS
        exact ⟨h2 ▸ Submodule.fg_span_singleton v⟩
    · push Not at hV
      haveI : Subsingleton V := ⟨fun a b => by rw [hV a, hV b]⟩
      infer_instance
  exact ⟨hs, fun _ _ _ => inferInstance⟩
end GlobalTheory.SmGL.FinitenessModel
