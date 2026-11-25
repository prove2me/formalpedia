-- Prove2me | solution 1 for GlobalTheory.JacStages.isSubquotient_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:34.86983+00:00
-- url     : https://prove2.me/submissions/a7c8de0a-4c1c-41da-8725-ed2f7bd27097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


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
open GlobalTheory GlobalTheory.JacStages
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.JacStages
theorem _root_.solution {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (ψ : G' →* G)
    (hψ : Function.Surjective ψ) (h : IsSubquotient (σ.comp ψ) (ρ.comp ψ)) : IsSubquotient σ ρ := by
  obtain ⟨S, f, hf⟩ := h
  refine ⟨⟨S.toSubmodule, fun g v hv => ?_⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf⟩
  · obtain ⟨g', rfl⟩ := hψ g
    exact S.apply_mem_toSubmodule g' hv
  · obtain ⟨g', rfl⟩ := hψ g
    exact f.isIntertwining' g'
end GlobalTheory.JacStages
