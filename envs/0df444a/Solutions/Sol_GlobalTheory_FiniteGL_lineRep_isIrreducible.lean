-- Prove2me | solution 1 for GlobalTheory.FiniteGL.lineRep_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:36.499491+00:00
-- url     : https://prove2.me/submissions/40858f18-3c4d-4e0f-a755-1606b7a6b669

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
import Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply
attribute [local simp] GlobalTheory.FiniteGL.restrictMirab_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
namespace GlobalTheory.FiniteGL
theorem _root_.solution {G : Type} [Group G] (χ : G →* ℂ) : (lineRep χ).IsIrreducible := by
  have hs : IsSimpleOrder (Submodule ℂ (Fin 1 → ℂ)) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · rcases hs.eq_bot_or_eq_top W.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
end GlobalTheory.FiniteGL
