-- Prove2me | solution 1 for OAI.Problem346.vanishing_on_products_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:20:34.170876+00:00
-- url     : https://prove2.me/submissions/e2f877dc-4088-4b30-aa78-4f69cff6bcc8

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/VanishingOne.lean:L9-L23
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.vanishing_on_products_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap

-- ---- from OAI.RepresentationTheory.FoulkesHowe.VanishingOne ----
namespace OAI

noncomputable section
universe u
namespace Problem346

theorem vanishing_on_products_one (V : Type u) [AddCommGroup V] [Module ℂ V]
    (b : ℕ) (T : SymmetricMultilinearForm 1 b V)
    (h : ∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) : T = 0 := by
  have hspan : Submodule.span ℂ (Set.range (symMonomial b V)) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff (symPowSubmodule b V)
      (fun v => Submodule.subset_span (Set.mem_range_self v))).mpr rfl
  apply MultilinearMap.ext_of_span_eq_top (g := fun (_ : Fin 1) => symMonomial b V)
    (fun _ => hspan)
  intro v
  have hv : (fun i : Fin 1 => symMonomial b V (v i)) =
      (fun _ : Fin 1 => symMonomial b V (v 0)) := by
    funext i
    rw [Fin.eq_zero i]
  rw [hv]
  exact h (v 0)

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution.{u} : type_of% @_root_.OAI.Problem346.vanishing_on_products_one.{u} := @_root_.OAI.Problem346.vanishing_on_products_one.{u}
