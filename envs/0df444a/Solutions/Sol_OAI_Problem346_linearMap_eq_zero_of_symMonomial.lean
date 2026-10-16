-- Prove2me | solution 1 for OAI.Problem346.linearMap_eq_zero_of_symMonomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:07:06.263671+00:00
-- url     : https://prove2.me/submissions/e2634eef-f539-4122-b4d9-05dfaeef0c70

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/MonomialMultilinear.lean:L51-L69
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.linearMap_eq_zero_of_symMonomial. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear ----
namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace Problem346

/-- Monomial values determine every linear map out of a symmetric power. -/
theorem linearMap_eq_zero_of_symMonomial (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]
    (φ : SymPow n V →ₗ[ℂ] W)
    (hφ : ∀ x : Fin n → V, φ (symMonomial n V x) = 0) : φ = 0 := by
  ext x
  change φ x = 0
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact hφ v
  | zero => exact map_zero φ
  | add x y hx hy ihx ihy =>
      change φ (⟨x, hx⟩ + ⟨y, hy⟩) = 0
      rw [map_add, ihx, ihy, add_zero]
  | smul c x hx ih =>
      change φ (c • (⟨x, hx⟩ : SymPow n V)) = 0
      rw [map_smul, ih, smul_zero]

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem346.linearMap_eq_zero_of_symMonomial.{u,v} := @_root_.OAI.Problem346.linearMap_eq_zero_of_symMonomial.{u,v}
