-- Prove2me | solution 1 for OAI.Problem346.multilinear_eq_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:12:34.329267+00:00
-- url     : https://prove2.me/submissions/bc92dc52-0337-46f0-8f0c-a2dfcdb37d9c

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Spanning.lean:L26-L50
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.multilinear_eq_zero_of_span. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Spanning ----
namespace OAI

noncomputable section
open scoped BigOperators
universe u v
namespace Problem346

/-- A multilinear map vanishing on tuples from a spanning set is zero. -/
theorem multilinear_eq_zero_of_span
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {N : Type v} [AddCommGroup N] [Module ℂ N]
    {s : Set M} (hs : Submodule.span ℂ s = ⊤) (n : ℕ) :
    ∀ F : MultilinearMap ℂ (fun _ : Fin n => M) N,
      (∀ x, (∀ i, x i ∈ s) → F x = 0) → F = 0 := by
  induction n with
  | zero =>
      intro F hF
      ext x
      exact hF x (fun i => Fin.elim0 i)
  | succ n ih =>
      intro F hF
      have hc : F.curryLeft = 0 := by
        apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top F.curryLeft hs).2
        intro x
        apply ih
        intro y hy
        apply hF
        exact Fin.cases x.property hy
      ext x
      have h := congrArg (fun f : M →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => M) N =>
        f (x 0) (Fin.tail x)) hc
      simpa using h

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem346.multilinear_eq_zero_of_span.{u,v} := @_root_.OAI.Problem346.multilinear_eq_zero_of_span.{u,v}
