-- Prove2me | solution 1 for OAI.Problem346.plethysm_linearMap_ext
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:13:44.331347+00:00
-- url     : https://prove2.me/submissions/16061a8f-f904-4738-8f47-3df68b80c67b

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Spanning.lean:L64-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.plethysm_linearMap_ext. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_multilinear_eq_zero_of_span

-- ---- from OAI.RepresentationTheory.FoulkesHowe.Spanning ----
namespace OAI

noncomputable section
open scoped BigOperators
universe u v
namespace Problem346

/-- Multilinear maps agree if they agree on tuples from a spanning set. -/
theorem multilinear_ext_of_span
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {N : Type v} [AddCommGroup N] [Module ℂ N]
    {s : Set M} (hs : Submodule.span ℂ s = ⊤) (n : ℕ)
    (F G : MultilinearMap ℂ (fun _ : Fin n => M) N)
    (h : ∀ x, (∀ i, x i ∈ s) → F x = G x) : F = G := by
  apply sub_eq_zero.mp
  apply multilinear_eq_zero_of_span hs n
  intro x hx
  simp only [sub_apply, h x hx, sub_self]

/-- Linear maps out of a plethysm are determined by double monomials. -/
theorem plethysm_linearMap_ext (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W]
    (f g : SymPow b (SymPow a V) →ₗ[ℂ] W)
    (h : ∀ x : Fin b → Fin a → V,
      f (symMonomial b (SymPow a V) (fun j => symMonomial a V (x j))) =
      g (symMonomial b (SymPow a V) (fun j => symMonomial a V (x j)))) : f = g := by
  classical
  apply symPow_linearMap_ext b (SymPow a V)
  have hm : f.compMultilinearMap (symMonomialMultilinear b (SymPow a V)) =
      g.compMultilinearMap (symMonomialMultilinear b (SymPow a V)) := by
    apply multilinear_ext_of_span (span_symMonomial a V) b
    intro x hx
    choose v hv using hx
    have hx' : x = fun j => symMonomial a V (v j) := funext (fun j => (hv j).symm)
    subst x
    exact h v
  intro x
  exact congrArg (fun F => F x) hm

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem346.plethysm_linearMap_ext.{u,v} := @_root_.OAI.Problem346.plethysm_linearMap_ext.{u,v}
