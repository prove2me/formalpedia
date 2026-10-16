-- Prove2me | solution 1 for OAI.Problem346.multilinear_agreement_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:15:08.248121+00:00
-- url     : https://prove2.me/submissions/e5250562-4029-446c-8a6d-513f265ce878

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SpanningAgreement.lean:L11-L59
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.multilinear_agreement_of_basis. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SpanningAgreement ----
namespace OAI

noncomputable section
open scoped BigOperators
open Module

namespace Problem346

/-- Equality on chosen basis generators extends to all generator tuples when each
coordinate of the generator function has a linear extension. -/
theorem multilinear_agreement_of_basis
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X K : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i) (B : ∀ i, Basis (K i) R (M i))
    (t : ∀ i, K i → X i) (ht : ∀ i k, s i (t i k) = B i k)
    (F : (∀ i, X i) → W) (G : MultilinearMap R M W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y))
    (hbase : ∀ k : ∀ i, K i, F (fun i => t i (k i)) = G (fun i => B i (k i))) :
    ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by
  classical
  have aux : ∀ (S : Finset I) (x : ∀ i, X i),
      (∀ i, i ∉ S → ∃ k, x i = t i k) → F x = G (fun i => s i (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      choose k hk using fun i => hx i (Finset.notMem_empty i)
      have he : x = fun i => t i (k i) := funext hk
      rw [he, hbase]
      simp only [ht]
    | @insert i S hi ih =>
      intro x hx
      obtain ⟨L, hL⟩ := hlinear x i
      have heq : L = G.toLinearMap (fun j => s j (x j)) i := by
        apply (B i).ext
        intro k
        rw [← ht i k, hL]
        rw [ih (Function.update x i (t i k))]
        · simp only [MultilinearMap.toLinearMap_apply]
          congr 1
          funext j
          by_cases hji : j = i
          · subst j
            simp [ht]
          · simp [Function.update_of_ne hji]
        · intro j hj
          by_cases hji : j = i
          · subst j
            exact ⟨k, by simp⟩
          · obtain ⟨l, hl⟩ := hx j (by simp [hji, hj])
            exact ⟨l, by simpa [Function.update_of_ne hji] using hl⟩
      have h := congrArg (fun L : M i →ₗ[R] W => L (s i (x i))) heq
      simpa only [hL, Function.update_eq_self, MultilinearMap.toLinearMap_apply] using h
  intro x
  exact aux Finset.univ x (by simp)

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators
open Module


theorem solution : type_of% @_root_.OAI.Problem346.multilinear_agreement_of_basis := @_root_.OAI.Problem346.multilinear_agreement_of_basis
