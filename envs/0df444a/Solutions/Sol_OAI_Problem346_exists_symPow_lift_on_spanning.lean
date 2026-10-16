-- Prove2me | solution 1 for OAI.Problem346.exists_symPow_lift_on_spanning
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:17:44.020241+00:00
-- url     : https://prove2.me/submissions/e0a3b42f-a94a-4d0e-bded-e5928f89ffab

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/GeneratorLift.lean:L10-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.exists_symPow_lift_on_spanning. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_multilinear_agreement_of_basis
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

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SpanningAgreement ----
namespace OAI

noncomputable section
open scoped BigOperators
open Module

namespace Problem346

/-- Construct the extension when a basis consists of specified generators. -/
theorem exists_multilinear_extension_of_basis
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X K : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i) (B : ∀ i, Basis (K i) R (M i))
    (t : ∀ i, K i → X i) (ht : ∀ i k, s i (t i k) = B i k)
    (F : (∀ i, X i) → W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y)) :
    ∃ G : MultilinearMap R M W, ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by
  let L : (PiTensorProduct R M) →ₗ[R] W :=
    (Basis.piTensorProduct B).constr R (fun k => F (fun i => t i (k i)))
  let G : MultilinearMap R M W := L.compMultilinearMap (PiTensorProduct.tprod R)
  refine ⟨G, multilinear_agreement_of_basis s B t ht F G hlinear ?_⟩
  intro k
  change F (fun i => t i (k i)) = L (PiTensorProduct.tprod R (fun i => B i (k i)))
  rw [← Basis.piTensorProduct_apply]
  dsimp only [L]
  rw [Basis.constr_basis]

/-- Separate linear extendibility on spanning generators gives a multilinear extension. -/
theorem exists_multilinear_extension_of_spanning
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i)
    (hspan : ∀ i, Submodule.span R (Set.range (s i)) = ⊤)
    (F : (∀ i, X i) → W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y)) :
    ∃ G : MultilinearMap R M W, ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by
  classical
  have hs (i : I) : ⊤ ≤ Submodule.span R (Set.range (s i)) := by rw [hspan i]
  let B := fun i => Basis.ofSpan (hs i)
  have hpre : ∀ i k, ∃ x, s i x = B i k := by
    intro i k
    exact Basis.ofSpan_subset (hs i) (Set.mem_range_self k)
  choose t ht using hpre
  exact exists_multilinear_extension_of_basis s B t ht F hlinear

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.GeneratorLift ----
namespace OAI

noncomputable section
namespace Problem346

/-- A separately linearly extendible symmetric formula on spanning generators
induces a linear map out of the homogeneous symmetric power. -/
theorem exists_symPow_lift_on_spanning
    {n : ℕ} {X V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (s : X → V) (hs : Submodule.span ℂ (Set.range s) = ⊤)
    (F : (Fin n → X) → W)
    (hlinear : ∀ x : Fin n → X, ∀ i : Fin n,
      ∃ L : V →ₗ[ℂ] W, ∀ y, L (s y) = F (Function.update x i y))
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → X),
      F (fun i => x (σ i)) = F x) :
    ∃ L : SymPow n V →ₗ[ℂ] W, ∀ x : Fin n → X,
      L (symMonomial n V (fun i => s (x i))) = F x := by
  classical
  obtain ⟨G, hG⟩ := exists_multilinear_extension_of_spanning
    (fun _ : Fin n => s) (fun _ => hs) F hlinear
  have hGs : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V),
      G (fun i => v (σ i)) = G v := by
    intro σ
    have h : G.domDomCongr σ = G := by
      apply multilinear_ext_of_span hs n
      intro v hv
      choose x hx using hv
      have he : v = fun i => s (x i) := funext (fun i => (hx i).symm)
      subst v
      change G (fun i => s (x (σ i))) = G (fun i => s (x i))
      rw [← hG, ← hG, hsym]
    intro v
    exact congrArg (fun G : MultilinearMap ℂ (fun _ : Fin n => V) W => G v) h
  obtain ⟨L, hL⟩ := exists_symPow_lift G hGs
  exact ⟨L, fun x => (hL _).trans (hG x).symm⟩

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution : type_of% @_root_.OAI.Problem346.exists_symPow_lift_on_spanning := @_root_.OAI.Problem346.exists_symPow_lift_on_spanning
