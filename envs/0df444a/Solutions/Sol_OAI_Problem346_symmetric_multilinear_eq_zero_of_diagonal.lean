-- Prove2me | solution 1 for OAI.Problem346.symmetric_multilinear_eq_zero_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:03:50.025464+00:00
-- url     : https://prove2.me/submissions/929912fd-d514-4f65-bd92-9af869ce5413

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalPolarization.lean:L26-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.symmetric_multilinear_eq_zero_of_diagonal. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints

-- ---- from OAI.RepresentationTheory.FoulkesHowe.DiagonalPolarization ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- A symmetric continuous multilinear form is determined by its diagonal. -/
theorem continuous_symmetric_multilinear_eq_zero_of_diagonal
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin n => W) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → W),
      T (fun i => x (σ i)) = T x)
    (hdiag : ∀ x : W, T (fun _ => x) = 0) : T = 0 := by
  ext x
  have h := T.iteratedFDeriv_comp_diagonal (0 : W) x
  have hz : (fun x : W => T (fun _ => x)) = fun _ => 0 := funext hdiag
  rw [hz] at h
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply] at h
  simp only [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Algebraic polarization, without a topology on the source vector space. -/
theorem symmetric_multilinear_eq_zero_of_diagonal
    {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin n => W) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → W),
      T (fun i => x (σ i)) = T x)
    (hdiag : ∀ x : W, T (fun _ => x) = 0) : T = 0 := by
  classical
  ext x
  let L : (Fin n → ℂ) →ₗ[ℂ] W :=
    ∑ i : Fin n, (LinearMap.proj i).smulRight (x i)
  let S := T.compLinearMap (fun _ => L)
  have hL (z : Fin n → ℂ) : L z = ∑ i, z i • x i := by simp [L]
  have hS (z : Fin n → Fin n → ℂ) :
      S z = ∑ r : Fin n → Fin n, (∏ i, z i (r i)) • T (fun i => x (r i)) := by
    simp only [S, MultilinearMap.compLinearMap_apply, hL]
    rw [T.map_sum]
    simp only [T.map_smul_univ]
  have hc : Continuous S := by
    have heq : (fun z => S z) = fun z =>
        ∑ r : Fin n → Fin n, (∏ i, z i (r i)) • T (fun i => x (r i)) := funext hS
    rw [show (S : (Fin n → Fin n → ℂ) → ℂ) = _ from heq]
    fun_prop
  let C : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ := ⟨S, hc⟩
  have hC : C = 0 := continuous_symmetric_multilinear_eq_zero_of_diagonal C
    (by intro σ z; exact hsym σ (fun i => L (z i)))
    (by intro z; exact hdiag (L z))
  have hh := congrArg (fun f : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => Fin n → ℂ) ℂ => f (fun i => Pi.single i 1)) hC
  change T (fun i => L (Pi.single i 1)) = 0 at hh
  simpa [hL] using hh

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.symmetric_multilinear_eq_zero_of_diagonal := @_root_.OAI.Problem346.symmetric_multilinear_eq_zero_of_diagonal
