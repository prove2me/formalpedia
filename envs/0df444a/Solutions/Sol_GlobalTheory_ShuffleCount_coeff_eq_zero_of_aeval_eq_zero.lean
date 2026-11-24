-- Prove2me | solution 1 for GlobalTheory.ShuffleCount.coeff_eq_zero_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:56.765498+00:00
-- url     : https://prove2.me/submissions/26ae6501-b31c-4a0a-93cb-5a2dfc16eca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ShuffleCountLinearIndependentClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory
namespace GlobalTheory.ShuffleCount
open MvPolynomial
private theorem aeval_killCompl {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (h0 : ∀ Δ ∉ U, φ Δ = 0) (P : MvPolynomial S ℚ) :
    aeval (fun Δ : U => φ Δ) (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = aeval φ P := by
  classical
  have key : (aeval (fun Δ : U => φ Δ)).comp (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S))) = aeval φ := by
    apply MvPolynomial.algHom_ext
    intro Δ
    by_cases hΔ : Δ ∈ U
    · have hX : (X Δ : MvPolynomial S ℚ) = rename Subtype.val (X (⟨Δ, hΔ⟩ : U)) := by rw [rename_X]
      rw [AlgHom.comp_apply]
      conv_lhs => rw [hX]
      rw [killCompl_rename_app, aeval_X, aeval_X]
    · rw [AlgHom.comp_apply, aeval_X, h0 Δ hΔ, X, killCompl_monomial_eq_zero_of_not_subset, map_zero]
      intro h
      obtain ⟨⟨_, hmem⟩, rfl⟩ := h (by simp : Δ ∈ (↑(Finsupp.single Δ 1).support : Set S))
      exact hΔ hmem
  exact AlgHom.congr_fun key P
private theorem coeff_killCompl_comapDomain {S : Type*} (U : Set S) (P : MvPolynomial S ℚ) (m : S →₀ ℕ)
    (hm : ↑m.support ⊆ Set.range (Subtype.val : U → S)) :
    coeff (m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn)
      (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n r =>
    by_cases hn : ↑n.support ⊆ Set.range (Subtype.val : U → S)
    · rw [killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hn, coeff_monomial, coeff_monomial]
      have hiff : n.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn =
          m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn ↔ n = m := by
        constructor
        · intro h
          rw [← Finsupp.mapDomain_comapDomain _ Subtype.val_injective n hn,
            ← Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hm, h]
        · rintro rfl
          rfl
      simp only [hiff]
    · rw [killCompl_monomial_eq_zero_of_not_subset _ _ hn, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact hn hm
  | add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ]
end GlobalTheory.ShuffleCount
end

set_option autoImplicit false
open GlobalTheory
open GlobalTheory GlobalTheory.ShuffleCount
open MvPolynomial
namespace GlobalTheory.ShuffleCount
theorem _root_.solution {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ)) (h0 : ∀ Δ ∉ U, φ Δ = 0)
    (P : MvPolynomial S ℚ) (hP : aeval φ P = 0) (m : S →₀ ℕ) (hm : ∀ Δ ∈ m.support, Δ ∈ U) :
    coeff m P = 0 := by
  classical
  have hm' : ↑m.support ⊆ Set.range (Subtype.val : U → S) := fun Δ hΔ =>
    ⟨⟨Δ, hm Δ (Finset.mem_coe.1 hΔ)⟩, rfl⟩
  rw [← coeff_killCompl_comapDomain U P m hm']
  have hQ : killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 hind
    rw [map_zero, aeval_killCompl U φ h0 P, hP]
  rw [hQ, coeff_zero]
end GlobalTheory.ShuffleCount
