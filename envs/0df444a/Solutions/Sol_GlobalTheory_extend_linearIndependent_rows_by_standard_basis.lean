-- Prove2me | solution 1 for GlobalTheory.extend_linearIndependent_rows_by_standard_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:57.365275+00:00
-- url     : https://prove2.me/submissions/107bc902-0f84-468b-ac6e-2c2f5f00462c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStandardBasisExtensionDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K) :
    LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧
      (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  intro hv
  set std : Fin n → (Fin n → K) := fun i => Pi.single i (1 : K) with hstd
  set W : Submodule K (Fin n → K) := span K (Set.range v) with hWdef
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (W.mkQ ∘ std)
  classical
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hW : finrank K W = Fintype.card J := finrank_span_eq_card hv
  have hQ := Submodule.finrank_quotient_add_finrank W
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hκ : Fintype.card κ ≤ finrank K ((Fin n → K) ⧸ W) := hli.fintype_card_le_finrank

  let C := {i : Fin n // i ∉ Set.range a}
  have hC : Fintype.card C = n - Fintype.card κ := by
    have h1 : Fintype.card C = Fintype.card (Fin n) - Fintype.card (Set.range a) := by
      simp only [C]
      rw [Fintype.card_subtype_compl]
    rw [h1, Fintype.card_fin, Set.card_range_of_injective ha]
  have hJC : Fintype.card J ≤ Fintype.card C := by omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hJC
  let e : J → Fin n := fun j => (φ j).1
  have he : Function.Injective e := fun x y h => φ.injective (Subtype.ext h)
  have heC : ∀ j, e j ∉ Set.range a := fun j => (φ j).2
  refine ⟨e, he, ?_⟩
  set f := Function.extend e v std with hf
  have hfe : ∀ j, f (e j) = v j := fun j => he.extend_apply v std j
  have hfa : ∀ k, f (a k) = std (a k) := by
    intro k
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    exact heC j ⟨k, hj.symm⟩

  have hstdspan : span K (Set.range std) = ⊤ := by
    have := (Pi.basisFun K (Fin n)).span_eq
    convert this using 2
    ext i
    simp [std, Pi.basisFun_apply]
  have hspanf : span K (Set.range f) = ⊤ := by
    have hWle : W ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨e j, hfe j⟩
    have hAle : span K (Set.range (std ∘ a)) ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact subset_span ⟨a k, hfa k⟩
    have htop : W ⊔ span K (Set.range (std ∘ a)) = ⊤ := by
      rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
      have : (W.mkQ ∘ std ∘ a) = (W.mkQ ∘ std) ∘ a := rfl
      rw [← Function.comp_assoc] at *
      rw [hspan, Set.range_comp, ← Submodule.map_span, hstdspan, Submodule.map_top, LinearMap.range_eq_top]
      exact W.mkQ_surjective
    exact eq_top_iff.mpr (htop ▸ sup_le hWle hAle)
  have hlin : LinearIndependent K f := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanf, finrank_top, hfin,
      Fintype.card_fin]
  have hunit : IsUnit (Matrix.of f) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hlin
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero
end GlobalTheory
