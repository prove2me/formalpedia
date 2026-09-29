-- Prove2me | solution 1 for NumberField.apply_norm_lt_zero_iff_odd_card_filter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9a332e9c-56ac-5d91-aabb-f688df5e0aeb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_apply_norm_lt_zero_iff_odd_card_filter

set_option autoImplicit false

noncomputable section

namespace NormSign

open NumberField NumberField.ComplexEmbedding Finset Complex
open scoped Classical ComplexConjugate

theorem prod_lt_zero_iff_odd {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∏ i ∈ s, f i < 0 ↔ Odd (s.filter (fun i => f i < 0)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfa : f a ≠ 0 := hf a (mem_insert_self a s)
    have ih' := ih (fun i hi => hf i (mem_insert_of_mem hi))
    have hne : ∏ i ∈ s, f i ≠ 0 := prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)
    rw [prod_insert ha, filter_insert]
    rcases lt_or_gt_of_ne hfa with hneg | hpos
    · rw [if_pos hneg, card_insert_of_notMem (fun h => ha (mem_filter.mp h).1),
        Nat.odd_add_one, ← ih']
      constructor
      · intro h h'
        nlinarith
      · intro h
        rcases lt_or_gt_of_ne hne with h1 | h1
        · exact absurd h1 h
        · exact mul_neg_of_neg_of_pos hneg h1
    · rw [if_neg (not_lt.mpr hpos.le), ← ih']
      constructor
      · intro h
        by_contra h'
        push Not at h'
        nlinarith
      · intro h
        exact mul_neg_of_pos_of_neg hpos h

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

abbrev cx (τ : K →+* ℝ) : K →+* ℂ := ofRealHom.comp τ

omit [NumberField K] in
theorem cx_apply (τ : K →+* ℝ) (x : K) : cx τ x = (τ x : ℂ) := rfl

omit [NumberField K] in
theorem conj_cx (τ : K →+* ℝ) (x : K) : conj (cx τ x) = cx τ x := by
  rw [cx_apply, conj_ofReal]

def embAbove (τ : K →+* ℝ) : Finset (F →+* ℂ) :=
  univ.filter fun σ => σ.comp (algebraMap K F) = cx τ

omit [NumberField K] in
theorem mem_embAbove {τ : K →+* ℝ} {σ : F →+* ℂ} :
    σ ∈ embAbove (F := F) τ ↔ σ.comp (algebraMap K F) = cx τ := by
  simp [embAbove]

omit [NumberField K] in
theorem conjugate_mem_embAbove {τ : K →+* ℝ} {σ : F →+* ℂ} (h : σ ∈ embAbove (F := F) τ) :
    conjugate σ ∈ embAbove (F := F) τ := by
  rw [mem_embAbove] at h ⊢
  ext x
  have := congr($h x)
  simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
  rw [conjugate_coe_eq, this]
  exact conj_cx τ x

theorem cx_norm_eq_prod (τ : K →+* ℝ) (β : F) :
    cx τ (Algebra.norm K β) = ∏ σ ∈ embAbove (F := F) τ, σ β := by
  classical
  letI : Algebra K ℂ := (cx τ).toAlgebra
  have h := Algebra.norm_eq_prod_embeddings K ℂ β
  rw [show algebraMap K ℂ = cx τ from rfl] at h
  rw [h]

  refine Finset.prod_bij' (fun σ _ => (σ : F →+* ℂ))
    (fun σ hσ => { toRingHom := σ, commutes' := fun x => ?_ }) ?_ ?_ ?_ ?_ ?_
  · exact congr($(mem_embAbove.mp hσ) x)
  · intro σ _
    rw [mem_embAbove]
    ext x
    exact σ.commutes x
  · intro σ hσ; exact mem_univ _
  · intro σ _; ext; rfl
  · intro σ _; rfl
  · intro σ _; rfl

omit [NumberField K] in

theorem prod_nonreal_eq (τ : K →+* ℝ) (β : F) (hβ : β ≠ 0) :
    ∏ σ ∈ (embAbove (F := F) τ).filter (fun σ => ¬ IsReal σ), σ β =
      ((∏ σ ∈ (embAbove (F := F) τ).filter (fun σ => ¬ IsReal σ), ‖σ β‖ : ℝ) : ℂ) := by
  classical
  set T := (embAbove (F := F) τ).filter (fun σ => ¬ IsReal σ) with hT
  have hne : ∀ σ : F →+* ℂ, σ β ≠ 0 := fun σ => (map_ne_zero σ).mpr hβ

  have key : ∏ σ ∈ T, (σ β / (‖σ β‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun σ _ => conjugate σ) ?_ ?_ ?_ ?_
    · intro σ _
      rw [conjugate_coe_eq, norm_conj, div_mul_div_comm, mul_conj, normSq_eq_norm_sq]
      have h0 : (‖σ β‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr (hne σ))
      push_cast
      field_simp
    · intro σ hσ _
      have h := (mem_filter.mp hσ).2
      rwa [isReal_iff] at h
    · intro σ hσ
      obtain ⟨h1, h2⟩ := mem_filter.mp hσ
      exact mem_filter.mpr ⟨conjugate_mem_embAbove h1, by rwa [isReal_conjugate_iff]⟩
    · intro σ _
      exact involutive_conjugate F σ
  rw [prod_div_distrib, div_eq_one_iff_eq (prod_ne_zero_iff.mpr fun σ _ => by
    exact_mod_cast (norm_ne_zero_iff.mpr (hne σ)))] at key
  rw [key]
  push_cast
  rfl

omit [NumberField K] in

theorem prod_real_eq (τ : K →+* ℝ) (β : F) :
    ∏ σ ∈ (embAbove (F := F) τ).filter (fun σ => IsReal σ), σ β =
      ((∏ ψ ∈ univ.filter (fun ψ : F →+* ℝ => ψ.comp (algebraMap K F) = τ), ψ β : ℝ) : ℂ) := by
  classical
  push_cast
  symm
  refine Finset.prod_bij' (fun ψ _ => ofRealHom.comp ψ) (fun σ hσ => (mem_filter.mp hσ).2.embedding)
    ?_ ?_ ?_ ?_ ?_
  · intro ψ hψ
    have h := (mem_filter.mp hψ).2
    refine mem_filter.mpr ⟨mem_embAbove.mpr ?_, ?_⟩
    · ext x
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← h]
      rfl
    · rw [isReal_iff]; ext x; simp [conjugate_coe_eq]
  · intro σ hσ
    obtain ⟨h1, h2⟩ := mem_filter.mp hσ
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    ext x
    apply Complex.ofReal_injective
    have := congr($(mem_embAbove.mp h1) x)
    simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
    rw [IsReal.coe_embedding_apply, this]
    rfl
  · intro ψ _
    ext x
    apply Complex.ofReal_injective
    rw [IsReal.coe_embedding_apply]
    rfl
  · intro σ hσ
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    exact IsReal.coe_embedding_apply (mem_filter.mp hσ).2 x
  · intro ψ _
    rfl

theorem main (τ : K →+* ℝ) (β : F) (hβ : β ≠ 0) :
    τ (Algebra.norm K β) < 0 ↔
      Odd (univ.filter (fun ψ : F →+* ℝ => ψ.comp (algebraMap K F) = τ ∧ ψ β < 0)).card := by
  classical
  set R := univ.filter (fun ψ : F →+* ℝ => ψ.comp (algebraMap K F) = τ) with hR
  set P : ℝ := ∏ σ ∈ (embAbove (F := F) τ).filter (fun σ => ¬ IsReal σ), ‖σ β‖ with hP
  have hPpos : 0 < P := prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hβ)
  have hfac : τ (Algebra.norm K β) = (∏ ψ ∈ R, ψ β) * P := by
    apply Complex.ofReal_injective
    rw [← cx_apply, cx_norm_eq_prod,
      ← prod_filter_mul_prod_filter_not (embAbove τ) (fun σ => IsReal σ), prod_real_eq,
      prod_nonreal_eq τ β hβ]
    push_cast
    rw [hR, hP]
    push_cast
    rfl
  rw [hfac, mul_neg_iff, prod_lt_zero_iff_odd R (fun ψ => ψ β) (fun ψ _ => (map_ne_zero ψ).mpr hβ),
    hR, filter_filter]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h hPpos.not_gt
    · exact h
  · intro h
    exact Or.inr ⟨h, hPpos⟩

end NormSign

end

open NumberField
open scoped Classical

universe u v

theorem solution
    (K : Type u) (F : Type v) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    (τ : K →+* ℝ) (β : F) (hβ : β ≠ 0) :
    τ (Algebra.norm K β) < 0 ↔
      Odd (Finset.univ.filter (fun ψ : F →+* ℝ =>
        ψ.comp (algebraMap K F) = τ ∧ ψ β < 0)).card :=
  NormSign.main τ β hβ

end S_NumberField_apply_norm_lt_zero_iff_odd_card_filter
end P2MW
export P2MW.S_NumberField_apply_norm_lt_zero_iff_odd_card_filter (solution)
