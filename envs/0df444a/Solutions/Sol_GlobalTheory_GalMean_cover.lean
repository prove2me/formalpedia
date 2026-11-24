-- Prove2me | solution 1 for GlobalTheory.GalMean.cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:40.701314+00:00
-- url     : https://prove2.me/submissions/71018e81-8704-49a7-9d42-d171bef751df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open Classical
namespace GlobalTheory.GalMean
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ)
    (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hE : Equidistributed φK j₀ 𝔞)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [IsGalois ℚ L] [NumberField L] (hK : ∀ x : K, φK x ∈ L)
    (hj : j₀ ∈ L)
    (hcard : 2 * (Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x)).card = Module.finrank ℚ L) :
    ∃ ext : (L →+* ℂ) → (ℂ ≃+* ℂ),
      (∀ τ ∈ Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x),
        Fixes φK (ext τ) ∧ ∀ x : L, ext τ (x : ℂ) = τ x) ∧
      ∀ C : ClassGroup (𝓞 K), ((Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x)).filter
        (fun τ => ClassGroup.mk K (𝔞 (ext τ)) = C)).card * (2 * classNumber K) = Module.finrank ℚ L := by
  set Fx := Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x) with hFx
  set S : ClassGroup (𝓞 K) → Finset (L →+* ℂ) := fun C => Finset.univ.filter
    (fun τ => ∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = C) with hSdef
  have hS : ∀ C, (S C).card * (2 * classNumber K) = Module.finrank ℚ L := by
    intro C
    have := hE.2.2 L inferInstance inferInstance hK hj C
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this

  have hsame : ∀ (τ : L →+* ℂ) (σ σ' : ℂ ≃+* ℂ), Fixes φK σ → Fixes φK σ' → (∀ x : L, σ (x : ℂ) = τ x) →
      (∀ x : L, σ' (x : ℂ) = τ x) → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') := by
    intro τ σ σ' hσ hσ' h h'
    refine (hE.2.1 σ σ' hσ hσ').2 ?_
    have e1 := h ⟨j₀, hj⟩
    have e2 := h' ⟨j₀, hj⟩
    simp only at e1 e2
    rw [e1, e2]
  have hdisj : ∀ C ∈ (Finset.univ : Finset (ClassGroup (𝓞 K))), ∀ C' ∈ (Finset.univ : Finset (ClassGroup (𝓞 K))),
      C ≠ C' → Disjoint (S C) (S C') := by
    intro C _ C' _ hCC'
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨σ, hσ, hσt, hC⟩ := (Finset.mem_filter.1 ht).2
    obtain ⟨σ', hσ', hσt', hC'⟩ := (Finset.mem_filter.1 ht').2
    exact hCC' (hC.symm.trans ((hsame t σ σ' hσ hσ' hσt hσt').trans hC'))
  have hsub : Finset.univ.biUnion S ⊆ Fx := by
    intro t ht
    obtain ⟨C, -, htC⟩ := Finset.mem_biUnion.1 ht
    obtain ⟨σ, hσ, hσt, -⟩ := (Finset.mem_filter.1 htC).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩
    rw [← hσt]; exact hσ x
  have hh : 0 < classNumber K := Fintype.card_pos
  have hcardU : 2 * (Finset.univ.biUnion S).card = Module.finrank ℚ L := by
    rw [Finset.card_biUnion hdisj]
    have e : (∑ C, (S C).card) * (2 * classNumber K) = classNumber K * Module.finrank ℚ L := by
      rw [Finset.sum_mul, Finset.sum_congr rfl (fun C _ => hS C), Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rfl
    have e2 : (2 * ∑ C, (S C).card) * classNumber K = Module.finrank ℚ L * classNumber K := by
      rw [mul_comm (Module.finrank ℚ L), ← e]; ring
    exact Nat.eq_of_mul_eq_mul_right hh e2
  have hU : Finset.univ.biUnion S = Fx := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hex : ∀ τ : L →+* ℂ, ∃ σ : ℂ ≃+* ℂ, τ ∈ Fx → Fixes φK σ ∧ ∀ x : L, σ (x : ℂ) = τ x := by
    intro τ
    by_cases hτ : τ ∈ Fx
    · rw [← hU] at hτ
      obtain ⟨C, -, htC⟩ := Finset.mem_biUnion.1 hτ
      obtain ⟨σ, hσ, hσt, -⟩ := (Finset.mem_filter.1 htC).2
      exact ⟨σ, fun _ => ⟨hσ, hσt⟩⟩
    · exact ⟨RingEquiv.refl ℂ, fun h => absurd h hτ⟩
  choose ext hext using hex
  refine ⟨ext, fun τ hτ => hext τ hτ, fun C => ?_⟩
  rw [← hS C]
  congr 1
  congr 1
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  constructor
  · rintro ⟨hτ, hC⟩
    exact ⟨ext τ, (hext τ (by simpa [Fx] using hτ)).1, (hext τ (by simpa [Fx] using hτ)).2, hC⟩
  · rintro ⟨σ, hσ, hσt, hC⟩
    have hτ : τ ∈ Fx := hsub (Finset.mem_biUnion.2 ⟨C, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, σ, hσ, hσt, hC⟩⟩)
    refine ⟨by simpa [Fx] using hτ, ?_⟩
    rw [hsame τ (ext τ) σ (hext τ hτ).1 hσ (hext τ hτ).2 hσt, hC]
end GlobalTheory.GalMean
