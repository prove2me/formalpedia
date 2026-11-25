-- Prove2me | solution 1 for GlobalTheory.Count.decOrbit_root_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:23.608395+00:00
-- url     : https://prove2.me/submissions/6f3156b5-9ec1-4a38-bb7f-bc961ffa8402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DecompositionGroupOrbitRootSameStabilizer
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.Count
namespace GlobalTheory.Count
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β β' : Ω) (S : Finset Ω), (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) → ∀ g : Polynomial E, g.Monic → g.natDegree = S.card → aeval β' g = 0 → (∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β) → (∀ σ : G E Ω, ∃ d ∈ Dec (F := E) A, σ β' = d β') ∧ (∀ σ ∈ Dec (F := E) A, σ β = β → σ β' = β') := by
  intro E Ω _ _ _ _ _ A β β' S hS g hg hdeg hroot hstab
  classical

  let φ : Ω → Ω := fun x => if h : ∃ d ∈ Dec (F := E) A, d β = x then (Classical.choose h) β' else 0
  have hφ : ∀ x ∈ S, ∃ d ∈ Dec (F := E) A, d β = x ∧ φ x = d β' := by
    intro x hx
    have h := (hS x).1 hx
    refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
    simp only [φ, dif_pos h]

  have hg0 : g ≠ 0 := hg.ne_zero
  have hconj : ∀ σ : G E Ω, σ β' ∈ (g.aroots Ω).toFinset := by
    intro σ
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨hg0, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, hroot, map_zero]

  have hinj : Set.InjOn φ S := by
    intro x hx y hy hxy
    obtain ⟨d, hd, rfl, hdx⟩ := hφ x hx
    obtain ⟨e, he, rfl, hey⟩ := hφ y hy
    have h1 : (e⁻¹ * d) β' = β' := by
      rw [AlgEquiv.mul_apply, ← hdx, hxy, hey]
      exact (AlgEquiv.symm_apply_apply e β')
    have h2 := hstab _ ((Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem he) hd) h1
    rw [AlgEquiv.mul_apply] at h2
    have := congrArg e h2
    simpa using this
  have hsub : S.image φ ⊆ (g.aroots Ω).toFinset := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨d, -, -, hdx⟩ := hφ x hx
    rw [hdx]; exact hconj d
  have hcard : (g.aroots Ω).toFinset.card ≤ (S.image φ).card := by
    rw [Finset.card_image_of_injOn hinj, ← hdeg]
    calc (g.aroots Ω).toFinset.card ≤ (g.aroots Ω).card := Multiset.toFinset_card_le _
      _ ≤ (g.map (algebraMap E Ω)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := Polynomial.natDegree_map _
  have heq : S.image φ = (g.aroots Ω).toFinset := Finset.eq_of_subset_of_card_le hsub hcard

  have hin : ∀ σ : G E Ω, ∃ x ∈ S, φ x = σ β' := by
    intro σ
    have := hconj σ
    rw [← heq] at this
    exact Finset.mem_image.1 this

  have hkey : ∀ τ ∈ Dec (F := E) A, τ β' = φ (τ β) := by
    intro τ hτ
    obtain ⟨x, hx, hxe⟩ := hin τ
    obtain ⟨d, hd, rfl, hdx⟩ := hφ x hx
    have h1 : (d⁻¹ * τ) β' = β' := by
      rw [AlgEquiv.mul_apply, ← hxe, hdx]
      exact (AlgEquiv.symm_apply_apply d β')
    have h2 := hstab _ ((Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hτ) h1
    rw [AlgEquiv.mul_apply] at h2
    have h3 : τ β = d β := by
      have := congrArg d h2
      simpa using this
    rw [h3, ← hxe]
  refine ⟨fun σ => ?_, fun σ hσ hσβ => ?_⟩
  · obtain ⟨x, hx, hxe⟩ := hin σ
    obtain ⟨d, hd, -, hdx⟩ := hφ x hx
    exact ⟨d, hd, by rw [← hxe, hdx]⟩
  · have h1 := hkey σ hσ
    have h0 := hkey 1 (Dec (F := E) A).one_mem
    rw [h1, hσβ]
    exact h0.symm
end GlobalTheory.Count
