-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_graph_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:43.502129+00:00
-- url     : https://prove2.me/submissions/32e618aa-29b9-43b2-a18c-e8cae6b7ca04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_flip_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (Γ : Submodule E (V × V))
    (h0 : ∀ p ∈ Γ, p.1 = 0 ↔ p.2 = 0) (hΓ : ∀ p ∈ Γ, ∀ q ∈ Γ, B p.2 q.2 = B p.1 q.1)
    {r : V × V} (hr : r ∈ Γ) (hr0 : r ≠ 0) (hrad : ∀ p ∈ Γ, B p.1 r.1 = 0) :
    ∃ Γ' : Submodule E (V × V), Γ < Γ' ∧ (∀ p ∈ Γ', p.1 = 0 ↔ p.2 = 0) ∧
      ∀ p ∈ Γ', ∀ q ∈ Γ', B p.2 q.2 = B p.1 q.1 := by
  have hr1 : r.1 ≠ 0 := fun h => hr0 (Prod.ext h ((h0 r hr).1 h))
  have hrad2 : ∀ p ∈ Γ, B p.2 r.2 = 0 := fun p hp => by rw [hΓ p hp r hr, hrad p hp]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, B w₀ r.1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hr1 (hV _ h)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, B w₁ r.1 = 1 :=
    ⟨(B w₀ r.1)⁻¹ • w₀, by simp [inv_mul_cancel₀ hw₀]⟩
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.snd E V V ∘ₗ Γ.subtype) (by
      rw [LinearMap.ker_eq_bot']
      intro p hp
      exact Subtype.ext (Prod.ext ((h0 p p.2).2 hp) hp))
  obtain ⟨w, hw⟩ := exists_flip_eq h2 hc hB hV
    (B.flip w₁ ∘ₗ LinearMap.fst E V V ∘ₗ Γ.subtype ∘ₗ L)
  have hw' : ∀ p ∈ Γ, B p.2 w = B p.1 w₁ := fun p hp => by
    have h := LinearMap.congr_fun hL ⟨p, hp⟩
    have h' : L p.2 = ⟨p, hp⟩ := h
    rw [hw]
    simp [h']
  have hr1w : B r.1 w₁ = 1 := by rw [← hB, hw₁, map_one]
  have hr2w : B r.2 w = 1 := by rw [hw' r hr, hr1w]
  have hwr2 : B w r.2 = 1 := by rw [← hB, hr2w, map_one]
  obtain ⟨w₂, ha, hb⟩ : ∃ w₂, (∀ p ∈ Γ, B p.2 w₂ = B p.1 w₁) ∧ B w₂ w₂ = B w₁ w₁ := by
    have hs : c ((B w₁ w₁ - B w w) / 2) = (B w₁ w₁ - B w w) / 2 := by
      rw [map_div₀, map_sub, hB, hB, map_ofNat]
    refine ⟨w + ((B w₁ w₁ - B w w) / 2) • r.2, fun p hp => ?_, ?_⟩
    · rw [map_add, LinearMap.map_smulₛₗ, hrad2 p hp, smul_zero, add_zero, hw' p hp]
    · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        RingHom.id_apply, hs, smul_eq_mul, hr2w, hwr2, hrad2 r hr]
      field_simp
      ring
  have ha' : ∀ p ∈ Γ, B w₂ p.2 = B w₁ p.1 := fun p hp => by rw [← hB, ha p hp, hB]
  have hmem : ∀ p ∈ Γ ⊔ Submodule.span E {(w₁, w₂)},
      ∃ q ∈ Γ, ∃ t : E, p = (q.1 + t • w₁, q.2 + t • w₂) := by
    intro p hp
    obtain ⟨q, hq, z, hz, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨q, hq, t, rfl⟩
  refine ⟨Γ ⊔ Submodule.span E {(w₁, w₂)}, lt_of_le_of_ne le_sup_left fun h => ?_, ?_, ?_⟩
  · have : (w₁, w₂) ∈ Γ := by
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have h1 := hrad _ this
    rw [hw₁] at h1
    exact one_ne_zero h1
  · intro p hp
    obtain ⟨q, hq, t, rfl⟩ := hmem p hp
    have e1 : B (q.1 + t • w₁) r.1 = t := by simp [hrad q hq, hw₁]
    have e2 : B (q.2 + t • w₂) r.2 = t := by simp [hrad2 q hq, ha' r hr, hw₁]
    constructor
    · intro h
      dsimp only at h ⊢
      have ht : t = 0 := by rw [← e1, h]; simp
      subst ht
      simpa using (h0 q hq).1 (by simpa using h)
    · intro h
      dsimp only at h ⊢
      have ht : t = 0 := by rw [← e2, h]; simp
      subst ht
      simpa using (h0 q hq).2 (by simpa using h)
  · intro p hp p' hp'
    obtain ⟨q, hq, t, rfl⟩ := hmem p hp
    obtain ⟨q', hq', t', rfl⟩ := hmem p' hp'
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      hΓ q hq q' hq', ha q hq, ha' q' hq', hb]
end GlobalTheory.HermWitt
