-- Prove2me | solution 1 for GlobalTheory.TypeComplement.exists_typeComplement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:26.377806+00:00
-- url     : https://prove2.me/submissions/88255aed-0962-4b6e-bd6f-ab96907d47f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
import Theorems.Thm_GlobalTheory_TypeComplement_toSubmodule_bot
import Theorems.Thm_GlobalTheory_TypeComplement_imRep_atom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement
namespace GlobalTheory.TypeComplement
theorem _root_.solution : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  intro K V _ _ _ ρ hss hsum X hcl
  haveI : ComplementedLattice (Subrepresentation ρ) := hss
  let Y : Subrepresentation ρ := supRep (fun S => IsAtom S ∧ ¬ S ≤ X)
  have hYle : ∀ S : Subrepresentation ρ, IsAtom S → ¬ S ≤ X → S.toSubmodule ≤ Y.toSubmodule :=
    fun S hA hn => le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ ¬ S ≤ X) =>
      S.toSubmodule) S ⟨hA, hn⟩

  obtain ⟨Y₀, hY₀⟩ := exists_isCompl X
  have hXY₀ : IsCompl X.toSubmodule Y₀.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.inf_eq_bot
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.sup_eq_top
  let p : V →ₗ[ℂ] V := X.toSubmodule.projection Y₀.toSubmodule hXY₀
  have hp : ∀ k v, p (ρ k v) = ρ k (p v) := by
    intro k v
    have hv : v ∈ X.toSubmodule ⊔ Y₀.toSubmodule := by rw [hXY₀.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : ∀ {a b : V}, a ∈ X.toSubmodule → b ∈ Y₀.toSubmodule → p (a + b) = a := by
      intro a b ha hb
      rw [map_add, Submodule.projection_apply_of_mem_left _ ha]
      have : p b = 0 := (Submodule.projection_apply_eq_zero_iff hXY₀).mpr hb
      rw [this, add_zero]
    rw [map_add, h1 (X.apply_mem_toSubmodule k hx) (Y₀.apply_mem_toSubmodule k hy), h1 hx hy]

  have hYY₀ : Y.toSubmodule ≤ Y₀.toSubmodule := by
    refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
    by_contra hc
    have hne : ∃ s ∈ S.toSubmodule, p s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc fun s hs => (Submodule.projection_apply_eq_zero_iff hXY₀).mp (h s hs)
    obtain ⟨_, ⟨e⟩⟩ := imRep_atom p hp hA hne
    have hle : imRep p hp S ≤ X := by
      rintro _ ⟨s, _, rfl⟩
      exact Submodule.projection_apply_mem hXY₀ s
    exact hn (hcl S _ hA hle ⟨e⟩)
  have hdisj : X.toSubmodule ⊓ Y.toSubmodule = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hYY₀).trans (disjoint_iff.mp hXY₀.disjoint).le)
  refine ⟨Y, ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩, ?_, ?_⟩
  ·
    refine eq_top_iff.mpr ?_
    show (⊤ : Subrepresentation ρ).toSubmodule ≤ _
    refine (hsum ⊤).le.trans (iSup₂_le fun S ⟨hA, _⟩ => ?_)
    by_cases hSX : S ≤ X
    · exact le_sup_of_le_left hSX
    · exact le_sup_of_le_right (hYle S hA hSX)
  ·
    intro S₁ S₂ hS₁ _ hY hX
    refine ⟨fun e => ?_⟩
    have h₁ : S₁ ≤ X := hcl S₁ S₂ hS₁ hX ⟨e⟩
    apply hS₁.1
    apply Subrepresentation.toSubmodule_injective
    rw [toSubmodule_bot, eq_bot_iff, ← hdisj]
    exact le_inf h₁ hY
  · intro T hT
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hX : X.toSubmodule ≤ X.toSubmodule.comap T := by
        refine (hsum X).le.trans (iSup₂_le fun S ⟨hA, hSX⟩ => ?_)
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hle : imRep T hT S ≤ X := hcl _ S hA' hSX ⟨e.symm⟩
          exact fun s hs => hle ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ X.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hX hv
    · have hY : Y.toSubmodule ≤ Y.toSubmodule.comap T := by
        refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hnX : ¬ imRep T hT S ≤ X := fun hle => hn (hcl S _ hA hle ⟨e⟩)
          exact fun s hs => hYle _ hA' hnX ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ Y.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hY hv
end GlobalTheory.TypeComplement
