-- Prove2me | solution 1 for GroundTheory.LocalField.exists_eq_indFun_of_isNilpotent_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:22:18.11651+00:00
-- url     : https://prove2.me/submissions/1cba9c34-1919-46d4-8883-83a89a8d72a2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
import Theorems.Thm_GroundTheory_LocalField_exists_normal_commute_of_not_commute
import Theorems.Thm_GroundTheory_LocalField_apply_eq_smul_of_forall_conj
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_eq_indFun_inertia
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_charInner_character_character
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_isClassFun_of_charInner
import Theorems.Thm_GroundTheory_LocalField_exists_hom_of_isIrreducible_of_commute
import Theorems.Thm_GroundTheory_LocalField_indFun_subtype_indFun_subtype
import Theorems.Thm_GroundTheory_LocalField_indFun_top_hom
import Theorems.Thm_GroundTheory_LocalField_isCharacter_character
import Theorems.Thm_GroundTheory_LocalField_isIrrCharacter_character
import Theorems.Thm_GroundTheory_LocalField_isIrrCharacter_hom
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
universe u
open Classical
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℕ) :
    ∀ (G : Type u) [Group G] [Fintype G] [Group.IsNilpotent G], Nat.card G = n →
      ∀ {χ : G → ℂ}, IsIrrCharacter χ →
        ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ hn χ hχ
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hχ

  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · obtain ⟨l, hl⟩ := exists_hom_of_isIrreducible_of_commute ρ hc
    exact ⟨⊤, l.comp (⊤ : Subgroup G).subtype, by rw [hl, indFun_top_hom]⟩
  push Not at hc
  obtain ⟨A, hAn, hAc, a₀, ha₀, g₀, hg₀⟩ := exists_normal_commute_of_not_commute ρ hc

  have hχA : IsCharacter (ρ.character ∘ A.subtype) := (isCharacter_character ρ).comp _
  have hne0 : ρ.character ∘ A.subtype ≠ 0 := fun h0 ↦
    (isIrrCharacter_character ρ).one_ne_zero (by simpa using congrFun h0 1)
  obtain ⟨φ, hφ, hφne⟩ : ∃ φ ∈ irrChars A, charInner A (ρ.character ∘ A.subtype) φ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne0 (eq_zero_of_isClassFun_of_charInner hχA.isClassFun hcon)
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := mem_irrChars.mp hφ

  have hrank : finrank ℂ (IntertwiningMap σ (ρ.comp A.subtype)) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character]
    exact hφne
  have : Nontrivial (IntertwiningMap σ (ρ.comp A.subtype)) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)
  obtain ⟨F, hF⟩ := exists_ne (0 : IntertwiningMap σ (ρ.comp A.subtype))
  have hFinj : Function.Injective F := (IsIrreducible.injective_or_eq_zero F).resolve_right hF
  have hσc : ∀ a b : A, σ a * σ b = σ b * σ a := by
    intro a b
    apply LinearMap.ext
    intro w
    apply hFinj
    change F (σ a (σ b w)) = F (σ b (σ a w))
    rw [IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F,
      IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F]
    change (ρ a * ρ b) (F w) = (ρ b * ρ a) (F w)
    rw [hAc a a.2 b b.2]
  obtain ⟨l, hl⟩ := exists_hom_of_isIrreducible_of_commute σ hσc
  rw [hl] at hφne
  by_cases hT : inertia A (fun a ↦ (l a : ℂ)) = ⊤
  ·
    exfalso
    have hlinv : ∀ (g : G) (a : A), l (conjNormal A g a) = l a := by
      intro g a
      have hg : g ∈ inertia A (fun a ↦ (l a : ℂ)) := hT ▸ Subgroup.mem_top g
      exact Units.ext (hg a)
    apply hg₀
    apply LinearMap.ext
    intro v
    change ρ g₀ (ρ ((⟨a₀, ha₀⟩ : A) : G) v) = ρ ((⟨a₀, ha₀⟩ : A) : G) (ρ g₀ v)
    rw [apply_eq_smul_of_forall_conj ρ l hφne hlinv, apply_eq_smul_of_forall_conj ρ l hφne hlinv,
      map_smul]
  ·
    obtain ⟨ψ, hψ, hχψ⟩ :=
      (isIrrCharacter_character ρ).exists_eq_indFun_inertia (isIrrCharacter_hom l) hφne
    set T := inertia A (fun a ↦ (l a : ℂ))
    have hlt : Nat.card T < n := hn ▸ lt_of_le_of_ne (Subgroup.card_le_card_group T)
      fun h ↦ hT ((Subgroup.card_eq_iff_eq_top T).mp h)
    obtain ⟨K, l', hK⟩ := ih (Nat.card T) hlt T rfl hψ
    refine ⟨K.map T.subtype,
      l'.comp (K.equivMapOfInjective T.subtype T.subtype_injective).symm.toMonoidHom, ?_⟩
    rw [hχψ, hK, indFun_subtype_indFun_subtype]
    rfl
end GroundTheory.LocalField
