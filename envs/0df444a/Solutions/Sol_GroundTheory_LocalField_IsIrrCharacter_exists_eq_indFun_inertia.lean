-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.exists_eq_indFun_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:59.333373+00:00
-- url     : https://prove2.me/submissions/b9bde132-d253-4966-b136-129994119063

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_nat_one
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_eq_zero_of_apply_one
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_sub_of_charInner_ne_zero
import Theorems.Thm_GroundTheory_LocalField_le_inertia
import Theorems.Thm_GroundTheory_LocalField_card_conjugates_mul_card_inertia
import Theorems.Thm_GroundTheory_LocalField_charInner_comp_conjNormal
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_comp_mulEquiv
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_nat
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_charInner_comm
import Theorems.Thm_GroundTheory_LocalField_charInner_sum_irrChars
import Theorems.Thm_GroundTheory_LocalField_eq_sum_irrChars_of_isClassFun
import Theorems.Thm_GroundTheory_LocalField_indFun_apply_one
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
variable {G : Type*} [Group G] [Fintype G] {A : Subgroup G} [A.Normal]
open Classical
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsIrrCharacter χ) {θ : A → ℂ}
    (hθ : IsIrrCharacter θ) (h : charInner A (χ ∘ A.subtype) θ ≠ 0) :
    ∃ ψ : inertia A θ → ℂ, IsIrrCharacter ψ ∧ χ = indFun (inertia A θ).subtype ψ := by
  classical
  set T := inertia A θ with hT
  have hAT : A ≤ T := le_inertia A hθ.isCharacter.isClassFun
  let ι : A →* T := Subgroup.inclusion hAT
  let res : (T → ℂ) →ₗ[ℂ] (A → ℂ) := LinearMap.funLeft ℂ ℂ ι
  have hχT : IsCharacter (χ ∘ T.subtype) := hχ.isCharacter.comp _
  have hχA : χ ∘ A.subtype = res (χ ∘ T.subtype) := rfl

  obtain ⟨ψ, hψ, hne⟩ : ∃ ψ ∈ irrChars T,
      charInner T (χ ∘ T.subtype) ψ * charInner A (res ψ) θ ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [hχA, eq_sum_irrChars_of_isClassFun hχT.isClassFun] at h
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
  have hψirr := mem_irrChars.mp hψ
  have ha : charInner T (χ ∘ T.subtype) ψ ≠ 0 := left_ne_zero_of_mul hne
  have he : charInner A (res ψ) θ ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨e, he'⟩ := (hψirr.isCharacter.comp ι).exists_nat_charInner hθ.isCharacter
  change charInner A (res ψ) θ = e at he'

  have hInd : IsCharacter (indFun ι θ) := hθ.isCharacter.indFun ι
  have hIndψ : charInner T (indFun ι θ) ψ ≠ 0 := by
    rw [charInner_indFun ι θ hψirr.isCharacter.isClassFun, charInner_comm]
    exact he
  have hη := hInd.sub_of_charInner_ne_zero hψirr hIndψ
  have hIndA : res (indFun ι θ) = ((Nat.card T : ℂ) / Nat.card A) • θ := by
    funext a
    change indFun ι θ (ι a) = _
    rw [indFun_apply, Pi.smul_apply, smul_eq_mul]
    have hiff : ∀ (t : T) (b : A), ι b = t⁻¹ * ι a * t ↔ b = conjNormal A t a := by
      intro t b
      rw [Subtype.ext_iff, Subtype.ext_iff]
      simp [ι]
    simp_rw [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have ht : ∀ t : T, θ (conjNormal A t a) = θ a := fun t ↦ t.2 a
    simp_rw [ht]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    ring

  have hzero : ∀ φ ∈ irrChars A, φ ≠ θ → charInner A (res ψ) φ = 0 := by
    intro φ hφ hne
    have h1 : charInner A (res (indFun ι θ)) φ = 0 := by
      rw [hIndA, map_smul, LinearMap.smul_apply, charInner_of_isIrrCharacter hθ (mem_irrChars.mp hφ),
        if_neg (Ne.symm hne), smul_zero]
    have h2 : res (indFun ι θ) = res ψ + res (indFun ι θ - ψ) := by simp
    rw [h2, map_add, LinearMap.add_apply] at h1
    obtain ⟨m, hm⟩ := (hψirr.isCharacter.comp ι).exists_nat_charInner (mem_irrChars.mp hφ).isCharacter
    obtain ⟨k, hk⟩ := (hη.comp ι).exists_nat_charInner (mem_irrChars.mp hφ).isCharacter
    change charInner A (res ψ) φ = m at hm
    change charInner A (res (indFun ι θ - ψ)) φ = k at hk
    rw [hm, hk, ← Nat.cast_add, Nat.cast_eq_zero, Nat.add_eq_zero_iff] at h1
    rw [hm, h1.1, Nat.cast_zero]
  have hψ1 : ψ 1 = e * θ 1 := by
    have hdec := congrFun (eq_sum_irrChars_of_isClassFun (hψirr.isCharacter.comp ι).isClassFun) 1
    rw [Finset.sum_apply, Finset.sum_eq_single θ] at hdec
    · change ψ (ι 1) = _ at hdec
      rw [map_one] at hdec
      rw [hdec, Pi.smul_apply, smul_eq_mul]
      change charInner A (res ψ) θ * θ 1 = _
      rw [he']
    · intro φ hφ hne
      change (charInner A (res ψ) φ • φ) 1 = 0
      rw [hzero φ hφ hne, zero_smul, Pi.zero_apply]
    · intro hθ'
      exact absurd (mem_irrChars.mpr hθ) hθ'

  obtain ⟨f, hf⟩ := (hχ.isCharacter.comp A.subtype).exists_nat_charInner hθ.isCharacter
  have hη2 := hχT.sub_of_charInner_ne_zero hψirr ha
  obtain ⟨k2, hk2⟩ := (hη2.comp ι).exists_nat_charInner hθ.isCharacter
  change charInner A (res (χ ∘ T.subtype - ψ)) θ = k2 at hk2
  have hef : e ≤ f := by
    have h3 : charInner A (res (χ ∘ T.subtype)) θ =
        charInner A (res ψ) θ + charInner A (res (χ ∘ T.subtype - ψ)) θ := by
      rw [← LinearMap.add_apply, ← map_add, ← map_add, add_sub_cancel]
    rw [← hχA, hf, he', hk2, ← Nat.cast_add] at h3
    have := Nat.cast_injective h3
    omega

  obtain ⟨m, hm⟩ := (hχ.isCharacter.comp A.subtype).exists_nat
  have hmφ : ∀ φ ∈ irrChars A, charInner A (χ ∘ A.subtype) φ = m φ := by
    intro φ hφ
    rw [hm, charInner_sum_irrChars _ hφ]
  have hd : ∀ φ ∈ irrChars A, ∃ d : ℕ, φ 1 = d := fun φ hφ ↦
    (mem_irrChars.mp hφ).isCharacter.exists_nat_one
  choose! d hd using hd
  have hθmem : θ ∈ irrChars A := mem_irrChars.mpr hθ
  set C := Finset.univ.image fun g : G ↦ θ ∘ conjNormal A g with hC
  have hCsub : C ⊆ irrChars A := by
    intro φ hφ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hφ
    exact mem_irrChars.mpr (hθ.comp_mulEquiv _)
  have hCterm : ∀ φ ∈ C, m φ * d φ = f * d θ := by
    intro φ hφ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hφ
    have h1 : (m (θ ∘ conjNormal A g) : ℂ) = f := by
      rw [← hmφ _ (hCsub hφ), charInner_comp_conjNormal A hχ.isCharacter.isClassFun, hf]
    have h2 : (d (θ ∘ conjNormal A g) : ℂ) = d θ := by
      rw [← hd _ (hCsub hφ), ← hd _ hθmem, Function.comp_apply, map_one]
    rw [Nat.cast_injective h1, Nat.cast_injective h2]
  have hχ1 : χ 1 = ((∑ φ ∈ irrChars A, m φ * d φ : ℕ) : ℂ) := by
    have := congrFun hm 1
    rw [Finset.sum_apply] at this
    change χ 1 = _ at this
    rw [this]
    push_cast
    refine Finset.sum_congr rfl fun φ hφ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, hd φ hφ]
  have hbound : C.card * f * d θ ≤ ∑ φ ∈ irrChars A, m φ * d φ := by
    calc C.card * f * d θ = ∑ φ ∈ C, m φ * d φ := by
          rw [Finset.sum_congr rfl hCterm, Finset.sum_const, smul_eq_mul, mul_assoc]
      _ ≤ ∑ φ ∈ irrChars A, m φ * d φ := Finset.sum_le_sum_of_subset hCsub

  have hcard := card_conjugates_mul_card_inertia A θ
  have hψG : IsCharacter (indFun T.subtype ψ) := hψirr.isCharacter.indFun _
  have hne3 : charInner G (indFun T.subtype ψ) χ ≠ 0 := by
    rw [charInner_indFun _ _ hχ.isCharacter.isClassFun, charInner_comm]
    exact ha
  have hη3 := hψG.sub_of_charInner_ne_zero hχ hne3
  obtain ⟨k3, hk3⟩ := hη3.exists_nat_one
  have hT0 : (Nat.card T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdeg : indFun T.subtype ψ 1 = ((C.card * e * d θ : ℕ) : ℂ) := by
    rw [indFun_apply_one _ T.subtype_injective, hψ1, hd θ hθmem, ← hcard, ← hC, ← hT]
    push_cast
    field_simp
  have hk0 : k3 = 0 := by
    rw [Pi.sub_apply, hdeg, hχ1, sub_eq_iff_eq_add, ← Nat.cast_add] at hk3
    have h4 := Nat.cast_injective hk3
    have h5 : C.card * e * d θ ≤ C.card * f * d θ := by gcongr
    omega
  refine ⟨ψ, hψirr, ?_⟩
  have h6 := hη3.eq_zero_of_apply_one (by rw [hk3, hk0, Nat.cast_zero])
  exact (sub_eq_zero.mp h6).symm
end IsIrrCharacter
end GroundTheory.LocalField
