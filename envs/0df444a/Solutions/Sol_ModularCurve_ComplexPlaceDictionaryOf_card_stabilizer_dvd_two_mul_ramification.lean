-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.card_stabilizer_dvd_two_mul_ramification
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e735707d-1ffa-5548-8e5b-a7b4d0a6d24c

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification.ModularCurve"
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf realizeOf_of_not ComplexPlaceDictionaryOf laurentBaseChange realizeOf_eq_div"
namespace ComplexPlaceDictionaryOf
p2m_export "ModularCurve.ComplexPlaceDictionaryOf" "ramification meromorphicOrderAt_realizeOf pt"
namespace CardStabilizerDvd
p2m_open "ModularCurve.ComplexPlaceDictionaryOf ModularCurve"

theorem realizeOf_smul (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    realizeOf Γ x (γ • τ) = realizeOf Γ x τ := by
  classical
  have key : ∀ {k : ℤ} (h : ModularForm Γ k),
      (h : ℍ → ℂ) (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * h τ := fun h =>
    SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
  by_cases H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
  · obtain ⟨⟨k, g, h⟩, hne, heq⟩ := H
    have hd : (denom (γ : GL (Fin 2) ℝ) τ : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
    have hne' : (h : ℍ → ℂ) (γ • τ) ≠ 0 := by rw [key h]; exact mul_ne_zero hd hne
    rw [realizeOf_eq_div Γ hT g h x heq _ hne', realizeOf_eq_div Γ hT g h x heq _ hne, key g, key h,
      mul_div_mul_left _ _ hd]
  · have H' : ¬ ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) (γ • τ) ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rintro ⟨⟨k, g, h⟩, hne, heq⟩
      refine H ⟨⟨k, g, h⟩, ?_, heq⟩
      intro h0
      apply hne
      show (h : ℍ → ℂ) (γ • τ) = 0
      rw [key h, show (h : ℍ → ℂ) τ = 0 from h0, mul_zero]
    rw [realizeOf_of_not Γ x _ H, realizeOf_of_not Γ x _ H']

theorem realizeOf_neg_one_smul (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf Γ x ((-1 : SL(2, ℤ)) • τ) = realizeOf Γ x τ := by
  rw [ModularGroup.SL_neg_smul, one_smul]

def invariantSubgroup (F : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | ∀ τ : ℍ, F (γ • τ) = F τ}
  mul_mem' := by
    intro a b ha hb τ
    rw [mul_smul, ha, hb]
  one_mem' := by
    intro τ
    rw [one_smul]
  inv_mem' := by
    intro a ha τ
    rw [← ha (a⁻¹ • τ), smul_inv_smul]

theorem mem_invariantSubgroup_iff (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    γ ∈ invariantSubgroup F ↔ ∀ τ : ℍ, F (γ • τ) = F τ :=
  Iff.rfl

theorem sup_le_invariantSubgroup (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (x : LaurentSeries ℂ) :
    Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ invariantSubgroup (realizeOf Γ x) := by
  refine sup_le ?_ ?_
  · intro γ hγ
    rw [mem_invariantSubgroup_iff]
    intro τ
    exact realizeOf_smul Γ hT x hγ τ
  · rw [Subgroup.zpowers_le, mem_invariantSubgroup_iff]
    intro τ
    exact realizeOf_neg_one_smul Γ x τ

theorem realizeOf_smul_of_mem_sup (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (x : LaurentSeries ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (τ : ℍ) :
    realizeOf Γ x (γ • τ) = realizeOf Γ x τ :=
  (mem_invariantSubgroup_iff _ _).mp (sup_le_invariantSubgroup Γ hT x hγ) τ

variable {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem exists_ord_eq_one (D : ComplexPlaceDictionaryOf Γ F₀) (τ : ℍ) :
    ∃ x : laurentBaseChange ℂ F₀, x ≠ 0 ∧ (D.pt τ).ord x = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (D.pt τ).toValuationSubring
  refine ⟨π, ?_, (D.pt τ).ord_coe_irreducible hπ⟩
  intro h
  apply hπ.ne_zero
  exact_mod_cast h

theorem card_dvd_two_mul_ram (hT : ModularGroup.T ∈ Γ) (D : ComplexPlaceDictionaryOf Γ F₀) (τ : ℍ) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) ∣
      2 * D.ramification τ := by
  obtain ⟨x, hx, hord⟩ := exists_ord_eq_one D τ
  have h := D.meromorphicOrderAt_realizeOf τ x hx
  rw [hord, mul_one] at h
  have := UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (fun z => realizeOf Γ (x : LaurentSeries ℂ) z)
    (fun γ hγ z => realizeOf_smul_of_mem_sup Γ hT (x : LaurentSeries ℂ) hγ z) τ _ h
  exact_mod_cast this

end ModularCurve.ComplexPlaceDictionaryOf.CardStabilizerDvd

end

open scoped MatrixGroups in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (τ : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) ∣
      2 * D.ramification τ :=
  ModularCurve.ComplexPlaceDictionaryOf.CardStabilizerDvd.card_dvd_two_mul_ram hT D τ

end S_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification (solution)
