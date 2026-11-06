-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.isUnit_mk_inf_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:12.54541+00:00
-- url     : https://prove2.me/submissions/422c2f71-a6cf-4032-842a-a4cdb3fe3691

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm
attribute [local simp] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ResidueCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.ResidueCharacter
theorem _root_.solution (I J : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk (I ⊓ J) a) ↔
      IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a) := by
  constructor
  · intro h
    constructor
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left)))
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right)))
  · rintro ⟨hI, hJ⟩
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hI
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hJ
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hbI : a * b - 1 ∈ I :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    have hcJ : a * c - 1 ∈ J :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hc)
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (I ⊓ J) (b + c - a * b * c), ?_⟩
    rw [← map_mul]
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
    have hid : a * (b + c - a * b * c) - 1 = -((a * b - 1) * (a * c - 1)) := by ring
    rw [hid]
    exact ⟨I.neg_mem (I.mul_mem_right _ hbI), J.neg_mem (J.mul_mem_left _ hcJ)⟩
end OAI.SevenEighths.ResidueCharacter
