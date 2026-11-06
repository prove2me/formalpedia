-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.inflate_factorsThrough
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:47.053205+00:00
-- url     : https://prove2.me/submissions/c3dcdef4-9381-4368-b7f1-36114b1846a8

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_apply_unit
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorsThroughIdeal_iff
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
theorem _root_.solution {M L : Ideal A} [Finite (A ⧸ M)]
    (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    FactorsThroughIdeal (inflate hML χ) (L.map (Ideal.Quotient.mk M)) := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have haL : a - 1 ∈ L := by
    apply (Ideal.mem_quotient_iff_mem hML).mp
    simpa only [map_sub, map_one, ha] using hu
  have ha1 : Ideal.Quotient.mk L a = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr haL
  rw [inflate_apply_unit, ← ha, Ideal.Quotient.factor_mk, ha1, map_one]
end OAI.SevenEighths.ResidueCharacter
