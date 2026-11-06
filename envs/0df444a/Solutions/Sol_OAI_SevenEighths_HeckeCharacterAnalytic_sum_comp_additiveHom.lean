-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.sum_comp_additiveHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:01.722211+00:00
-- url     : https://prove2.me/submissions/cc6b1c58-fcba-4c24-9f91-9bf901a25c5f

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeCoordinates_coordinateQuotientHom_intCast
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeCoordinates.coordinateQuotientHom_intCast
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (π : A →+ B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ a, f (π a)) = (Nat.card π.ker : ℂ) * ∑ b, f b := by
  classical
  let : Fintype π.ker := Fintype.ofFinite _
  have hid (a : A) : f (π a) = (fun p : B × π.ker => f p.1) (additiveFiberEquiv π hπ a) := rfl
  simp_rw [hid]
  rw [(additiveFiberEquiv π hπ).bijective.sum_comp (fun p : B × π.ker => f p.1)]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]
end OAI.SevenEighths.HeckeCharacterAnalytic
