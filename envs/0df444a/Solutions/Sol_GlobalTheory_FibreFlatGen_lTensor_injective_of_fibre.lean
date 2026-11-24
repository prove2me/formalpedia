-- Prove2me | solution 1 for GlobalTheory.FibreFlatGen.lTensor_injective_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:54.019571+00:00
-- url     : https://prove2.me/submissions/84a84216-a38e-42a9-839a-7c0e879381d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RTensorInjectiveOfFlatBaseChange
import Theorems.Thm_GlobalTheory_FibreFlatGen_rTensor_injective_of_flat_baseChange
import Theorems.Thm_GlobalTheory_FibreFlatGen_rTensor_injective_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory GlobalTheory.FibreFlatGen
open LocalFlat
universe u
namespace GlobalTheory.FibreFlatGen
theorem _root_.solution {A B A' L C N' N : Type} [CommRing A] [CommRing B] [CommRing A']
    [CommRing L] [CommRing C] [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [Algebra A A'] (S : Submonoid A) [IsLocalization S A'] [Algebra A' L] [IsScalarTower A A' L]
    [Algebra A' C] [Algebra A C] [IsScalarTower A A' C]
    [Module.Flat B L] [Module.Flat C (C ⊗[A] B)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A' N'] [Module A' N]
    [IsScalarTower A' C N'] [IsScalarTower A' C N] (ι : N' →ₗ[C] N) (hι : Function.Injective ι) :
    Function.Injective ((ι.restrictScalars A').lTensor L) := by
  letI : Module A N' := Module.compHom N' (algebraMap A A')
  letI : Module A N := Module.compHom N (algebraMap A A')
  haveI t₁ : IsScalarTower A A' N' := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [Algebra.smul_def, mul_smul]⟩
  haveI t₂ : IsScalarTower A A' N := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [Algebra.smul_def, mul_smul]⟩
  haveI t₃ : IsScalarTower A C N' := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [← smul_assoc, algebraMap_smul]⟩
  haveI t₄ : IsScalarTower A C N := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [← smul_assoc, algebraMap_smul]⟩
  have s₁ := rTensor_injective_of_flat_baseChange (A := A) (C := C) (B := B) ι hι
  have s₂ := rTensor_injective_of_flat (A := A) (B := B) (L := L) (ι.restrictScalars A) s₁
  haveI c₁ := IsLocalization.tensorProduct_compatibleSMul S A' L N'
  haveI c₂ := IsLocalization.tensorProduct_compatibleSMul S A' L N
  let e' := TensorProduct.equivOfCompatibleSMul A A' A' L N'
  let e := TensorProduct.equivOfCompatibleSMul A A' A' L N
  have key : ∀ z, e ((ι.restrictScalars A').lTensor L z) =
      (ι.restrictScalars A).lTensor L (e' z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul l n => rfl
  intro x y h
  apply e'.injective
  apply s₂
  rw [← key, ← key, h]
end GlobalTheory.FibreFlatGen
