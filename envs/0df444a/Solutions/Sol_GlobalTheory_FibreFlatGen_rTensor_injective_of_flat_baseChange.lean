-- Prove2me | solution 1 for GlobalTheory.FibreFlatGen.rTensor_injective_of_flat_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:20.554393+00:00
-- url     : https://prove2.me/submissions/141018ad-d891-4bb7-9c4a-9a245bed2fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RTensorInjectiveOfFlatBaseChange

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
theorem _root_.solution {A C B N' N : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup B] [Module A B] [Module.Flat C (C ⊗[A] B)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Function.Injective ι) :
    Function.Injective ((ι.restrictScalars A).rTensor B) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C N' B
  let e := AlgebraTensorModule.cancelBaseChange A C C N B
  have h1 : Function.Injective (ι.rTensor (C ⊗[A] B)) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have key : ∀ z, (ι.restrictScalars A).rTensor B (e' z) = e (ι.rTensor (C ⊗[A] B) z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul n t =>
      induction t with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]
end GlobalTheory.FibreFlatGen
