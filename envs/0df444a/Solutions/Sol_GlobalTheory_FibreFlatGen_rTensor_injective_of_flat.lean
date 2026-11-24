-- Prove2me | solution 1 for GlobalTheory.FibreFlatGen.rTensor_injective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:17.866345+00:00
-- url     : https://prove2.me/submissions/3f116959-859f-48dd-b194-1bf70d331b54

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
theorem _root_.solution {A B L N' N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L] [Module.Flat B L]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Function.Injective (ι.rTensor B)) : Function.Injective (ι.lTensor L) := by
  let e' := AlgebraTensorModule.cancelBaseChange A B B L N'
  let e := AlgebraTensorModule.cancelBaseChange A B B L N
  have hι' : Function.Injective (ι.baseChange B) := by
    have := (LinearMap.lTensor_inj_iff_rTensor_inj (M := B) ι).mpr hι
    exact this
  have h1 : Function.Injective ((ι.baseChange B).lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have key : ∀ z, ι.lTensor L (e' z) = e ((ι.baseChange B).lTensor L z) := by
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
