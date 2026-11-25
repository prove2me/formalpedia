-- Prove2me | solution 1 for GlobalTheory.HTLat.eigSubLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:13.943805+00:00
-- url     : https://prove2.me/submissions/5a854c53-5611-4dd0-b32b-d6678f6c0fa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V)
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : IsSplitting σ)
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V)
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : _root_.GlobalTheory.EigenSplit.IsSplitting σ)
namespace GlobalTheory.HTLat
namespace _root_.GlobalTheory.HTLat
theorem _root_.solution (χ : Λ →+* C) {X Y : Submodule O V} (hXY : X ≤ Y) :
    _root_.GlobalTheory.HTLat.eigSubLat ρ χ X ≤ _root_.GlobalTheory.HTLat.eigSubLat ρ χ Y :=
  inf_le_inf_right _ hXY
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
