-- Prove2me | solution 1 for GlobalTheory.HTLat.eigSubLat_le_eigQuotLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:48.07606+00:00
-- url     : https://prove2.me/submissions/ca636528-8aca-49c1-88b9-ba6921e74798

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
theorem _root_.solution (i : ι) (X : Submodule O V) :
    _root_.GlobalTheory.HTLat.eigSubLat ρ (σ i) X ≤ _root_.GlobalTheory.HTLat.eigQuotLat ρ h i X := by
  intro x hx
  exact ⟨x, hx.1, _root_.GlobalTheory.EigenSplit.proj_of_mem h hx.2⟩
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
