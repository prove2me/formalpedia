-- Prove2me | solution 1 for GlobalTheory.HTLat.mem_eigSubLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:45:44.593198+00:00
-- url     : https://prove2.me/submissions/99baa8ee-aef5-4e4a-b6ae-a84e81fa9f91

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
namespace GlobalTheory.HTLat
theorem _root_.solution {χ : Λ →+* C} {X : Submodule O V} {x : V} :
    x ∈ eigSubLat ρ χ X ↔ x ∈ X ∧ x ∈ eigenSub ρ χ := Iff.rfl
end GlobalTheory.HTLat
