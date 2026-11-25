-- Prove2me | solution 1 for GlobalTheory.HTLat.map_eigQuotLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:45:30.941258+00:00
-- url     : https://prove2.me/submissions/e176588a-7ef6-49c9-bcf7-29fa2f54ac1a

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
theorem _root_.solution {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V'] [IsScalarTower O C V']
    {ρ' : Λ →+* Module.End C V'} {f : V →ₗ[C] V'} (hf : IsEquivariant ρ ρ' f) (i : ι)
    (X : Submodule O V) :
    (eigQuotLat ρ h i X).map (f.restrictScalars O) =
      eigQuotLat ρ' h i (X.map (f.restrictScalars O)) := by
  rw [eigQuotLat, eigQuotLat, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  exact hf.proj h i x
end GlobalTheory.HTLat
