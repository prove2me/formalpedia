-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_hom_congr_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:41.253043+00:00
-- url     : https://prove2.me/submissions/25e6bd8c-823d-4db8-b2d0-c442029c926e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
variable {S : Type} [AddCommGroup S] [Module Rg S]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution {S' : Type} [AddCommGroup S'] [Module Rg S'] (e : S ≃ₗ[Rg] S') :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S' →ₗ[Rg] M) :=
  LinearEquiv.rank_eq
    { toFun := fun g => g.comp e.symm.toLinearMap
      invFun := fun g => g.comp e.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }
end GlobalTheory.SemisimpleCount
