-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.map_mem_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:54.578703+00:00
-- url     : https://prove2.me/submissions/daf09697-19f2-46bf-8526-d6578d0ab1ed

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
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution {A B : Type} [AddCommGroup A] [Module Rg A] [AddCommGroup B] [Module Rg B]
    (f : A →ₗ[Rg] B) {a : A} (ha : ∀ x ∈ I, x • a = 0) : ∀ x ∈ I, x • f a = 0 := by
  intro x hx
  rw [← map_smul, ha x hx, map_zero]
end GlobalTheory.SemisimpleCount
