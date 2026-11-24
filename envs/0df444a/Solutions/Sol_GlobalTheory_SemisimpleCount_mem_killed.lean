-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.mem_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:45.738094+00:00
-- url     : https://prove2.me/submissions/3a40636c-911a-4297-9408-40fd3b215667

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
theorem _root_.solution {m : M} : m ∈ killed I M ↔ ∀ x ∈ I, x • m = 0 := Iff.rfl
end GlobalTheory.SemisimpleCount
