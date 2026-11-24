-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.injective_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:45.493608+00:00
-- url     : https://prove2.me/submissions/5bba1646-f8ec-4ba9-9dc4-17438fc621b7

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
theorem _root_.solution {A : Type} [AddCommGroup A] [Module Rg A] [IsSimpleModule Rg S]
    {f : S →ₗ[Rg] A} (hf : f ≠ 0) : Function.Injective f :=
  (LinearMap.injective_or_eq_zero f).resolve_right hf
end GlobalTheory.SemisimpleCount
