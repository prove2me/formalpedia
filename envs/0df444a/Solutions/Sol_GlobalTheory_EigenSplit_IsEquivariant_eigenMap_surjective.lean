-- Prove2me | solution 1 for GlobalTheory.EigenSplit.IsEquivariant.eigenMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:41:32.171822+00:00
-- url     : https://prove2.me/submissions/7bd66ee7-e958-401d-8df1-2bff09f6389e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']
variable {σ : ι → O →+* R} (h : IsSplitting σ) {ρ : O →+* Module.End R N}
  {ρ' : O →+* Module.End R N'} {ρ'' : O →+* Module.End R N''}
include h
namespace GlobalTheory.EigenSplit
namespace IsEquivariant
theorem _root_.solution {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (i : ι)
    (hs : Function.Surjective f) : Function.Surjective (hf.eigenMap (σ i)) := by
  classical
  intro y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨projTo h ρ i x, Subtype.ext (by simp [hf.proj h, hx, proj_of_mem h y.2])⟩
end IsEquivariant
end GlobalTheory.EigenSplit
