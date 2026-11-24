-- Prove2me | solution 1 for GlobalTheory.EigenSplit.IsEquivariant.eigenMap_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:57.661004+00:00
-- url     : https://prove2.me/submissions/a2797d7c-150e-48cf-add5-eee33e49aa8f

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
theorem _root_.solution {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''}
    (hf : IsEquivariant ρ ρ' f) (hg : IsEquivariant ρ' ρ'' g) (i : ι)
    (he : Function.Exact f g) :
    Function.Exact (hf.eigenMap (σ i)) (hg.eigenMap (σ i)) := by
  classical
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (he y).1 (congrArg Subtype.val hy)
    exact ⟨projTo h ρ i x, Subtype.ext (by simp [hf.proj h, hx, proj_of_mem h y.2])⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((he _).2 ⟨x, rfl⟩)
end IsEquivariant
end GlobalTheory.EigenSplit
