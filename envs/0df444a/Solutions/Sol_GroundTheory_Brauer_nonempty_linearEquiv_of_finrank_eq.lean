-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_linearEquiv_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:13.595524+00:00
-- url     : https://prove2.me/submissions/68092cf3-6e8e-4884-bc18-03b4ebab9fb6

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
namespace GroundTheory.Brauer
theorem _root_.solution {K R : Type*} {M N : Type*} [Field K] [Ring R]
    [Algebra K R] [IsSimpleRing R] [FiniteDimensional K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M] [FiniteDimensional K M]
    [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N] [FiniteDimensional K N]
    (h : Module.finrank K M = Module.finrank K N) : Nonempty (M ≃ₗ[R] N) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  rcases subsingleton_or_nontrivial (M × N) with hMN | hMN
  · have : Subsingleton M := (Prod.fst_surjective (β := N)).subsingleton
    have : Subsingleton N := (Prod.snd_surjective (α := M)).subsingleton
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  have : Module.Finite R (M × N) := Module.Finite.of_restrictScalars_finite K R _
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R _
  have : Module.Finite R N := Module.Finite.of_restrictScalars_finite K R _
  obtain ⟨k, _, S, hS, -⟩ := (IsSimpleRing.isIsotypic R (M × N)).linearEquiv_fun
  have hT : IsIsotypicOfType R (M × N) S := IsSimpleRing.isIsotypic R (M × N) S
  obtain ⟨m, ⟨eM⟩⟩ := (hT.of_injective (LinearMap.inl R M N) LinearMap.inl_injective).linearEquiv_fun
  obtain ⟨n, ⟨eN⟩⟩ := (hT.of_injective (LinearMap.inr R M N) LinearMap.inr_injective).linearEquiv_fun
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  have : FiniteDimensional K S :=
    FiniteDimensional.of_injective ((Submodule.subtype S).restrictScalars K) Subtype.val_injective
  have hS0 : 0 < Module.finrank K S := Module.finrank_pos
  have hm : Module.finrank K M = m * Module.finrank K S := by
    rw [(eM.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]; simp
  have hn : Module.finrank K N = n * Module.finrank K S := by
    rw [(eN.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]; simp
  obtain rfl : m = n := Nat.eq_of_mul_eq_mul_right hS0 (hm.symm.trans (h.trans hn))
  exact ⟨eM.trans eN.symm⟩
end GroundTheory.Brauer
