-- Prove2me | solution 1 for GlobalTheory.exists_isLocalHom_normIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:33.428099+00:00
-- url     : https://prove2.me/submissions/ee9948f0-cb47-4678-bffd-e53f5a9ed431

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_mem_normIntegers_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {V K C : Type*} [CommRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [NormedField C] [IsUltrametricDist C] [Algebra K C]
    (h : ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) :
    ∃ φ : V →+* normIntegers C, IsLocalHom φ ∧
      ∀ a, (φ a : C) = algebraMap K C (algebraMap V K a) := by
  let φ : V →+* normIntegers C :=
    ((algebraMap K C).comp (algebraMap V K)).codRestrict (normIntegers C) fun a =>
      mem_normIntegers_iff.2 ((h _).2 ⟨a, rfl⟩)
  refine ⟨φ, ⟨fun a ha => ?_⟩, fun _ => rfl⟩
  have h1 : ‖algebraMap K C (algebraMap V K a)‖ = 1 :=
    (NormIntegers.isUnit_iff_norm_eq_one (normIntegers_integers C)).1 ha
  have h0 : algebraMap V K a ≠ 0 := fun h0 => by simp [h0] at h1
  obtain ⟨b, hb⟩ := (h (algebraMap V K a)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective V K ?_)
  rw [map_mul, hb, mul_inv_cancel₀ h0, map_one]
end GlobalTheory
