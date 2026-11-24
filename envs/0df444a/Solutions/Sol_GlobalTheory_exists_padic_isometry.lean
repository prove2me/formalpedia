-- Prove2me | solution 1 for GlobalTheory.exists_padic_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:41.396833+00:00
-- url     : https://prove2.me/submissions/740b5250-b69f-4898-a50b-94bbe71ee46d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_norm_ratCast_eq_padicNorm

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
theorem _root_.solution {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
    [CompleteSpace C] (p : ℕ) [Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) :
    ∃ j : ℚ_[p] →+* C, ∀ x, ‖j x‖ = ‖x‖ := by
  let w : AbsoluteValue ℚ ℝ := Rat.AbsoluteValue.padic p
  let i : WithAbs w →+* ℚ_[p] := (Rat.castHom ℚ_[p]).comp (WithAbs.equiv w).toRingHom
  let f : WithAbs w →+* C := (Rat.castHom C).comp (WithAbs.equiv w).toRingHom
  have hi : ∀ x, ‖i x‖ = ‖x‖ := fun x => Padic.eq_padicNorm _
  have hf : ∀ x, ‖f x‖ = ‖x‖ := fun x => (norm_ratCast_eq_padicNorm p h _).trans (hi x)
  have hi' : Isometry i := AddMonoidHomClass.isometry_of_norm i hi
  have hf' : Isometry f := AddMonoidHomClass.isometry_of_norm f hf
  have hd : DenseRange i :=
    (Padic.denseRange_ratCast p).mono (by
      rintro _ ⟨q, rfl⟩
      exact ⟨WithAbs.toAbs w q, rfl⟩)
  let j : ℚ_[p] →+* C :=
    IsDenseInducing.extendRingHom hi'.isUniformInducing hd hf'.uniformContinuous
  have hjc : Continuous j :=
    (uniformContinuous_uniformly_extend hi'.isUniformInducing hd hf'.uniformContinuous).continuous
  refine ⟨j, fun x => ?_⟩
  refine hd.induction_on x (isClosed_eq hjc.norm continuous_norm) fun q => ?_
  have : j (i q) = f q :=
    IsDenseInducing.extend_eq (hi'.isUniformInducing.isDenseInducing hd) hf'.continuous q
  rw [this, hf, hi]
end GlobalTheory
