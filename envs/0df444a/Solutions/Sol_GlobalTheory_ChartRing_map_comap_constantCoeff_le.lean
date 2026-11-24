-- Prove2me | solution 1 for GlobalTheory.ChartRing.map_comap_constantCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:14.927858+00:00
-- url     : https://prove2.me/submissions/f719f16b-23f7-4727-b5ee-078e290d3123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace GlobalTheory.ChartRing
theorem _root_.solution {S : Type*} [CommRing S] [Algebra A S] (J : Ideal S)
    (φ : A⟦X⟧ →ₐ[A] S) (hI : I.map (algebraMap A S) ≤ J) (hX : φ X ∈ J) :
    (I.comap (constantCoeff (R := A))).map φ ≤ J := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, f.eq_X_mul_shift_add_const, map_add, map_mul]
  refine add_mem (Ideal.mul_mem_right _ _ hX) ?_
  have : φ (C (constantCoeff f)) = algebraMap A S (constantCoeff f) := φ.commutes _
  rw [this]
  exact hI (Ideal.mem_map_of_mem _ hf)
end GlobalTheory.ChartRing
