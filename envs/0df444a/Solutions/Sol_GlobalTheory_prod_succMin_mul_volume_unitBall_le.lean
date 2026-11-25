-- Prove2me | solution 1 for GlobalTheory.prod_succMin_mul_volume_unitBall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:59.811562+00:00
-- url     : https://prove2.me/submissions/38140cb8-e16c-4689-900a-2d69e1a4a7c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_measure_le_two_pow_mul_covolume
import Theorems.Thm_GlobalTheory_exists_linearMap_det_eq_prod_inv_succMin
import Theorems.Thm_GlobalTheory_spanCovol_bot
import Theorems.Thm_GlobalTheory_succMin_pos_of_isZLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution :
    (∏ i : Fin (finrank ℝ E), succMin L (i + 1)) * volume.real (Metric.ball (0 : E) 1) ≤
      2 ^ finrank ℝ E * ZLattice.covolume L := by
  obtain ⟨T, hdet, hT⟩ := exists_linearMap_det_eq_prod_inv_succMin L
  have hP : 0 < ∏ i : Fin (finrank ℝ E), succMin L (i + 1) :=
    Finset.prod_pos fun i _ ↦ succMin_pos_of_isZLattice (by omega) i.2
  have h := measure_le_two_pow_mul_covolume L volume (s := T ⁻¹' Metric.ball 0 1)
    (fun x hx ↦ by simpa using hx) ((convex_ball 0 1).linear_preimage T)
    (fun x hx h0 hs ↦ (hT x hx h0).not_gt (mem_ball_zero_iff.1 hs))
  have hc := ZLattice.covolume_pos L volume
  rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; positivity), hdet, inv_inv,
    abs_of_pos hP, ← ofReal_measureReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul hP.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h
end GlobalTheory
