-- Prove2me | solution 1 for GlobalTheory.UnitaryChart.eq_of_skew_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:25.616072+00:00
-- url     : https://prove2.me/submissions/bd63e01c-8071-4c7e-ad86-28833bb0af14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter
namespace GlobalTheory.UnitaryChart
theorem _root_.solution {E : Type} [NormedRing E] [NormedAlgebra ℝ E] {u v u' v' : E}
    (hu : u' * u = 1) (hv : v * v' = 1)
    (h : u - u' = v - v') (nu : ‖1 - u'‖ ≤ 1 / 2) (nv : ‖1 - v'‖ ≤ 1 / 2) : u = v := by
  set w := u - v with hw
  have e1 : w = u' - v' := by
    rw [hw]; exact sub_eq_sub_iff_sub_eq_sub.mp h
  have e2 : u' * w * v' = v' - u' := by
    calc u' * w * v' = (u' * u) * v' - u' * (v * v') := by rw [hw]; noncomm_ring
      _ = v' - u' := by rw [hu, hv, one_mul, mul_one]
  have e3 : (2 : ℝ) • w = (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') := by
    have : (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') = w - u' * w * v' := by
      noncomm_ring
    rw [this, e2, two_smul]
    nth_rewrite 2 [e1]
    abel
  have n0 := norm_nonneg w
  have n1 : ‖(1 - u') * w‖ ≤ 1 / 2 * ‖w‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right nu n0)
  have n2 : ‖w * (1 - v')‖ ≤ ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left nv n0)
  have n3 : ‖(1 - u') * w * (1 - v')‖ ≤ 1 / 2 * ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul n1 nv (norm_nonneg _) (by positivity))
  have n4 : 2 * ‖w‖ ≤ ‖(1 - u') * w‖ + ‖w * (1 - v')‖ + ‖(1 - u') * w * (1 - v')‖ := by
    have : ‖(2 : ℝ) • w‖ = 2 * ‖w‖ := by rw [norm_smul]; simp
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖w‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)
end GlobalTheory.UnitaryChart
