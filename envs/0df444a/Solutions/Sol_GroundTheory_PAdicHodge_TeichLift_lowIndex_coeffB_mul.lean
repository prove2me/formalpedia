-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.lowIndex_coeffB_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:26.090849+00:00
-- url     : https://prove2.me/submissions/192b0a76-b265-4644-9167-d2fcc5e094cd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_lowIndex_zcoeff_mul
import Theorems.Thm_GroundTheory_PAdicHodge_lowIndex_shift
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_eq_zero_of_mul_pow
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hb : ConvergesAt (T.coeffB b) ρ)
    (hc : ConvergesAt (T.coeffB c) ρ) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    lowIndex (T.coeffB (b * c)) ρ = lowIndex (T.coeffB b) ρ + lowIndex (T.coeffB c) ρ := by
  obtain ⟨x, y, N, hx, hy⟩ := T.exists_common b c
  have hxy : (b * c) * algebraMap Γ T.B T.π ^ (N + N) = algebraMap Γ T.B (x * y) := by
    rw [pow_add, map_mul, ← hx, ← hy]; ring
  have hx0 : x ≠ 0 := by rintro rfl; exact hb0 (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
  have hy0 : y ≠ 0 := by rintro rfl; exact hc0 (T.eq_zero_of_mul_pow (by rw [hy, map_zero]))
  have hx0' : T.zcoeff x ≠ 0 := fun h => hx0 ((T.zcoeff_eq_zero_iff x).1 h)
  have hy0' : T.zcoeff y ≠ 0 := fun h => hy0 ((T.zcoeff_eq_zero_iff y).1 h)
  rw [T.coeffB_eq hx, convergesAt_shift_iff hρ0] at hb
  rw [T.coeffB_eq hy, convergesAt_shift_iff hρ0] at hc
  have hxy0' : T.zcoeff (x * y) ≠ 0 := by
    intro h
    have := T.gaussNorm_zcoeff_mul hρ0 hρ1 hb hc
    have h0 : gaussNorm (0 : ℤ → L) ρ = 0 := by simp [gaussNorm]
    rw [h, h0] at this
    exact (mul_pos (gaussNorm_pos hρ0 hb hx0') (gaussNorm_pos hρ0 hc hy0')).ne' this.symm
  rw [T.coeffB_eq hxy, T.coeffB_eq hx, T.coeffB_eq hy,
    lowIndex_shift hρ0 (T.convergesAt_zcoeff_mul hρ0 hρ1 hb hc) hxy0',
    lowIndex_shift hρ0 hb hx0', lowIndex_shift hρ0 hc hy0', T.lowIndex_zcoeff_mul hρ0 hρ1 hb hc hx0 hy0]
  push_cast; ring
end GroundTheory.PAdicHodge.TeichLift
