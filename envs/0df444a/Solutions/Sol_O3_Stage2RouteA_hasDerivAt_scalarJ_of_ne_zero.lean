-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_scalarJ_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:24.986936+00:00
-- url     : https://prove2.me/submissions/4cfe97a2-a42a-4b25-957c-eab797e01387

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (O3.Experimental.scalarJ p) ((p - 1) * |u| ^ (p - 2)) u := by
  have ha := hasDerivAt_abs hu
  have hap := ha.rpow_const (Or.inl (abs_pos.mpr hu).ne') (p := p - 2)
  have hm := hap.mul (hasDerivAt_id u)
  have hid :
      (↑(SignType.sign u) : ℝ) * (p - 2) * |u| ^ (p - 2 - 1) * u +
          |u| ^ (p - 2) * 1 = (p - 1) * |u| ^ (p - 2) := by
    rcases lt_or_gt_of_ne hu with huNeg | huPos
    · have hsign : (↑(SignType.sign u) : ℝ) = -1 := by
        rw [sign_neg huNeg]
        rfl
      rw [hsign, abs_of_neg huNeg]
      have hpow : (-u) ^ (p - 2 - 1) * (-u) = (-u) ^ (p - 2) := by
        calc
          (-u) ^ (p - 2 - 1) * (-u) =
              (-u) ^ (p - 2 - 1) * (-u) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (-u) ^ ((p - 2 - 1) + 1) :=
            (Real.rpow_add (neg_pos.mpr huNeg) _ _).symm
          _ = (-u) ^ (p - 2) := by ring_nf
      have hpowU : (-u) ^ (p - 2 - 1) * u = -((-u) ^ (p - 2)) := by
        calc
          (-u) ^ (p - 2 - 1) * u =
              -((-u) ^ (p - 2 - 1) * (-u)) := by ring
          _ = -((-u) ^ (p - 2)) := by rw [hpow]
      rw [mul_assoc ((-1 : ℝ) * (p - 2)), hpowU]
      ring
    · have hsign : (↑(SignType.sign u) : ℝ) = 1 := by
        rw [sign_pos huPos]
        rfl
      rw [hsign, abs_of_pos huPos]
      simp only [one_mul, mul_one]
      have hpow : u ^ (p - 2 - 1) * u = u ^ (p - 2) := by
        calc
          u ^ (p - 2 - 1) * u = u ^ (p - 2 - 1) * u ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = u ^ ((p - 2 - 1) + 1) := (Real.rpow_add huPos _ _).symm
          _ = u ^ (p - 2) := by ring_nf
      rw [mul_assoc, hpow]
      ring
  rw [← hid]
  change HasDerivAt ((fun y : ℝ ↦ |y| ^ (p - 2)) * id)
    ((↑(SignType.sign u) : ℝ) * (p - 2) * |u| ^ (p - 2 - 1) * id u +
      |u| ^ (p - 2) * 1) u
  exact hm
end O3.Stage2RouteA
