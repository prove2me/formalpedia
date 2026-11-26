-- Prove2me | solution 1 for O3.Stage2RouteC.lpNorm_eq_piLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:58.607793+00:00
-- url     : https://prove2.me/submissions/ede05a52-df3f-435c-83d1-73819c19c37e

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteC
namespace O3.Stage2RouteC
theorem _root_.solution {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : O3.Point d) :
    O3.lpNorm p x =
      ‖(WithLp.toLp (ENNReal.ofReal p) x :
        PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖ := by
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [PiLp.norm_eq_sum]
  · simp [O3.lpNorm, O3.lpPower, ENNReal.toReal_ofReal (zero_le_one.trans hp)]
  · simpa [ENNReal.toReal_ofReal (zero_le_one.trans hp)] using (zero_lt_one.trans_le hp)
end O3.Stage2RouteC
