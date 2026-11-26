-- Prove2me | solution 1 for O3.Stage2RouteC.lpNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:50.69692+00:00
-- url     : https://prove2.me/submissions/02901541-c5b5-48f9-a357-55caa38766b5

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
import Theorems.Thm_O3_Stage2RouteC_lpNorm_eq_piLpNorm

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteC
namespace O3.Stage2RouteC
theorem _root_.solution {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (a : ℝ) (x : O3.Point d) :
    O3.lpNorm p (a • x) = |a| * O3.lpNorm p x := by
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLpNorm hp, lpNorm_eq_piLpNorm hp]
  change ‖a • (WithLp.toLp (ENNReal.ofReal p) x :
      PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖ =
    |a| * ‖(WithLp.toLp (ENNReal.ofReal p) x :
      PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖
  exact norm_smul a _
end O3.Stage2RouteC
