-- Prove2me | solution 1 for O3.Stage8EuclideanRadius.lpNorm_two_eq_transport_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:56.495799+00:00
-- url     : https://prove2.me/submissions/539f8f3e-34c5-4c1e-9d0b-cce6be7402b9

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_O3_Stage8EuclideanRadius
import Theorems.Thm_O3_Stage2RouteC_lpNorm_eq_piLpNorm


set_option autoImplicit true
open O3 O3.Stage8EuclideanRadius
open O3
namespace O3.Stage8EuclideanRadius
theorem _root_.solution {d : ℕ} (x y : Vec d) :
    lpNorm 2 (x - y) =
      dist
        (WithLp.toLp (ENNReal.ofReal (2 : ℝ)) x : EuclideanLpSpace d)
        (WithLp.toLp (ENNReal.ofReal (2 : ℝ)) y : EuclideanLpSpace d) := by
  rw [Stage2RouteC.lpNorm_eq_piLpNorm (p := (2 : ℝ)) (by norm_num)]
  change
    ‖(WithLp.toLp (ENNReal.ofReal (2 : ℝ)) (x - y) : EuclideanLpSpace d)‖ =
      ‖(WithLp.toLp (ENNReal.ofReal (2 : ℝ)) x : EuclideanLpSpace d) -
        WithLp.toLp (ENNReal.ofReal (2 : ℝ)) y‖
  rfl
end O3.Stage8EuclideanRadius
