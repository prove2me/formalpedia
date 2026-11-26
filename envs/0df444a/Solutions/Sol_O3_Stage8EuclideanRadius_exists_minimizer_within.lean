-- Prove2me | solution 1 for O3.Stage8EuclideanRadius.exists_minimizer_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:42.94221+00:00
-- url     : https://prove2.me/submissions/9aaf3b51-c187-4e75-9016-565a16bf882f

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_O3_Stage8EuclideanRadius
import Theorems.Thm_O3_Stage8EuclideanRadius_exists_minimizer_at_radius

set_option autoImplicit true
open O3 O3.Stage8EuclideanRadius
open O3
namespace O3.Stage8EuclideanRadius
theorem _root_.solution {d : ℕ} (P : AdmissibleInstance d 2)
    {D : ℝ} (hDR : P.radius ≤ D) :
    ∃ xstar : Vec d,
      xstar ∈ MinimizerSet P.f ∧ lpNorm 2 (xstar - P.x0) ≤ D := by
  obtain ⟨xstar, hxstar, hr⟩ := exists_minimizer_at_radius P
  exact ⟨xstar, hxstar, hr.trans_le hDR⟩
end O3.Stage8EuclideanRadius
