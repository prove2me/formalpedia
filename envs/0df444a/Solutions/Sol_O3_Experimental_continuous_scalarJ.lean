-- Prove2me | solution 1 for O3.Experimental.continuous_scalarJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:41.242301+00:00
-- url     : https://prove2.me/submissions/d8b1f760-da2e-4d60-912c-2729076a2cb2

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental

set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p : ℝ} (hp : 2 < p) : Continuous (scalarJ p) := by
  unfold scalarJ
  fun_prop (discharger := linarith)
end O3.Experimental
