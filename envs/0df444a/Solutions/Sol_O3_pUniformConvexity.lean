-- Prove2me | solution 1 for O3.pUniformConvexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:45.171184+00:00
-- url     : https://prove2.me/submissions/38461923-3364-4ca1-942a-bf35cbb5ce83

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_pUniformConvexity

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution : PUniformConvexityStatement := by
  intro p hp d x y c
  exact Experimental.pUniformConvexity hp x y c
end O3
