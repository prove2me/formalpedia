-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_abs_affine_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:22.95479+00:00
-- url     : https://prove2.me/submissions/57939bfd-3973-45ca-8ec4-25698f589b60

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p a b t : ℝ} (hp : 1 < p) :
    HasDerivAt (fun s : ℝ ↦ |a + s * b| ^ p)
      (p * |a + t * b| ^ (p - 2) * (a + t * b) * b) t := by
  have hbase := hasDerivAt_abs_rpow (a + t * b) hp
  have haff : HasDerivAt (fun s : ℝ ↦ a + s * b) b t := by
    convert ((hasDerivAt_id t).mul_const b).const_add a using 1 <;>
      first | rfl | ring
  convert hbase.comp t haff using 1 <;> rfl
end O3.Stage2RouteA
