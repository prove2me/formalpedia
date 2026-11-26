-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_scalarJ_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:22.827844+00:00
-- url     : https://prove2.me/submissions/e3ca679c-9bf7-4dd0-91ca-63c473db6df3

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_of_ne_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p a b t : ℝ} (hz : a + t * b ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ O3.Experimental.scalarJ p (a + s * b))
      ((p - 1) * |a + t * b| ^ (p - 2) * b) t := by
  have haff : HasDerivAt (fun s : ℝ ↦ a + s * b) b t := by
    convert ((hasDerivAt_id t).mul_const b).const_add a using 1 <;>
      first | rfl | ring
  change HasDerivAt
    (O3.Experimental.scalarJ p ∘ fun s : ℝ ↦ a + s * b)
    (((p - 1) * |a + t * b| ^ (p - 2)) * b) t
  exact (hasDerivAt_scalarJ_of_ne_zero (p := p) hz).comp t haff
end O3.Stage2RouteA
