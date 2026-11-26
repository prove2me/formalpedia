-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_line_duality_pair_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:36:28.133036+00:00
-- url     : https://prove2.me/submissions/3206724b-53a1-4694-8ba5-f9c59d0903d7

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_line_duality_pair_eq_affine_of_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {q : ℝ} (hq : 1 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    HasDerivAt (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h)
      ((lpNorm q h) ^ (2 : ℕ)) t := by
  rw [line_duality_pair_eq_affine_of_zero hq x h t hz]
  convert ((hasDerivAt_id t).sub_const t).mul_const
    ((lpNorm q h) ^ (2 : ℕ)) using 1 <;>
    first | rfl | ring
end O3.Stage2RouteA
