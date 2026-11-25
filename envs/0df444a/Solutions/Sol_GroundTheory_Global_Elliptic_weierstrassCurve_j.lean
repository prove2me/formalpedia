-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassCurve_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:37.527487+00:00
-- url     : https://prove2.me/submissions/00b2efa0-7a3e-4fa0-a575-6704f7571921

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution : (weierstrassCurve L).j = 1728 * L.g₂ ^ 3 / discr L := by
  rw [WeierstrassCurve.j_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  have h := discr_ne_zero L
  rw [discr] at h
  have h1 : 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
    intro h0
    apply h
    linear_combination -16 * h0
  rw [div_eq_div_iff h1 h]
  ring
end GroundTheory.Global.Elliptic
