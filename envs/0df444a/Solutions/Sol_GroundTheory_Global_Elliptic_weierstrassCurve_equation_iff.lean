-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassCurve_equation_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:34.730835+00:00
-- url     : https://prove2.me/submissions/eeebb489-5cc2-490d-8052-293b12d5d99c

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
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (x Y : ℂ) :
    (weierstrassCurve L).toAffine.Equation x Y ↔
      (2 * Y) ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆]
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination h / 4
end GroundTheory.Global.Elliptic
