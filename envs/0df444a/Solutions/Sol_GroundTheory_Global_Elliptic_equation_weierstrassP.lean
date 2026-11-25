-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.equation_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:04:07.486749+00:00
-- url     : https://prove2.me/submissions/2e1e70d9-0c52-4ebe-a729-385f9aba82a2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCurve_equation_iff

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
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) :
    (weierstrassCurve L).toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [weierstrassCurve_equation_iff, mul_div_cancel₀ _ two_ne_zero]
  exact L.derivWeierstrassP_sq z hz
end GroundTheory.Global.Elliptic
