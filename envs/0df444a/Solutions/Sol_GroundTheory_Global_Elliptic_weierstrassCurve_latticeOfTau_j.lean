-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassCurve_latticeOfTau_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:08.847598+00:00
-- url     : https://prove2.me/submissions/f6b7ad72-0ae4-4dc0-a5f9-8ec88ac69274

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_g__latticeOfTau_1a1fccf096b7
import Theorems.Thm_GroundTheory_Global_Elliptic_discr_latticeOfTau
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCurve_j


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology
open scoped PeriodPair Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (τ : ℍ) :
    (weierstrassCurve (latticeOfTau τ)).j = modularJ τ := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weierstrassCurve_j, discr_latticeOfTau, g₂_latticeOfTau, modularJ]
  field_simp
  ring
end GroundTheory.Global.Elliptic
