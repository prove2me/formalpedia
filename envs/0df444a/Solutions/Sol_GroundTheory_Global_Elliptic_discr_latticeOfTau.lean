-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.discr_latticeOfTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:11.089176+00:00
-- url     : https://prove2.me/submissions/0f312627-fc82-4a1d-a105-03948951959d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_g__latticeOfTau_1a1fccf096b7
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_g__latticeOfTau_ea6d51c2ccc7

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
    discr (latticeOfTau τ) = (2 * π) ^ 12 * ModularForm.discriminant τ := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [discr, g₂_latticeOfTau, g₃_latticeOfTau, h]
  ring
end GroundTheory.Global.Elliptic
