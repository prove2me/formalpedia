-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_natCast_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:18.940936+00:00
-- url     : https://prove2.me/submissions/84428dce-25ad-4d13-a7ce-d63e569b1259

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_UpperTheory_Reformulated_B_CapelliMiscellany_norm_natCast_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ :=
  _root_.UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime
end GroundTheory.PAdicHodge
