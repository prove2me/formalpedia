-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclRadius_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:37.177367+00:00
-- url     : https://prove2.me/submissions/6ac55cf4-1b68-45b9-a61e-a3dad5275ffc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot


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
theorem _root_.solution (j : ℕ) : cyclRadius p j ≤ 1 :=
  norm_sub_one_le_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (exists_isPrimitiveRoot (p := p) j).choose_spec.pow_eq_one
end GroundTheory.PAdicHodge
