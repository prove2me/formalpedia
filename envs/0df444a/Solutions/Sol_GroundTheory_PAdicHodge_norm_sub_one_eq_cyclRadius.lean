-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_one_eq_cyclRadius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:51.958427+00:00
-- url     : https://prove2.me/submissions/f1c3b5b6-717a-4c3a-9757-b24124a2f195

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_of_isPrimitiveRoot
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
theorem _root_.solution {η : PadicAlgCl p} {j : ℕ} (hη : IsPrimitiveRoot η (p ^ j)) :
    ‖η - 1‖ = cyclRadius p j :=
  norm_sub_one_eq_of_isPrimitiveRoot (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (exists_isPrimitiveRoot (p := p) j).choose_spec hη
end GroundTheory.PAdicHodge
