-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_one_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:13.315426+00:00
-- url     : https://prove2.me/submissions/97146af6-ab1b-4914-966c-c0766bf6c7df

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_one_of_pow_eq_one

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
theorem _root_.solution {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) :
    ‖ζ - 1‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max ζ (-1)
  rw [← sub_eq_add_neg, norm_neg, norm_one, norm_eq_one_of_pow_eq_one hN hζ, max_self] at this
  exact this
end GroundTheory.PAdicHodge
