-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:13.660333+00:00
-- url     : https://prove2.me/submissions/eb6b9ac2-ded1-429d-bc5a-a1f0cd18a6bd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower

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
theorem _root_.solution {x : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) :
    ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN).1 h
end GroundTheory.PAdicHodge
