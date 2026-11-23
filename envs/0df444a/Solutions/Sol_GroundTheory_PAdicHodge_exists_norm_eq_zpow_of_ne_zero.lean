-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_eq_zpow_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:30.058491+00:00
-- url     : https://prove2.me/submissions/9ac3db15-798e-4d9c-a8ff-d7d92178f9ac

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
theorem _root_.solution {c : ℚ_[p]} (hc : c ≠ 0) : ∃ z : ℤ, ‖c‖ = (p : ℝ) ^ z :=
  ⟨-c.valuation, Padic.norm_eq_zpow_neg_valuation hc⟩
end GroundTheory.PAdicHodge
