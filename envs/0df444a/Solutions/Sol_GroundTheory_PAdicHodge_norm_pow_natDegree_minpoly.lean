-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_natDegree_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:30.212792+00:00
-- url     : https://prove2.me/submissions/cffedb0e-82fd-4c4e-ae59-36d6e5ec50bc

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
theorem _root_.solution (y : PadicAlgCl p) :
    ‖y‖ ^ (minpoly ℚ_[p] y).natDegree = ‖(minpoly ℚ_[p] y).coeff 0‖ := by
  have hd : (minpoly ℚ_[p] y).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)).ne'
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
    Real.rpow_inv_natCast_pow (norm_nonneg _) hd]
end GroundTheory.PAdicHodge
