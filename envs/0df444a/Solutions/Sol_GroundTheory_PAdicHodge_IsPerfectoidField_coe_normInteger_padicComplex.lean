-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.coe_normInteger_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:46.422726+00:00
-- url     : https://prove2.me/submissions/ecb74f48-c12c-4211-ab09-5a28e36e8e60

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (normInteger ℂ_[p] : Set ℂ_[p]) = (𝓞_ℂ_[p] : Set ℂ_[p]) := by
  ext x
  rw [SetLike.mem_coe, mem_normInteger, PadicComplex.norm_eq_norm, SetLike.mem_coe,
    PadicComplexInt, Valuation.mem_valuationSubring_iff]
  exact Valued.toNormedField.norm_le_one_iff (L := ℂ_[p]) (Γ₀ := ℝ≥0)
end GroundTheory.PAdicHodge.IsPerfectoidField
