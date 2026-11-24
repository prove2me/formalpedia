-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.mk_untilt_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:16.203435+00:00
-- url     : https://prove2.me/submissions/c02ba5f2-4b90-4e0f-9f6e-1ff5e8f7c0f9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt

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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (x : 𝒪♭) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})
      (PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x)) = PreTilt.coeff n x := by
  rw [mk_untilt, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]
end GroundTheory.PAdicHodge.IsPerfectoidField
