-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.mk_untilt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:09.417798+00:00
-- url     : https://prove2.me/submissions/1afa62b3-0d87-49bc-aab4-7ba3a0201580

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta

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
theorem _root_.solution (x : 𝒪♭) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt x) = PreTilt.coeff 0 x :=
  PreTilt.mk_untilt_eq_coeff_zero x
end GroundTheory.PAdicHodge.IsPerfectoidField
