-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.coeff_ofCompatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:24:49.914082+00:00
-- url     : https://prove2.me/submissions/f39d840d-ba94-4b75-b3b0-94ae014267fd

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
theorem _root_.solution (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) (n : ℕ) :
    PreTilt.coeff n (ofCompatible p y hy) = Ideal.Quotient.mk _ (y n) :=
  rfl
end GroundTheory.PAdicHodge.IsPerfectoidField
