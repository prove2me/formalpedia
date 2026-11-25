-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.untilt_coeff_zero_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:44.08121+00:00
-- url     : https://prove2.me/submissions/c75246ce-935f-4b46-9f61-be42f528e57c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_fontaineTheta_teichmuller_add_mul_p

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
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {ξ v : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) :
    PreTilt.untilt (ξ.coeff 0) + θ v * p = 0 := by
  rw [← fontaineTheta_teichmuller_add_mul_p, ← hv]
  exact hξ
end GroundTheory.PAdicHodge.IsPerfectoidField
