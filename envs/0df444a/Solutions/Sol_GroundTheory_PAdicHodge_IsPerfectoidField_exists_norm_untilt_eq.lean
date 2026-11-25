-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_norm_untilt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:36.250004+00:00
-- url     : https://prove2.me/submissions/73505945-509d-4550-b03e-be2173d7b905

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_eq_of_mk_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mk_untilt_eq

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
variable (p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {b : 𝒪} (hb : ‖(p : K)‖ < ‖(b : K)‖) :
    ∃ a : 𝒪♭, ‖((PreTilt.untilt a : 𝒪) : K)‖ = ‖(b : K)‖ := by
  obtain ⟨a, ha⟩ := exists_mk_untilt_eq p b
  exact ⟨a, norm_eq_of_mk_eq p ha hb⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
