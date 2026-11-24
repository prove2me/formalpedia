-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.untilt_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:22.025861+00:00
-- url     : https://prove2.me/submissions/7ae50f6a-08f7-40ae-b51e-320cfcf35476

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt_iterate
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero

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
theorem _root_.solution {x : 𝒪♭} : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => preTilt_ext p fun n => ?_, fun h => h ▸ untilt_zero p⟩
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  rw [h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
  rw [← mk_untilt_iterate, h1, map_zero, map_zero]
end GroundTheory.PAdicHodge.IsPerfectoidField
