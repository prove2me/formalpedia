-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.isUnit_of_coeff_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:08.024903+00:00
-- url     : https://prove2.me/submissions/2d1acb01-4023-4b63-87fa-515b2ee0c97d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {u : Γ} (h : T.coeff u 0 = 1) : IsUnit u := by
  haveI := T.isAdicComplete
  have he : u - 1 ∈ T.I := by
    show u - 1 ∈ Ideal.span {T.π}
    rw [← T.ker_red, RingHom.mem_ker, map_sub, map_one, ← coeff_zero, h, sub_self]
  have := (Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot (I := T.I) he)) 1
  simpa using this
end GroundTheory.PAdicHodge.TeichLift
