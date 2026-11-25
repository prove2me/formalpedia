-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.exists_prefix_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:09.445665+00:00
-- url     : https://prove2.me/submissions/da364f26-f257-4153-b94a-9dbbe7dbc35b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_π_mul_zero
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (x : Γ) (n : ℕ) :
    ∃ c : L, T.PrefixLe x n ‖c‖ ∧ ∀ b, T.PrefixLe x n b → ‖c‖ ≤ b := by
  obtain ⟨m, hm, hmax⟩ := (Finset.range (n + 1)).exists_max_image (fun i => ‖T.coeff x i‖)
    ⟨0, by simp⟩
  exact ⟨T.coeff x m, fun i hi => hmax i (Finset.mem_range.2 (by omega)),
    fun b hb => hb m (by simpa [Nat.lt_succ_iff] using hm)⟩
end GroundTheory.PAdicHodge.TeichLift
