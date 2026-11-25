-- Prove2me | solution 2 for GroundTheory.PAdicHodge.TeichLift.rpow_mix_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:29.7028+00:00
-- url     : https://prove2.me/submissions/b3277884-188e-4a32-8f13-1e4589366975

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
theorem _root_.solution {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    B ^ (1 - t) * δ ^ t ≤ B := by
  have hB : 0 ≤ B := hδ.trans hδB
  calc B ^ (1 - t) * δ ^ t ≤ B ^ (1 - t) * B ^ t :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ hδB ht) (Real.rpow_nonneg hB _)
    _ = B := by rw [← Real.rpow_add' hB (by simp), sub_add_cancel, Real.rpow_one]
end GroundTheory.PAdicHodge.TeichLift
