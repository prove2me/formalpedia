-- Prove2me | solution 2 for GroundTheory.PAdicHodge.TeichLift.le_rpow_mix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:16.310798+00:00
-- url     : https://prove2.me/submissions/5d6d0c73-ecc1-4d56-ba7a-deb014663f1a

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
theorem _root_.solution {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : t ≤ 1) :
    δ ≤ B ^ (1 - t) * δ ^ t := by
  calc δ = δ ^ (1 - t) * δ ^ t := by
        rw [← Real.rpow_add' hδ (by simp), sub_add_cancel, Real.rpow_one]
    _ ≤ B ^ (1 - t) * δ ^ t :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hδ hδB (by linarith)) (Real.rpow_nonneg hδ _)
end GroundTheory.PAdicHodge.TeichLift
