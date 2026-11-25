-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.coeff_teich_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:51.1992+00:00
-- url     : https://prove2.me/submissions/45b1f8d0-3161-45dd-99eb-f64411a27acd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_of_mem
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
theorem _root_.solution (c : L) (x : Γ) (n : ℕ) : T.coeff (T.teich c * x) n = c * T.coeff x n := by
  refine T.coeff_eq_of_mem (a := fun i => c * T.coeff x i) ?_ n le_rfl
  have : T.finSum (fun i => c * T.coeff x i) (n + 1) = T.teich c * T.partialSum x (n + 1) := by
    simp only [finSum, partialSum, Finset.mul_sum, T.teich_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, ← mul_sub]
  exact Ideal.mul_mem_left _ _ (T.sub_partialSum_mem x (n + 1))
end GroundTheory.PAdicHodge.TeichLift
