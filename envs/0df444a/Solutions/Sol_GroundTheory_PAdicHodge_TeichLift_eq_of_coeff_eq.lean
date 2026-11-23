-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.eq_of_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:15.480288+00:00
-- url     : https://prove2.me/submissions/4027de2b-9748-4a2c-89d4-1506c60be79e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {x y : Γ} (h : T.coeff x = T.coeff y) : x = y := by
  haveI := T.isAdicComplete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := T.I) (x - y) fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]
  have h1 := T.sub_partialSum_mem x n
  have h2 := T.sub_partialSum_mem y n
  have : x - y = (x - T.partialSum x n) - (y - T.partialSum y n) := by
    simp only [partialSum, h]; ring
  rw [this]; exact sub_mem h1 h2
end GroundTheory.PAdicHodge.TeichLift
