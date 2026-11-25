-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.mem_span_of_prefixLe_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:23.31928+00:00
-- url     : https://prove2.me/submissions/e6eddbe1-2e9f-409d-82d4-be54bc894b79

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem
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
theorem _root_.solution {x : Γ} {n : ℕ} (h : T.PrefixLe x n 0) :
    x ∈ Ideal.span {T.π ^ (n + 1)} := by
  have h0 : T.partialSum x (n + 1) = 0 := by
    simp only [partialSum, finSum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := h i (by simpa [Nat.lt_succ_iff] using hi)
    rw [norm_le_zero_iff.1 this, T.teich_zero, mul_zero]
  simpa [h0] using T.sub_partialSum_mem x (n + 1)
end GroundTheory.PAdicHodge.TeichLift
