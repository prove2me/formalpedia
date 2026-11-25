-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:31.060896+00:00
-- url     : https://prove2.me/submissions/33eac300-2631-4277-9e8b-f7adf9155fec

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_coeff_of_sub_mem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_mem_int
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_int_iff
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
theorem _root_.solution {x : Γ} {n : ℕ} {c : L} (hc : c ≠ 0) :
    T.PrefixLe x n ‖c‖ ↔ ∃ u ∈ T.int, x - T.teich c * u ∈ Ideal.span {T.π ^ (n + 1)} := by
  constructor
  · intro h
    refine ⟨T.finSum (fun i => T.coeff x i / c) (n + 1), T.finSum_mem_int fun i hi => ?_, ?_⟩
    · rw [norm_div, div_le_one (norm_pos_iff.2 hc)]
      exact h i (by omega)
    · have : T.teich c * T.finSum (fun i => T.coeff x i / c) (n + 1) = T.partialSum x (n + 1) := by
        simp only [finSum, partialSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_left_comm, ← T.teich_mul, mul_div_cancel₀ _ hc]
      rw [this]; exact T.sub_partialSum_mem x (n + 1)
  · rintro ⟨u, hu, h⟩ m hm
    rw [T.coeff_eq_coeff_of_sub_mem h m hm, coeff_teich_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((T.mem_int_iff.1 hu) m)
end GroundTheory.PAdicHodge.TeichLift
