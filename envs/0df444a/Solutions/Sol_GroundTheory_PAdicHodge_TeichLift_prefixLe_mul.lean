-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:10.253951+00:00
-- url     : https://prove2.me/submissions/3c4e787a-6c53-44a1-9a94-dc389bfcd961

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_of_mem_span
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_add
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_sum
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_prefixLe___pow_mul_teich_fc75b8d33f82
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
theorem _root_.solution {x y : Γ} {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, i + j ≤ n → ‖T.coeff x i‖ * ‖T.coeff y j‖ ≤ B) : T.PrefixLe (x * y) n B := by
  have h1 : x * y - T.partialSum x (n + 1) * T.partialSum y (n + 1) ∈
      Ideal.span {T.π ^ (n + 1)} := by
    have : x * y - T.partialSum x (n + 1) * T.partialSum y (n + 1) =
        (x - T.partialSum x (n + 1)) * y + T.partialSum x (n + 1) * (y - T.partialSum y (n + 1)) := by
      ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (T.sub_partialSum_mem x _))
      (Ideal.mul_mem_left _ _ (T.sub_partialSum_mem y _))
  have h2 : T.PrefixLe (T.partialSum x (n + 1) * T.partialSum y (n + 1)) n B := by
    simp only [partialSum, finSum, Finset.sum_mul_sum]
    refine T.prefixLe_sum _ _ hB fun i _ => T.prefixLe_sum _ _ hB fun j _ => ?_
    have : T.π ^ i * T.teich (T.coeff x i) * (T.π ^ j * T.teich (T.coeff y j)) =
        T.π ^ (i + j) * T.teich (T.coeff x i * T.coeff y j) := by
      rw [T.teich_mul, pow_add]; ring
    rw [this]
    exact T.prefixLe_π_pow_mul_teich _ _ _ hB fun hij => by rw [norm_mul]; exact h i j hij
  have := T.prefixLe_add h2 (T.prefixLe_of_mem_span h1 hB)
  rwa [add_sub_cancel] at this
end GroundTheory.PAdicHodge.TeichLift
