-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:33.904058+00:00
-- url     : https://prove2.me/submissions/67e70f99-69f6-4a10-bcf0-1137fd1c7b13

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_zero
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_add
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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Γ) {n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, T.PrefixLe (f i) n b) : T.PrefixLe (∑ i ∈ s, f i) n b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T.prefixLe_zero n hb
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact T.prefixLe_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end GroundTheory.PAdicHodge.TeichLift
