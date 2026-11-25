-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_multiset_sum_le_of_forall_le_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:56.26141+00:00
-- url     : https://prove2.me/submissions/30b8f45c-302e-48c0-af46-14dd754b9de0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTraceFₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTraceₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (s : Multiset (PadicAlgCl p)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ‖x‖ ≤ C) : ‖s.sum‖ ≤ C := by
  induction s using Multiset.induction_on with
  | empty => simpa using hC
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max a s.sum).trans
      (max_le (h a (Multiset.mem_cons_self a s)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))
end GroundTheory.PAdicHodge
