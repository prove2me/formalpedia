-- Prove2me | solution 1 for GroundTheory.PAdicHodge.fixedPoints_closedSubgroup_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:40.739703+00:00
-- url     : https://prove2.me/submissions/8308d0e0-7d58-4ae9-ae26-78c7a248f38a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_axConstant_pos
import Theorems.Thm_GroundTheory_PAdicHodge_setOf_forall_smul_eq_eq_closure
import Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma_closedSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (H : Subgroup Gal(PadicAlgCl p/K))
    (hH : IsClosed (H : Set Gal(PadicAlgCl p/K))) :
    {x : ℂ_[p] | ∀ σ ∈ H, σ • x = x} =
      closure (((↑) : PadicAlgCl p → ℂ_[p]) ''
        (IntermediateField.fixedField H : Set (PadicAlgCl p))) :=
  setOf_forall_smul_eq_eq_closure (H : Set Gal(PadicAlgCl p/K)) _
    (fun y hy σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ) axConstant_pos
    (fun z _ hz => ax_lemma_closedSubgroup H hH z hz)
end GroundTheory.PAdicHodge
