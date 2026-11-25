-- Prove2me | solution 1 for GroundTheory.PAdicHodge.fixedPoints_gal_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:27.967587+00:00
-- url     : https://prove2.me/submissions/62d9ad94-ca5d-474b-b274-04089ecf8f16

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_axConstant_pos
import Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma
import Theorems.Thm_GroundTheory_PAdicHodge_setOf_forall_smul_eq_eq_closure

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
theorem _root_.solution :
    MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] =
      closure (((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p))) := by
  have h := setOf_forall_smul_eq_eq_closure (K := K) Set.univ (K : Set (PadicAlgCl p))
    (fun y hy σ _ => σ.commutes ⟨y, hy⟩) axConstant_pos
    (fun z r hz => ax_lemma z fun σ => hz σ (Set.mem_univ σ))
  rw [← h]
  ext x
  simp [MulAction.mem_fixedPoints]
end GroundTheory.PAdicHodge
