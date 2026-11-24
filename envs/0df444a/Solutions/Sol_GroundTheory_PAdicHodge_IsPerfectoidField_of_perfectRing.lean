-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.of_perfectRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:28.651832+00:00
-- url     : https://prove2.me/submissions/724eacbc-0fcb-4f31-9519-d7d055df9005

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField

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
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p] [CompleteSpace K]
    (h : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1) : IsPerfectoidField K p where
  complete := inferInstance
  norm_natCast_lt_one := by simp [CharP.cast_eq_zero]
  exists_norm_mem_Ioo := h
  surjective_pow := surjective_pow_modP_of_exists_pow_eq (Fact.out : p.Prime).ne_zero
    fun x _ => (frobeniusEquiv K p).surjective x
end GroundTheory.PAdicHodge.IsPerfectoidField
