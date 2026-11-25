-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.exists_frobeniusLift_of_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:44.675179+00:00
-- url     : https://prove2.me/submissions/ef6e350b-87b1-4d4f-bb49-1d98642a41cd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_toAdd_deg_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_intCast_mem_multiples_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger MulAction
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {K : OpenSubgroup G} {x : G} (hx : x ∈ (K : Subgroup G)) {N : ℕ}
    (hN : 0 < N) (hd : D.deg x = Multiplicative.ofAdd (N : ℤ̂)) :
    ∃ s : D.FrobeniusLift K, s.elt = x := by
  have hm := toAdd_deg_mem_multiples (D := D) K hx
  rw [hd, toAdd_ofAdd, ← Int.cast_natCast,
    intCast_mem_multiples_iff (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))] at hm
  obtain ⟨m, rfl⟩ := Int.natCast_dvd_natCast.1 hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  exact ⟨⟨x, hx, m, hm0, by rw [hd, Nat.mul_comm]⟩, rfl⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
