-- Prove2me | solution 1 for GlobalTheory.RowFubini.relIndex_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:01.205084+00:00
-- url     : https://prove2.me/submissions/fb0832fd-6d7d-4e19-ae26-20678ab7ca7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
import Theorems.Thm_GlobalTheory_RowFubini_relIndex_eq_of_le_of_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
theorem _root_.solution {G Y : Type*} [Group G] [Group Y] (π : G →* Y) (A B : Subgroup G)
    (hBA : B ≤ A) :
    B.relIndex A = B.relIndex (A ⊓ π.ker) * (B.map π).relIndex (A.map π) := by
  set S := (B ⊔ π.ker) ⊓ A with hS
  have hBS : B ≤ S := le_inf le_sup_left hBA
  have hSA : S ≤ A := inf_le_right
  have h1 : B.relIndex A = B.relIndex S * S.relIndex A :=
    (Subgroup.relIndex_mul_relIndex B S A hBS hSA).symm
  have h2 : S.relIndex A = (B.map π).relIndex (A.map π) := by
    rw [Subgroup.relIndex_map_map, hS, Subgroup.inf_relIndex_right]
    refine relIndex_eq_of_le_of_cover _ _ _ le_sup_left ?_
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
    obtain ⟨a, ha, n, hn, rfl⟩ := hg
    exact ⟨a, ha, by simpa using (le_sup_right : π.ker ≤ B ⊔ π.ker) hn⟩
  have h3 : B.relIndex S = B.relIndex (A ⊓ π.ker) := by
    refine (relIndex_eq_of_le_of_cover _ _ _ ?_ ?_).symm
    · exact le_inf (inf_le_right.trans le_sup_right) inf_le_left
    · intro g hg
      have hgA : g ∈ A := hg.2
      have hg1 : g ∈ π.ker ⊔ B := sup_comm B π.ker ▸ hg.1
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg1
      obtain ⟨m, hm, b, hb, rfl⟩ := hg1
      refine ⟨m, ⟨?_, hm⟩, by simpa using hb⟩
      have : m = (m * b) * b⁻¹ := by group
      rw [this]
      exact A.mul_mem hgA (A.inv_mem (hBA hb))
  rw [h1, h2, h3]
end GlobalTheory.RowFubini
