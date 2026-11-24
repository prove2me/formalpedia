-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.exists_affine_le_or_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:29.668709+00:00
-- url     : https://prove2.me/submissions/ce68f47a-1571-4483-98dc-5272b8d62bb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {W : Scheme.{0}} [Nonempty W] (t : Finset W.Opens) :
    ∃ U : W.Opens, IsAffineOpen U ∧ (U : Set W).Nonempty ∧
      ∀ O ∈ t, U ≤ O ∨ Disjoint (U : Set W) O := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    obtain ⟨x⟩ := ‹Nonempty W›
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, ⟨x, hx⟩, by simp⟩
  | insert O t _ ih =>
    obtain ⟨U, hU, hne, h⟩ := ih
    by_cases hd : Disjoint (U : Set W) O
    · refine ⟨U, hU, hne, fun O' hO' ↦ ?_⟩
      rcases Finset.mem_insert.mp hO' with rfl | hO'
      · exact .inr hd
      · exact h _ hO'
    · obtain ⟨x, hx⟩ := Set.not_disjoint_iff.mp hd
      obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ :=
        W.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (U : Set W) ∩ O from hx)
          (U.isOpen.inter O.isOpen)
      refine ⟨U', hU', ⟨x, hx'⟩, fun O' hO' ↦ ?_⟩
      rcases Finset.mem_insert.mp hO' with rfl | hO'
      · exact .inl fun z hz ↦ (hle hz).2
      · rcases h _ hO' with h | h
        · exact .inl fun z hz ↦ h (hle hz).1
        · exact .inr (h.mono_left fun z hz ↦ (hle hz).1)
end GlobalTheory.DenseClosedAffineSubsets
