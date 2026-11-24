-- Prove2me | solution 1 for GlobalTheory.involution_pair_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:03.665469+00:00
-- url     : https://prove2.me/submissions/91a3fd1d-ac5d-4503-890f-24f2ec876239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRepresentativesTwoElementOrbitsInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  intro ι _ s hs
  classical
  haveI := Fintype.ofFinite ι
  set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS
  have memS : ∀ x : S, enc (x : ι) < enc (s x) := fun x => (Finset.mem_filter.1 x.2).2
  refine ⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩
  · intro j k h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j k h
    simp only at h
    have hj := memS (S.equivFin.symm j)
    have hk := memS (S.equivFin.symm k)
    generalize (S.equivFin.symm j : ι) = a at h hj
    generalize (S.equivFin.symm k : ι) = b at h hk
    subst h
    rw [hs] at hk
    omega
  · intro i
    by_cases hi : s i = i
    · exact Or.inl hi
    right
    have hne : enc i ≠ enc (s i) := fun h => hi (henc h).symm
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      exact ⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩
    · have hm : s i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩
      exact ⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩
end GlobalTheory
