-- Prove2me | solution 1 for GlobalTheory.exists_dual_apply_notMem_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:08.584919+00:00
-- url     : https://prove2.me/submissions/27020038-eaa5-426b-a39c-f5c73bbffde2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_exists_sum_dual_apply_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (s : Set (Ideal A)) (hs : s.Finite) (hp : ∀ P ∈ s, P.IsPrime) :
    ∃ (e : M) (f : Module.Dual A M), ∀ P ∈ s, f e ∉ P := by
  classical
  have h1 : ∀ P ∈ s, ∃ p : Module.Dual A M × M, p.1 p.2 ∉ P := by
    intro P hP
    by_contra! h
    obtain ⟨t, ht⟩ := exists_sum_dual_apply_eq_one A M
    exact (hp P hP).ne_top ((Ideal.eq_top_iff_one _).mpr (ht ▸ sum_mem fun p _ ↦ h p))
  choose! p hp1 using h1
  let t : Finset (Ideal A) := hs.toFinset.filter fun P ↦ Maximal (· ∈ s) P
  have ht : ∀ P, P ∈ t ↔ Maximal (· ∈ s) P := fun P ↦ by
    simp only [t, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.prop, h⟩⟩
  have h2 : ∀ P ∈ t, ∃ a, a ∉ P ∧ ∀ Q ∈ t, Q ≠ P → a ∈ Q := by
    intro P hP
    have hP' := (ht P).mp hP
    have : ¬ (t.erase P).inf id ≤ P := by
      rw [Ideal.IsPrime.inf_le' (hp P hP'.prop)]
      rintro ⟨Q, hQ, hle⟩
      rw [Finset.mem_erase] at hQ
      exact hQ.1 (le_antisymm hle (((ht Q).mp hQ.2).le_of_ge hP'.prop hle))
    obtain ⟨a, ha, haP⟩ := SetLike.not_le_iff_exists.mp this
    exact ⟨a, haP, fun Q hQ hne ↦
      (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne, hQ⟩) : _ ≤ Q) ha⟩
  choose! a ha ha' using h2
  let e : M := ∑ P ∈ t, a P • (p P).2
  have h3 : ∀ P ∈ t, (p P).1 e ∉ P := by
    intro P hP hmem
    have hP' := (ht P).mp hP
    simp only [e, map_sum, map_smul, smul_eq_mul] at hmem
    rw [← Finset.add_sum_erase _ _ hP] at hmem
    have h4 : ∑ Q ∈ t.erase P, a Q * (p P).1 (p Q).2 ∈ P :=
      sum_mem fun Q hQ ↦ Ideal.mul_mem_right _ _
        (ha' Q (Finset.mem_erase.mp hQ).2 P hP (Finset.mem_erase.mp hQ).1.symm)
    have h5 := (Ideal.add_mem_iff_left _ h4).mp hmem
    rcases (hp P hP'.prop).mem_or_mem h5 with h | h
    · exact ha P hP h
    · exact hp1 P hP'.prop h
  let I : Ideal A := LinearMap.range (Module.Dual.eval A M e)
  by_contra! h
  have hsub : (I : Set A) ⊆ ⋃ P ∈ s, ((id P : Ideal A) : Set A) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨P, hP, hf⟩ := h e f
    exact Set.mem_biUnion hP hf
  obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite hs (f := id) ⊥ ⊥
    (fun i hi _ _ ↦ hp i hi)).mp hsub
  obtain ⟨Q, hPQ, hQ⟩ := hs.exists_le_maximal hP
  exact h3 Q ((ht Q).mpr hQ) (hPQ (hle ⟨(p Q).1, rfl⟩))
end GlobalTheory
