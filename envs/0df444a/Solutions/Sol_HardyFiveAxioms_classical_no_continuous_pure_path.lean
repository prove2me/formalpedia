-- Prove2me | solution 1 for HardyFiveAxioms.classical_no_continuous_pure_path
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:06:20.325485+00:00
-- url     : https://prove2.me/submissions/8021a52d-e95f-48bf-849b-95cb2d161118

import Mathlib
import Definitions.Def_hardy2001_states

set_option autoImplicit false

namespace HardyFiveAxioms

lemma cl05e_convex (N : ℕ) : Convex ℝ (classicalStates N) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun n => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 n
    have := hy.1 n
    positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := hx.2
    have h2 := hy.2
    nlinarith

lemma cl05e_gen_subset (N : ℕ) :
    (insert (0 : Fin N → ℝ) (Set.range (fun n : Fin N => basisState n))) ⊆ classicalStates N := by
  intro z hz
  rcases hz with rfl | ⟨n, rfl⟩
  · refine ⟨fun _ => le_refl _, ?_⟩
    simp
  · refine ⟨fun m => ?_, ?_⟩
    · simp only [basisState, Pi.single_apply]
      split_ifs <;> norm_num
    · simp [basisState]

lemma cl05e_mem_hull (N : ℕ) (p : Fin N → ℝ) (hp : p ∈ classicalStates N) :
    p ∈ convexHull ℝ (insert (0 : Fin N → ℝ) (Set.range (fun n : Fin N => basisState n))) := by
  let w : Option (Fin N) → ℝ := fun o => Option.elim o (1 - ∑ n, p n) p
  let z : Option (Fin N) → (Fin N → ℝ) := fun o => Option.elim o 0 basisState
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Option (Fin N))), 0 ≤ w i := by
    intro i _
    cases i with
    | none => simp only [w, Option.elim]; linarith [hp.2]
    | some n => simp only [w, Option.elim]; exact hp.1 n
  have hw1 : ∑ i, w i = 1 := by
    rw [Fintype.sum_option]
    simp [w]
  have hz : ∀ i ∈ (Finset.univ : Finset (Option (Fin N))),
      z i ∈ convexHull ℝ (insert (0 : Fin N → ℝ) (Set.range (fun n : Fin N => basisState n))) := by
    intro i _
    apply subset_convexHull
    cases i with
    | none => simp [z]
    | some n => simp [z]
  have key := (convex_convexHull ℝ _).sum_mem hw0 hw1 hz
  have heq : ∑ i, w i • z i = p := by
    rw [Fintype.sum_option]
    simp only [w, z, Option.elim, smul_zero, zero_add]
    ext m
    simp [Finset.sum_apply, basisState, Pi.single_apply]
  rwa [heq] at key

lemma cl05e_pure_coord (N : ℕ) (p : Fin N → ℝ) (hp : p ∈ pureStates (classicalStates N))
    (m : Fin N) : p m = 0 ∨ p m = 1 := by
  obtain ⟨hext, hne⟩ := hp
  have hsub : convexHull ℝ (insert (0 : Fin N → ℝ) (Set.range (fun n : Fin N => basisState n)))
      ⊆ classicalStates N :=
    convexHull_min (cl05e_gen_subset N) (cl05e_convex N)
  have hmem := cl05e_mem_hull N p (mem_extremePoints.1 hext).1
  have h2 : p ∈ Set.extremePoints ℝ
      (convexHull ℝ (insert (0 : Fin N → ℝ) (Set.range (fun n : Fin N => basisState n)))) :=
    inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hmem, hext⟩
  have h3 := extremePoints_convexHull_subset h2
  rcases h3 with h0 | ⟨n, rfl⟩
  · exact absurd h0 hne
  · simp only [basisState, Pi.single_apply]
    split_ifs
    · right; rfl
    · left; rfl

end HardyFiveAxioms

open HardyFiveAxioms in
theorem solution (N : ℕ) (γ : unitInterval → (Fin N → ℝ))
    (hγ : Continuous γ) (hpure : ∀ t, γ t ∈ pureStates (classicalStates N)) :
    ∀ t, γ t = γ 0 := by
  intro t
  funext m
  have hc : Continuous (fun s => γ s m) := (continuous_apply m).comp hγ
  by_contra hne
  have ht := cl05e_pure_coord N (γ t) (hpure t) m
  have h0 := cl05e_pure_coord N (γ 0) (hpure 0) m
  have hmid : ∀ a b : unitInterval, γ a m = 0 → γ b m = 1 → False := by
    intro a b ha hb
    have hI := intermediate_value_univ a b hc
    rw [ha, hb] at hI
    obtain ⟨s, hs⟩ := hI (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rcases cl05e_pure_coord N (γ s) (hpure s) m with h | h
    · simp only at hs; rw [hs] at h; norm_num at h
    · simp only at hs; rw [hs] at h; norm_num at h
  rcases ht with ht | ht <;> rcases h0 with h0 | h0
  · exact hne (by rw [ht, h0])
  · exact hmid t 0 ht h0
  · exact hmid 0 t h0 ht
  · exact hne (by rw [ht, h0])
