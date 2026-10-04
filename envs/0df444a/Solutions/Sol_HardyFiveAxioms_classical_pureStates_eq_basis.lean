-- Prove2me | solution 1 for HardyFiveAxioms.classical_pureStates_eq_basis
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:09:26.99866+00:00
-- url     : https://prove2.me/submissions/469f654a-6707-4d83-a5a0-2d8c54d78850

import Mathlib
import Definitions.Def_hardy2001_states

set_option autoImplicit false

namespace HardyFiveAxioms.Aux04334560

open HardyFiveAxioms

lemma ext_left {N : ℕ} {S : Set (Fin N → ℝ)} {p x y : Fin N → ℝ}
    (hp : p ∈ Set.extremePoints ℝ S) (hx : x ∈ S) (hy : y ∈ S)
    (h : ∀ i, x i + y i = 2 * p i) : x = p := by
  have hmem : p ∈ openSegment ℝ x y := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [h i]
  exact ((mem_extremePoints.1 hp).2 x hx y hy hmem).1

lemma sum_one {N : ℕ} {p : Fin N → ℝ} (hp : p ∈ Set.extremePoints ℝ (classicalStates N))
    (h0 : p ≠ 0) : ∑ n, p n = 1 := by
  have hpS : p ∈ classicalStates N := hp.1
  obtain ⟨hnn, hsum⟩ := hpS
  set s := ∑ n, p n with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => hnn i)
  by_contra hne
  have hlt : s < 1 := lt_of_le_of_ne hsum hne
  have hx : (fun n => (2 - s) * p n) ∈ classicalStates N := by
    refine ⟨fun n => mul_nonneg (by linarith) (hnn n), ?_⟩
    rw [← Finset.mul_sum, ← hs]
    nlinarith
  have hy : (fun n => s * p n) ∈ classicalStates N := by
    refine ⟨fun n => mul_nonneg hs0 (hnn n), ?_⟩
    rw [← Finset.mul_sum, ← hs]
    nlinarith
  have heq := ext_left hp hx hy (fun i => by ring)
  apply h0
  funext n
  have := congrFun heq n
  have h1 : (1 - s) * p n = 0 := by linarith
  have h2 : (1 - s) ≠ 0 := by linarith
  simpa using (mul_eq_zero.1 h1).resolve_left h2

lemma two_zero {N : ℕ} {p : Fin N → ℝ} (hp : p ∈ Set.extremePoints ℝ (classicalStates N))
    {i j : Fin N} (hij : i ≠ j) : p i = 0 ∨ p j = 0 := by
  have hpS : p ∈ classicalStates N := hp.1
  obtain ⟨hnn, hsum⟩ := hpS
  by_contra hcon
  push_neg at hcon
  have hi : 0 < p i := lt_of_le_of_ne (hnn i) (Ne.symm hcon.1)
  have hj : 0 < p j := lt_of_le_of_ne (hnn j) (Ne.symm hcon.2)
  set d := min (p i) (p j) with hd
  have hd0 : 0 < d := lt_min hi hj
  have hdi : d ≤ p i := min_le_left _ _
  have hdj : d ≤ p j := min_le_right _ _
  have hx : (p + Pi.single i d - Pi.single j d) ∈ classicalStates N := by
    refine ⟨fun n => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : n = i
      · subst h1; simp [hij]; linarith [hnn n]
      · by_cases h2 : n = j
        · subst h2; simp [h1]; linarith
        · simp [h1, h2]; exact hnn n
    · simp only [Pi.add_apply, Pi.sub_apply]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_pi_single',
        Finset.sum_pi_single']
      simp only [Finset.mem_univ, if_true]
      linarith
  have hy : (p - Pi.single i d + Pi.single j d) ∈ classicalStates N := by
    refine ⟨fun n => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : n = i
      · subst h1; simp [hij]; linarith
      · by_cases h2 : n = j
        · subst h2; simp [h1]; linarith [hnn n]
        · simp [h1, h2]; exact hnn n
    · simp only [Pi.add_apply, Pi.sub_apply]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_pi_single',
        Finset.sum_pi_single']
      simp only [Finset.mem_univ, if_true]
      linarith
  have heq := ext_left hp hx hy (fun n => by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have := congrFun heq i
  simp [hij] at this
  linarith

lemma sub_basis {N : ℕ} (p : Fin N → ℝ) (hp : p ∈ pureStates (classicalStates N)) :
    p ∈ Set.range (basisState (N := N)) := by
  obtain ⟨hext, h0⟩ := hp
  have h0' : p ≠ 0 := h0
  have hs := sum_one hext h0'
  have hnn := hext.1.1
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0' (funext hc)
  have hzero : ∀ j, j ≠ i → p j = 0 := fun j hj =>
    (two_zero hext hj).resolve_right hi
  have hpi : p i = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj) (by simp)] at hs
    exact hs
  refine ⟨i, ?_⟩
  funext k
  simp only [basisState, Pi.single_apply]
  by_cases hk : k = i
  · subst hk; simp [hpi]
  · simp [hk, hzero k hk]

lemma basis_mem {N : ℕ} (n : Fin N) : basisState n ∈ classicalStates N := by
  refine ⟨fun m => ?_, ?_⟩
  · simp only [basisState, Pi.single_apply]; split_ifs <;> norm_num
  · simp [basisState]

lemma basis_sub {N : ℕ} (n : Fin N) : basisState n ∈ pureStates (classicalStates N) := by
  refine ⟨mem_extremePoints.2 ⟨basis_mem n, ?_⟩, ?_⟩
  · intro x hx y hy hseg
    obtain ⟨a, b, ha, hb, hab, hxy⟩ := hseg
    obtain ⟨hxn, hxs⟩ := hx
    obtain ⟨hyn, hys⟩ := hy
    have hc : ∀ m, a * x m + b * y m = basisState n m := fun m => by
      have := congrFun hxy m
      simpa [smul_eq_mul] using this
    have hoff : ∀ m, m ≠ n → x m = 0 ∧ y m = 0 := by
      intro m hm
      have h := hc m
      simp [basisState, Pi.single_apply, hm] at h
      have h1 := mul_nonneg ha.le (hxn m)
      have h2 := mul_nonneg hb.le (hyn m)
      constructor
      · have : a * x m = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left ha.ne'
      · have : b * y m = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hb.ne'
    have hxsum : ∑ m, x m = x n :=
      Finset.sum_eq_single n (fun m _ hm => (hoff m hm).1) (by simp)
    have hysum : ∑ m, y m = y n :=
      Finset.sum_eq_single n (fun m _ hm => (hoff m hm).2) (by simp)
    have hn := hc n
    simp [basisState] at hn
    have hx1 : x n ≤ 1 := hxsum ▸ hxs
    have hy1 : y n ≤ 1 := hysum ▸ hys
    have hxn1 : x n = 1 := by nlinarith
    have hyn1 : y n = 1 := by nlinarith
    constructor
    · funext m
      by_cases hm : m = n
      · subst hm; simp [basisState, hxn1]
      · simp [basisState, Pi.single_apply, hm, (hoff m hm).1]
    · funext m
      by_cases hm : m = n
      · subst hm; simp [basisState, hyn1]
      · simp [basisState, Pi.single_apply, hm, (hoff m hm).2]
  · intro h
    have := congrFun (h : basisState n = 0) n
    simp [basisState] at this

end HardyFiveAxioms.Aux04334560

open HardyFiveAxioms in
theorem solution (N : ℕ) :
    pureStates (classicalStates N) = Set.range (basisState (N := N)) := by
  ext p
  constructor
  · exact HardyFiveAxioms.Aux04334560.sub_basis p
  · rintro ⟨n, rfl⟩
    exact HardyFiveAxioms.Aux04334560.basis_sub n
