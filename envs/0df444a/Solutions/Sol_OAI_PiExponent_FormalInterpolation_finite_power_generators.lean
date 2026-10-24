-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_power_generators
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:54:29.367979+00:00
-- url     : https://prove2.me/submissions/7f953053-7261-426a-b08f-06cf1077faaa

import Mathlib
open scoped BigOperators Pointwise

theorem solution
    {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
    (J : Ideal R) (x : ι → R)
    (s₀ n₀ : ι → Nat) (F₀ : ι → Finset R)
    (hs₀ : ∀ i, 0 < s₀ i) (hn₀ : ∀ i, 0 < n₀ i)
    (hF₀ : ∀ i f, f ∈ F₀ i → f ∈ J ^ (s₀ i))
    (hpow₀ : ∀ i, x i ^ n₀ i ∈ Ideal.span (F₀ i : Set R)) :
    ∃ (s : Nat) (S : Finset R),
      0 < s ∧
      (∀ g ∈ S, g ∈ J ^ s) ∧
      ∀ i, ∃ k : Nat, 0 < k ∧ s = s₀ i * k ∧
        x i ^ (n₀ i * k) ∈ Ideal.span (S : Set R) := by
  classical
  let s : ℕ := ∏ i, s₀ i
  have hs : 0 < s := Finset.prod_pos (fun i _ => hs₀ i)
  have hdiv : ∀ i, s₀ i ∣ s := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let k : ι → ℕ := fun i => s / s₀ i
  have hk : ∀ i, s = s₀ i * k i := fun i => (Nat.mul_div_cancel' (hdiv i)).symm
  have hkpos : ∀ i, 0 < k i := fun i => Nat.div_pos (Nat.le_of_dvd hs (hdiv i)) (hs₀ i)
  let S : Finset R := Finset.univ.biUnion (fun i => F₀ i ^ k i)
  -- span of a power of a set is the power of the span
  have hspan : ∀ i, Ideal.span ((F₀ i ^ k i : Finset R) : Set R) = Ideal.span (F₀ i : Set R) ^ k i := by
    intro i
    rw [Finset.coe_pow]
    exact (Submodule.span_pow _ _).symm
  refine ⟨s, S, hs, ?_, fun i => ⟨k i, hkpos i, hk i, ?_⟩⟩
  · intro g hg
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hg
    have h1 : g ∈ Ideal.span ((F₀ i ^ k i : Finset R) : Set R) := Ideal.subset_span hgi
    rw [hspan i] at h1
    have h2 : Ideal.span (F₀ i : Set R) ≤ J ^ s₀ i := by
      rw [Ideal.span_le]; intro f hf; exact hF₀ i f hf
    have := Ideal.pow_right_mono h2 (k i) h1
    rwa [← pow_mul, ← hk i] at this
  · rw [pow_mul]
    have h1 := Ideal.pow_mem_pow (hpow₀ i) (k i)
    rw [← hspan i] at h1
    exact Ideal.span_mono (fun y hy => Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_coe.mp hy⟩)) h1
