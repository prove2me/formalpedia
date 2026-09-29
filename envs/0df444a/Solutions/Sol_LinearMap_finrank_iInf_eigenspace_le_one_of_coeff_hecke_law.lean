-- Prove2me | solution 1 for LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/29520915-2c39-54e0-b393-f80bc2fb875a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law

set_option autoImplicit false

theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : ℕ → V →ₗ[K] K)
    (hinj : ∀ v : V, (∀ n : ℕ, 1 ≤ n → a n v = 0) → v = 0)
    (T : ℕ → V →ₗ[K] V) (c : ℕ → K)
    (hlaw : ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ, 1 ≤ n → ∀ v : V,
      a n (T ℓ v) = a (n * ℓ) v + (if ℓ ∣ n then c ℓ * a (n / ℓ) v else 0))
    (μ : ℕ → K) :
    (∀ v ∈ ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ), a 1 v = 0 → v = 0) ∧
    Module.finrank K ↥(⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ)) ≤ 1 := by
  classical
  set W : Submodule K V := ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ) with hW
  have hmem : ∀ v ∈ W, ∀ ℓ : ℕ, ℓ.Prime → T ℓ v = μ ℓ • v := by
    intro v hv ℓ hℓ
    have h1 : v ∈ Module.End.eigenspace (T ℓ) (μ ℓ) := by
      have := (Submodule.mem_iInf _).1 hv ℓ
      exact (Submodule.mem_iInf _).1 this hℓ
    exact Module.End.mem_eigenspace_iff.1 h1

  have key : ∀ v ∈ W, a 1 v = 0 → ∀ n : ℕ, 1 ≤ n → a n v = 0 := by
    intro v hv h1 n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1; exact h1
      · have hn2 : 2 ≤ n := by omega
        obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 from hn1)
        obtain ⟨m, rfl⟩ := hℓn
        have hℓpos : 0 < ℓ := hℓ.pos
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at hn
          · exact h
        have hmlt : m < ℓ * m := by
          have := hℓ.two_le
          nlinarith
        have ham : a m v = 0 := ih m hmlt hm1
        have hlaw' := hlaw ℓ hℓ m hm1 v
        rw [hmem v hv ℓ hℓ, LinearMap.map_smul, smul_eq_mul, ham, mul_zero] at hlaw'
        have hite : (if ℓ ∣ m then c ℓ * a (m / ℓ) v else 0) = 0 := by
          split_ifs with hdiv
          · obtain ⟨r, rfl⟩ := hdiv
            have hr1 : 1 ≤ r := by
              rcases Nat.eq_zero_or_pos r with h | h
              · subst h; simp at hm1
              · exact h
            have hrlt : r < ℓ * (ℓ * r) := by
              have := hℓ.two_le
              nlinarith
            rw [Nat.mul_div_cancel_left r hℓpos, ih r hrlt hr1, mul_zero]
          · rfl
        rw [hite, add_zero] at hlaw'
        rw [mul_comm] at hlaw'
        exact hlaw'.symm
  have hi : ∀ v ∈ W, a 1 v = 0 → v = 0 := fun v hv h1 => hinj v (key v hv h1)
  refine ⟨hi, ?_⟩

  let f : W →ₗ[K] K := (a 1).domRestrict W
  have hf : Function.Injective f := by
    intro x y hxy
    have : a 1 (x - y : W) = 0 := by
      change a 1 ((x : V) - (y : V)) = 0
      rw [map_sub]; exact sub_eq_zero.2 hxy
    have h0 := hi _ (x - y).2 this
    exact Subtype.ext (sub_eq_zero.1 (by exact_mod_cast h0))
  calc Module.finrank K W ≤ Module.finrank K K := LinearMap.finrank_le_finrank_of_injective hf
    _ = 1 := Module.finrank_self K

end S_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
end P2MW
export P2MW.S_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law (solution)
