-- Prove2me | solution 1 for HighDimStat.Rkhs.pre_inner_welldefined
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:35:32.080712+00:00
-- url     : https://prove2.me/submissions/a2bc6463-8672-4e7d-8e52-ec5d85004e2c

import Mathlib

set_option autoImplicit false

namespace HighDimStat.Rkhs
namespace P2MAlias

/-- A kernel `K` on `X` is positive semidefinite: every finite Gram matrix is PSD. -/
abbrev IsPSDKernel {X : Type} (K : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
    0 ≤ Finset.sum Finset.univ (fun i =>
      Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)))

end P2MAlias
end HighDimStat.Rkhs

open HighDimStat.Rkhs.P2MAlias in
theorem solution {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    (∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
      (∀ z : X, Finset.sum Finset.univ (fun i => c i * K z (x i)) = 0) →
      Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))) = 0) ∧
    (∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
      0 ≤ Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)))) := by
  refine ⟨fun n x c hz => ?_, hK⟩
  have h : ∀ i, Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)) = 0 := by
    intro i
    have h1 : Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))
        = c i * Finset.sum Finset.univ (fun j => c j * K (x i) (x j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [h1, hz (x i), mul_zero]
  exact Finset.sum_eq_zero (fun i _ => h i)

