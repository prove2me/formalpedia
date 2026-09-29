-- Prove2me | solution 1 for LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cd3e05f0-1cce-5100-bf90-a09f3c7b9a2c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact

set_option autoImplicit false

open Module

universe u v

namespace P2mLES

variable {k : Type u} [DivisionRing k]

theorem finrank_eq_range_add_ker {M N : Type v} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [Module.Finite k M] (f : M →ₗ[k] N) :
    finrank k M = finrank k (LinearMap.range f) + finrank k (LinearMap.ker f) :=
  (LinearMap.finrank_range_add_finrank_ker f).symm

theorem main
    (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i)) = 0 := by

  set a : ℕ → ℕ := fun i => finrank k (LinearMap.range (f i)) with ha
  set b : ℕ → ℕ := fun i => finrank k (LinearMap.range (g i)) with hb
  set r : ℕ → ℕ := fun i => finrank k (LinearMap.range (δ i)) with hr

  have hB : ∀ i, finrank k (B i) = b i + a i := fun i => by
    rw [finrank_eq_range_add_ker (g i), (LinearMap.exact_iff.mp (hfg i))]
  have hC : ∀ i, finrank k (C i) = r i + b i := fun i => by
    rw [finrank_eq_range_add_ker (δ i), (LinearMap.exact_iff.mp (hgδ i))]
  have hA : ∀ i, finrank k (A (i + 1)) = a (i + 1) + r i := fun i => by
    rw [finrank_eq_range_add_ker (f (i + 1)), (LinearMap.exact_iff.mp (hδf i))]
  have hA0 : finrank k (A 0) = a 0 := by
    rw [finrank_eq_range_add_ker (f 0), LinearMap.ker_eq_bot.mpr hf0, finrank_bot, add_zero]

  set t : ℕ → ℤ := fun i => Nat.rec (motive := fun _ => ℤ) 0 (fun j _ => (r j : ℤ)) i with ht
  have ht0 : t 0 = 0 := rfl
  have htS : ∀ i, t (i + 1) = r i := fun i => rfl
  have hterm : ∀ i, ((finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i)) = t i + t (i + 1) := by
    intro i
    cases i with
    | zero =>
      rw [hA0, hB 0, hC 0, ht0, htS]
      push_cast
      ring
    | succ j =>
      rw [hA j, hB (j + 1), hC (j + 1), htS, htS]
      push_cast
      ring

  have htel : ∀ i, (-1 : ℤ) ^ i * (t i + t (i + 1))
      = (-1 : ℤ) ^ i * t i - (-1 : ℤ) ^ (i + 1) * t (i + 1) := fun i => by
    rw [pow_succ]
    ring
  simp_rw [hterm, htel]
  rw [Finset.sum_range_sub' (fun i => (-1 : ℤ) ^ i * t i) N, ht0, mul_zero, zero_sub, neg_eq_zero]

  cases N with
  | zero => rw [ht0, mul_zero]
  | succ m =>
    rw [htS]
    have : r m = 0 := by
      simp only [hr]
      haveI : Subsingleton (LinearMap.range (δ m)) := inferInstance
      exact Module.finrank_zero_of_subsingleton
    rw [this, Nat.cast_zero, mul_zero]

end P2mLES

theorem solution
    {k : Type u} [DivisionRing k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0 :=
  P2mLES.main A B C f g δ hf0 hfg hgδ hδf N hN

end S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact
end P2MW
export P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact (solution)
