-- Prove2me | solution 1 for MaxCutSample2027.Coreset.theorem_2_9
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:40:40.684888+00:00
-- url     : https://prove2.me/submissions/58692d22-6926-4028-8c24-b93c7fda2d01

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_5
import Theorems.Thm_MaxCutSample2027_Coreset_equation_2_14
import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

private theorem empirical_sum {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (x : Fin k → V) (f : V → ℝ) : ∑ v, empirical x v * f v = (∑ i, f (x i)) / (k : ℝ) := by
  calc
    _ = (∑ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) * f v) / (k : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ => by simp only [empirical]; ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x) (fun _ _ => Finset.mem_univ _) (fun i => f (x i))]
      apply Finset.sum_congr rfl
      intro v _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

private theorem empirical_probability {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (x : Fin k → V) : IsProbabilityVector (empirical x) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨fun v => div_nonneg (Nat.cast_nonneg _) hk'.le, ?_⟩
  simpa [hk'.ne'] using empirical_sum x (fun _ => 1)

private theorem sample_le {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f g : (Fin k → V) → ℝ) (h : ∀ x, f x ≤ g x) :
    sampleAverage p k f ≤ sampleAverage p k g := by
  unfold sampleAverage
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x)
    (Finset.prod_nonneg fun i _ => hp (x i))

private theorem sample_smul {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (a : ℝ) (f : (Fin k → V) → ℝ) : sampleAverage p k (fun x => a * f x) = a * sampleAverage p k f := by
  unfold sampleAverage
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x => |FK (K A p) (empirical x) - FK (K A p) p|) ≤
      48 * H A p / Real.sqrt (k : ℝ) := by
  have hpp : IsProbabilityVector p := ⟨fun v => (hp.1 v).le, hp.2⟩
  have pointwise (x : Fin k → V) : |FK (K A p) (empirical x) - FK (K A p) p| ≤
      4 * DeltaK (K A p) p (empirical x) := by
    rw [abs_sub_comm]
    exact lemma_2_5 A p hA hp p (empirical x) hpp (empirical_probability hk x)
  calc
    _ ≤ sampleAverage p k (fun x => 4 * DeltaK (K A p) p (empirical x)) := sample_le hpp.1 _ _ pointwise
    _ = 4 * sampleAverage p k (fun x => DeltaK (K A p) p (empirical x)) := sample_smul _ _ _
    _ ≤ 4 * (12 * H A p / Real.sqrt (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (equation_2_14 A p hA hp k hk) (by norm_num)
    _ = _ := by ring
