-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:45:48.326599+00:00
-- url     : https://prove2.me/submissions/7cabe8c4-a566-4ba3-a4af-95158ff73978

import Theorems.Thm_MaxCutSample2027_Coreset_theorem_2_1
import Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_2_10
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

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
    (A : V → V → ℝ) (hA : IsWeightMatrix A) (hbound : ∀ u v, A u v ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage (uniformLaw (V := V)) k
      (fun x => |maxCut (Ahat A uniformLaw x) - maxCut A|) ≤
      48 * (Fintype.card V : ℝ) ^ 2 / Real.sqrt (k : ℝ) := by
  let N : ℝ := Fintype.card V
  let p : V → ℝ := uniformLaw
  have hN : 0 < N := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  have hp : IsPositiveProbabilityVector p := by
    constructor
    · intro v
      change 0 < 1 / N
      positivity
    · change (∑ _ : V, 1 / N) = 1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change N * (1 / N) = 1
      field_simp [hN.ne']
  have dom (v : V) : weightedDegree A v / N ^ 2 ≤ p v := by
    have bound : weightedDegree A v ≤ N := by
      unfold weightedDegree
      calc
        _ ≤ ∑ _ : V, (1 : ℝ) := Finset.sum_le_sum fun u _ => hbound v u
        _ = _ := by simp [N]
    change weightedDegree A v / N ^ 2 ≤ 1 / N
    apply (div_le_iff₀ (by positivity : 0 < N ^ 2)).2
    have h : 1 / N * N ^ 2 = N := by field_simp [hN.ne']
    simpa only [h] using bound
  have hH : H A p ≤ 1 := (lemma_2_10 A p hA hp hbound).2 dom
  have h := theorem_2_1 A p hA hp k hk
  have scale (x : Fin k → V) : |(maxCut (Ahat A p x) - maxCut A) / N ^ 2| =
      (1 / N ^ 2) * |maxCut (Ahat A p x) - maxCut A| := by rw [abs_div, abs_of_pos (by positivity : 0 < N ^ 2)]; ring
  change sampleAverage p k (fun x => |(maxCut (Ahat A p x) - maxCut A) / N ^ 2|) ≤ _ at h
  simp only [scale, sample_smul] at h
  have hden : 0 < Real.sqrt (k : ℝ) := by positivity
  have h₁ : 48 * H A p / Real.sqrt (k : ℝ) ≤ 48 / Real.sqrt (k : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have h₂ := h.trans h₁
  change sampleAverage p k (fun x => |maxCut (Ahat A p x) - maxCut A|) ≤
    48 * N ^ 2 / Real.sqrt (k : ℝ)
  rw [one_div, inv_mul_le_iff₀ (by positivity : 0 < N ^ 2)] at h₂
  convert h₂ using 1 <;> first | rfl | ring
