-- Prove2me | solution 1 for HighDimProbAudit.Grothendieck.positive_feature_maps
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:10:38.806142+00:00
-- url     : https://prove2.me/submissions/dae7d17d-f1c1-4608-8747-0da6ac63ba62

import Mathlib
import Definitions.Def_HighDimProbAudit_Grothendieck_GlobalSeries

set_option autoImplicit false

open HighDimProbAudit.Grothendieck
open scoped BigOperators ENNReal

namespace SolPositiveFeatureMaps

noncomputable def tp {n : ℕ} (k : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin k → Fin n) :=
  WithLp.toLp 2 (fun t : Fin k → Fin n => ∏ r : Fin k, u (t r))

lemma tp_inner (n k : ℕ) (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (tp k u) (tp k v) = (inner ℝ u v) ^ k := by
  simp only [tp, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  have h1 : ∑ t : Fin k → Fin n, (∏ r : Fin k, v (t r)) * (∏ r : Fin k, u (t r)) =
      ∑ t : Fin k → Fin n, ∏ r : Fin k, (v (t r) * u (t r)) := by
    refine Finset.sum_congr rfl fun t _ => (Finset.prod_mul_distrib).symm
  rw [h1, ← Fintype.prod_sum (fun (_ : Fin k) (i : Fin n) => v i * u i)]
  simp

lemma tp_norm_sq (n k : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ‖tp k u‖ ^ 2 = ‖u‖ ^ (2 * k) := by
  have h1 : ‖tp k u‖ ^ 2 = inner ℝ (tp k u) (tp k u) := by
    rw [real_inner_self_eq_norm_mul_norm, sq]
  have h2 : inner ℝ u u = ‖u‖ ^ 2 := by
    rw [real_inner_self_eq_norm_mul_norm, sq]
  rw [h1, tp_inner, h2, ← pow_mul]

lemma series_case (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : GlobalPowerSeries a f) (ha : ∀ k, 0 ≤ a k) :
    ∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
          ∀ u v, inner ℝ (Φ u) (Φ v) = f (inner ℝ u v) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let E (k : ℕ) := EuclideanSpace ℝ (Fin k → Fin n)
  let H := lp E 2
  refine ⟨H, inferInstance, inferInstance, inferInstance, ?_⟩
  let seqPhi (u : EuclideanSpace ℝ (Fin n)) (k : ℕ) : E k := Real.sqrt (a k) • tp k u
  have h_norm_phi : ∀ (u : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      ‖seqPhi u k‖ ^ 2 = a k * (‖u‖ ^ 2) ^ k := by
    intro u k
    dsimp [seqPhi]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (ha k), tp_norm_sq, pow_mul]
  have h_mem_phi : ∀ u : EuclideanSpace ℝ (Fin n), Memℓp (seqPhi u) 2 := by
    intro u
    rw [memℓp_gen_iff (by norm_num)]
    refine (hf (‖u‖ ^ 2)).summable.congr fun k => ?_
    rw [← h_norm_phi u k, ENNReal.toReal_ofNat, Real.rpow_two]
  let Φ (u : EuclideanSpace ℝ (Fin n)) : H := ⟨seqPhi u, h_mem_phi u⟩
  refine ⟨Φ, fun u v => ?_⟩
  have h_lp := lp.hasSum_inner (𝕜 := ℝ) (Φ u) (Φ v)
  have h_term : (fun k : ℕ => inner ℝ ((Φ u) k) ((Φ v) k)) =
      fun k : ℕ => a k * (inner ℝ u v) ^ k := by
    ext k
    change inner ℝ (Real.sqrt (a k) • tp k u) (Real.sqrt (a k) • tp k v) = _
    rw [real_inner_smul_left, real_inner_smul_right, tp_inner, ← mul_assoc,
      Real.mul_self_sqrt (ha k)]
  rw [h_term] at h_lp
  exact h_lp.unique (hf (inner ℝ u v))

end SolPositiveFeatureMaps

open SolPositiveFeatureMaps

theorem solution (n : ℕ) :
    (∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
          ∀ u v, inner ℝ (Φ u) (Φ v) =
            2 * (inner ℝ u v) ^ 2 + 5 * (inner ℝ u v) ^ 3) ∧
    (∀ p : Polynomial ℝ, (∀ k : ℕ, 0 ≤ p.coeff k) →
      ∃ (H : Type) (hN : NormedAddCommGroup H),
        letI := hN
        ∃ hI : InnerProductSpace ℝ H,
          letI := hI
          CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
            ∀ u v, inner ℝ (Φ u) (Φ v) = p.eval (inner ℝ u v)) ∧
    (∀ (a : ℕ → ℝ) (f : ℝ → ℝ), GlobalPowerSeries a f → (∀ k, 0 ≤ a k) →
      ∃ (H : Type) (hN : NormedAddCommGroup H),
        letI := hN
        ∃ hI : InnerProductSpace ℝ H,
          letI := hI
          CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
            ∀ u v, inner ℝ (Φ u) (Φ v) = f (inner ℝ u v)) := by
  refine ⟨?_, ?_, series_case n⟩
  · let a : ℕ → ℝ := fun k => if k = 2 then 2 else if k = 3 then 5 else 0
    let f : ℝ → ℝ := fun x => 2 * x ^ 2 + 5 * x ^ 3
    have hf : GlobalPowerSeries a f := by
      intro x
      have h_sum : ∑ k ∈ ({2, 3} : Finset ℕ), a k * x ^ k = f x := by
        rw [Finset.sum_pair (by decide)]
        rfl
      rw [← h_sum]
      refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      dsimp [a]
      rw [if_neg hk.1, if_neg hk.2, zero_mul]
    have ha : ∀ k, 0 ≤ a k := by
      intro k
      dsimp [a]
      split_ifs <;> positivity
    exact series_case n a f hf ha
  · intro p hp
    have hf : GlobalPowerSeries (fun k => p.coeff k) (fun x => p.eval x) := by
      intro x
      dsimp
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
      refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
      rw [Polynomial.notMem_support_iff.mp hk, zero_mul]
    exact series_case n (fun k => p.coeff k) (fun x => p.eval x) hf hp
