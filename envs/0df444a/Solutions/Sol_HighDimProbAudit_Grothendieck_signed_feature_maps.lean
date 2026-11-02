-- Prove2me | solution 1 for HighDimProbAudit.Grothendieck.signed_feature_maps
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:08:29.290891+00:00
-- url     : https://prove2.me/submissions/dbfb8506-02eb-4f36-86d0-384d65cf2024

import Mathlib
import Definitions.Def_HighDimProbAudit_Grothendieck_GlobalSeries

set_option autoImplicit false

open HighDimProbAudit.Grothendieck
open scoped BigOperators ENNReal

namespace SolSignedFeatureMaps

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

noncomputable def cPhi (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.sqrt |a k|

noncomputable def cPsi (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (if 0 ≤ a k then 1 else -1) * Real.sqrt |a k|

lemma cPhi_sq (a : ℕ → ℝ) (k : ℕ) : (cPhi a k) ^ 2 = |a k| :=
  Real.sq_sqrt (abs_nonneg (a k))

lemma cPsi_sq (a : ℕ → ℝ) (k : ℕ) : (cPsi a k) ^ 2 = |a k| := by
  unfold cPsi
  rw [mul_pow, Real.sq_sqrt (abs_nonneg (a k))]
  split_ifs <;> ring

lemma cPhi_mul_cPsi (a : ℕ → ℝ) (k : ℕ) : cPhi a k * cPsi a k = a k := by
  unfold cPhi cPsi
  have hsq : Real.sqrt |a k| * Real.sqrt |a k| = |a k| :=
    Real.mul_self_sqrt (abs_nonneg (a k))
  calc Real.sqrt |a k| * ((if 0 ≤ a k then 1 else -1) * Real.sqrt |a k|)
    _ = (if 0 ≤ a k then 1 else -1) * (Real.sqrt |a k| * Real.sqrt |a k|) := by ring
    _ = (if 0 ≤ a k then 1 else -1) * |a k| := by rw [hsq]
    _ = a k := by
        split_ifs with h0
        · rw [one_mul, abs_of_nonneg h0]
        · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h0), neg_neg]

lemma summable_abs_pow {a : ℕ → ℝ} {f : ℝ → ℝ} (hf : GlobalPowerSeries a f)
    {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : ℕ => |a k| * ‖u‖ ^ (2 * k)) := by
  have h1 : Summable (fun k : ℕ => |a k * (‖u‖ ^ 2) ^ k|) :=
    (hf (‖u‖ ^ 2)).summable.abs
  refine h1.congr fun k => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg (sq_nonneg ‖u‖) k), ← pow_mul]

end SolSignedFeatureMaps

open SolSignedFeatureMaps

theorem solution (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : GlobalPowerSeries a f) :
    ∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧ ∃ Φ Ψ : EuclideanSpace ℝ (Fin n) → H,
          (∀ u v, inner ℝ (Φ u) (Ψ v) = f (inner ℝ u v)) ∧
          (∀ u, HasSum (fun k : ℕ => |a k| * ‖u‖ ^ (2 * k)) (‖Φ u‖ ^ 2) ∧
            ‖Φ u‖ ^ 2 = ‖Ψ u‖ ^ 2) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let E (k : ℕ) := EuclideanSpace ℝ (Fin k → Fin n)
  let H := lp E 2
  refine ⟨H, inferInstance, inferInstance, inferInstance, ?_⟩
  let seqPhi (u : EuclideanSpace ℝ (Fin n)) (k : ℕ) : E k := cPhi a k • tp k u
  let seqPsi (u : EuclideanSpace ℝ (Fin n)) (k : ℕ) : E k := cPsi a k • tp k u
  have h_norm_phi : ∀ (u : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      ‖seqPhi u k‖ ^ 2 = |a k| * ‖u‖ ^ (2 * k) := by
    intro u k
    dsimp [seqPhi]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, cPhi_sq, tp_norm_sq]
  have h_norm_psi : ∀ (u : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      ‖seqPsi u k‖ ^ 2 = |a k| * ‖u‖ ^ (2 * k) := by
    intro u k
    dsimp [seqPsi]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, cPsi_sq, tp_norm_sq]
  have h_mem_phi : ∀ u : EuclideanSpace ℝ (Fin n), Memℓp (seqPhi u) 2 := by
    intro u
    rw [memℓp_gen_iff (by norm_num)]
    refine (summable_abs_pow hf u).congr fun k => ?_
    rw [← h_norm_phi u k, ENNReal.toReal_ofNat, Real.rpow_two]
  have h_mem_psi : ∀ u : EuclideanSpace ℝ (Fin n), Memℓp (seqPsi u) 2 := by
    intro u
    rw [memℓp_gen_iff (by norm_num)]
    refine (summable_abs_pow hf u).congr fun k => ?_
    rw [← h_norm_psi u k, ENNReal.toReal_ofNat, Real.rpow_two]
  let Φ (u : EuclideanSpace ℝ (Fin n)) : H := ⟨seqPhi u, h_mem_phi u⟩
  let Ψ (u : EuclideanSpace ℝ (Fin n)) : H := ⟨seqPsi u, h_mem_psi u⟩
  refine ⟨Φ, Ψ, ?_, ?_⟩
  · intro u v
    have h_lp := lp.hasSum_inner (𝕜 := ℝ) (Φ u) (Ψ v)
    have h_term : (fun k : ℕ => inner ℝ ((Φ u) k) ((Ψ v) k)) =
        fun k : ℕ => a k * (inner ℝ u v) ^ k := by
      ext k
      change inner ℝ (cPhi a k • tp k u) (cPsi a k • tp k v) = _
      rw [real_inner_smul_left, real_inner_smul_right, tp_inner, ← mul_assoc, cPhi_mul_cPsi]
    rw [h_term] at h_lp
    exact h_lp.unique (hf (inner ℝ u v))
  · intro u
    have h_phi_inner := lp.hasSum_inner (𝕜 := ℝ) (Φ u) (Φ u)
    have h_psi_inner := lp.hasSum_inner (𝕜 := ℝ) (Ψ u) (Ψ u)
    have h_phi_eq : inner ℝ (Φ u) (Φ u) = ‖Φ u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, sq]
    have h_psi_eq : inner ℝ (Ψ u) (Ψ u) = ‖Ψ u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, sq]
    have h_term_phi : (fun k : ℕ => inner ℝ ((Φ u) k) ((Φ u) k)) =
        fun k : ℕ => |a k| * ‖u‖ ^ (2 * k) := by
      ext k
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
      exact h_norm_phi u k
    have h_term_psi : (fun k : ℕ => inner ℝ ((Ψ u) k) ((Ψ u) k)) =
        fun k : ℕ => |a k| * ‖u‖ ^ (2 * k) := by
      ext k
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
      exact h_norm_psi u k
    rw [h_term_phi, h_phi_eq] at h_phi_inner
    rw [h_term_psi, h_psi_eq] at h_psi_inner
    exact ⟨h_phi_inner, h_phi_inner.unique h_psi_inner⟩
