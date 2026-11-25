-- Prove2me | solution 1 for LeJEPAWorldModel.gaussian_of_affine_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:51:45.136029+00:00
-- url     : https://prove2.me/submissions/c42c67db-d37b-462f-887f-4af43758c662

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace LeJEPAWorldModel

theorem gaussian_of_affine_eigenfunction (K lam a b : ℝ) (hK : 0 < K) (hlam : 0 < lam)
    (ha : a ≠ 0) (p : ℝ → ℝ) (hpos : ∀ x, 0 < p x) (hdiff : Differentiable ℝ p)
    (hnorm : ∫ x, p x = 1)
    (heig : ∀ x, slGenerator K p (fun y => a * y + b) x = -lam * (a * x + b)) :
    ∀ x, p x = gaussianPDFReal (-b / a) (K / lam).toNNReal x := by
  set v : ℝ≥0 := (K / lam).toNNReal with hvdef
  have hv : (v : ℝ) = K / lam := Real.coe_toNNReal _ (by positivity)
  have hv0 : (0 : ℝ) < v := by rw [hv]; positivity
  have hvne : v ≠ 0 := by intro h; rw [h] at hv0; simp at hv0
  set μ : ℝ := -b / a with hμ
  have hφ : ∀ y, deriv (fun y => a * y + b) y = a := fun y => by
    have := ((hasDerivAt_id y).const_mul a).add_const b
    simpa using this.deriv
  have hp' : ∀ x, deriv p x = -(lam / K) * (x - μ) * p x := by
    intro x
    have h := heig x
    unfold slGenerator at h
    simp only [hφ] at h
    have hd : deriv (fun y => K * p y * a) x = K * deriv p x * a :=
      (((hdiff x).hasDerivAt.const_mul K).mul_const a).deriv
    rw [hd, one_div, inv_mul_eq_iff_eq_mul₀ (hpos x).ne'] at h
    have e : deriv p x = (K * deriv p x * a) / (K * a) := by field_simp
    rw [e, h, hμ]
    field_simp
    ring
  set q : ℝ → ℝ := fun x => p x * Real.exp (lam / K * (x - μ) ^ 2 / 2) with hq
  have hq' : ∀ x, HasDerivAt q 0 x := by
    intro x
    have hin : HasDerivAt (fun x => lam / K * (x - μ) ^ 2 / 2) (lam / K * (x - μ)) x := by
      refine (((((hasDerivAt_id x).sub_const μ).pow 2).const_mul (lam / K)).div_const 2).congr_deriv ?_
      simp only [id, Nat.cast_ofNat, mul_one]
      ring
    refine ((hdiff x).hasDerivAt.mul hin.exp).congr_deriv ?_
    rw [hp' x]; ring
  have hconst := is_const_of_deriv_eq_zero (fun x => (hq' x).differentiableAt)
    (fun x => (hq' x).deriv)
  set C := q 0
  have hpx : ∀ x, p x = C * Real.exp (-(lam / K * (x - μ) ^ 2 / 2)) := by
    intro x
    have h1 : q x = C := hconst x 0
    simp only [hq] at h1
    rw [← h1, mul_assoc, ← Real.exp_add]; simp
  have hG : ∀ x, gaussianPDFReal μ v x =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(lam / K * (x - μ) ^ 2 / 2)) := by
    intro x
    rw [gaussianPDFReal_def]
    congr 2
    rw [hv]; field_simp
  have hs : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.2 (by positivity)
  have hpG : ∀ x, p x = (C * Real.sqrt (2 * Real.pi * v)) * gaussianPDFReal μ v x := by
    intro x; rw [hpx, hG]; field_simp
  have hint : ∫ x, p x = C * Real.sqrt (2 * Real.pi * v) := by
    simp_rw [hpG]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one μ hvne, mul_one]
  intro x
  rw [hpG x, ← hint, hnorm, one_mul]

end LeJEPAWorldModel
open LeJEPAWorldModel in
theorem solution (K lam a b : ℝ) (hK : 0 < K) (hlam : 0 < lam)
    (ha : a ≠ 0) (p : ℝ → ℝ) (hpos : ∀ x, 0 < p x) (hdiff : Differentiable ℝ p)
    (hnorm : ∫ x, p x = 1)
    (heig : ∀ x, slGenerator K p (fun y => a * y + b) x = -lam * (a * x + b)) :
    ∀ x, p x = ProbabilityTheory.gaussianPDFReal (-b / a) (K / lam).toNNReal x :=
  gaussian_of_affine_eigenfunction K lam a b hK hlam ha p hpos hdiff hnorm heig
