-- Prove2me | solution 1 for MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5c30b379-db7a-5c5d-9e57-d3f88b24f3cf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem solution
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (e : Fin n → X → ℂ)
    (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (w : X → ℂ) (hw : Integrable (fun x => ‖w x‖ ^ 2) μ)
    (hwe : ∀ j, Integrable (fun x => w x * conj (e j x)) μ) :
    ∑ j, ‖∫ x, w x * conj (e j x) ∂μ‖ ^ 2 ≤ ∫ x, ‖w x‖ ^ 2 ∂μ := by
  classical

  set a : Fin n → ℂ := fun j => ∫ x, w x * conj (e j x) ∂μ with ha
  set s : X → ℂ := fun x => ∑ j, a j * e j x with hs

  have hI1 : Integrable (fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ)) μ := hw.ofReal
  have hI2 : ∀ j, Integrable (fun x => conj (a j) * (w x * conj (e j x))) μ := fun j => (hwe j).const_mul _
  have hIc : ∀ j, Integrable (fun x => conj (w x * conj (e j x))) μ := fun j => by
    have := Complex.conjCLE.toContinuousLinearMap.integrable_comp (hwe j)
    simpa using this
  have hI3 : ∀ j, Integrable (fun x => a j * conj (w x * conj (e j x))) μ := fun j => (hIc j).const_mul _
  have hI4 : ∀ i j, Integrable (fun x => a i * conj (a j) * (e i x * conj (e j x))) μ :=
    fun i j => (hint i j).const_mul _
  have hS1 : Integrable (fun x => ∑ j, conj (a j) * (w x * conj (e j x))) μ :=
    integrable_finsetSum _ fun j _ => hI2 j
  have hS2 : Integrable (fun x => ∑ j, a j * conj (w x * conj (e j x))) μ :=
    integrable_finsetSum _ fun j _ => hI3 j
  have hS3 : Integrable (fun x => ∑ i, ∑ j, a i * conj (a j) * (e i x * conj (e j x))) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI4 i j

  have hsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hexp : ∀ x, ((‖w x - s x‖ ^ 2 : ℝ) : ℂ) =
      ((‖w x‖ ^ 2 : ℝ) : ℂ) - (∑ j, conj (a j) * (w x * conj (e j x)))
        - (∑ j, a j * conj (w x * conj (e j x)))
        + ∑ i, ∑ j, a i * conj (a j) * (e i x * conj (e j x)) := by
    intro x
    have h1 : w x * conj (s x) = ∑ j, conj (a j) * (w x * conj (e j x)) := by
      simp only [hs, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h2 : s x * conj (w x) = ∑ j, a j * conj (w x * conj (e j x)) := by
      simp only [hs, map_mul, Complex.conj_conj, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : s x * conj (s x) = ∑ i, ∑ j, a i * conj (a j) * (e i x * conj (e j x)) := by
      simp only [hs, map_sum, map_mul, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsq, hsq, ← h1, ← h2, ← h3, map_sub]
    ring

  have hint_exp : ∫ x, ((‖w x - s x‖ ^ 2 : ℝ) : ℂ) ∂μ =
      ((∫ x, ‖w x‖ ^ 2 ∂μ : ℝ) : ℂ) - ∑ j, a j * conj (a j) := by
    have hE : (fun x => ((‖w x - s x‖ ^ 2 : ℝ) : ℂ)) = fun x =>
        ((‖w x‖ ^ 2 : ℝ) : ℂ) - (∑ j, conj (a j) * (w x * conj (e j x)))
          - (∑ j, a j * conj (w x * conj (e j x)))
          + ∑ i, ∑ j, a i * conj (a j) * (e i x * conj (e j x)) := funext hexp
    have hA : Integrable (fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ) - (∑ j, conj (a j) * (w x * conj (e j x)))
        - (∑ j, a j * conj (w x * conj (e j x)))) μ := (hI1.sub hS1).sub hS2
    have hB : Integrable (fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ) - (∑ j, conj (a j) * (w x * conj (e j x)))) μ :=
      hI1.sub hS1
    have h0 : ∫ x, ((‖w x‖ ^ 2 : ℝ) : ℂ) ∂μ = ((∫ x, ‖w x‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [hE, integral_add hA hS3, integral_sub hB hS2, integral_sub hI1 hS1,
      h0, integral_finsetSum _ (fun j _ => hI2 j), integral_finsetSum _ (fun j _ => hI3 j),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI4 i j)]
    have e1 : ∀ j, ∫ x, conj (a j) * (w x * conj (e j x)) ∂μ = conj (a j) * a j := fun j => by
      rw [integral_const_mul]
    have e2 : ∀ j, ∫ x, a j * conj (w x * conj (e j x)) ∂μ = a j * conj (a j) := fun j => by
      rw [integral_const_mul, integral_conj]
    have e3 : ∀ i, ∫ x, ∑ j, a i * conj (a j) * (e i x * conj (e j x)) ∂μ = a i * conj (a i) := fun i => by
      rw [integral_finsetSum _ (fun j _ => hI4 i j)]
      have : ∀ j, ∫ x, a i * conj (a j) * (e i x * conj (e j x)) ∂μ =
          if i = j then a i * conj (a i) else 0 := fun j => by
        rw [integral_const_mul, hon]
        split_ifs with h
        · subst h; ring
        · ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_ite_eq]
      simp
    simp only [e1, e2, e3]
    have : ∑ j, conj (a j) * a j = ∑ j, a j * conj (a j) := Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this]
    ring

  have hpos : 0 ≤ ∫ x, ‖w x - s x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have hkey : ((∫ x, ‖w x‖ ^ 2 ∂μ : ℝ) : ℂ) - ∑ j, a j * conj (a j) = ((∫ x, ‖w x - s x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← hint_exp]
    exact integral_ofReal
  have hnorm : ∀ j, a j * conj (a j) = ((‖a j‖ ^ 2 : ℝ) : ℂ) := fun j => (hsq (a j)).symm
  simp only [hnorm] at hkey
  have hreal : (∫ x, ‖w x‖ ^ 2 ∂μ) - ∑ j, ‖a j‖ ^ 2 = ∫ x, ‖w x - s x‖ ^ 2 ∂μ := by
    have := hkey
    push_cast at this
    exact_mod_cast this
  have : ∑ j, ‖a j‖ ^ 2 ≤ ∫ x, ‖w x‖ ^ 2 ∂μ := by linarith
  simpa only [ha] using this

end S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
end P2MW
export P2MW.S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal (solution)
