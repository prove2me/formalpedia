-- Prove2me | solution 1 for Grothendieck.ae_mulVecE_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:38:13.898565+00:00
-- url     : https://prove2.me/submissions/eb01d8f4-71b5-49e4-a759-cef4eee45558

import Mathlib
import Definitions.Def_Grothendieck_Gaussian

/-!
# The degenerate correlation `|τ| = 1` of Lemma 2.1 (Briët–de Oliveira Filho–Vallentin)
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace Grothendieck

/-! ### Coordinate lemmas for `mulVecE` -/

lemma equiv_apply_eq_ofLp {m : Type*} [Fintype m] (x : EuclideanSpace ℝ m) (i : m) :
    (EuclideanSpace.equiv m ℝ) x i = x.ofLp i := by
  rw [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply]

lemma ofLp_equiv_symm {m : Type*} [Fintype m] (y : m → ℝ) (i : m) :
    ((EuclideanSpace.equiv m ℝ).symm y).ofLp i = y i := by
  simp [EuclideanSpace.equiv]

lemma ofLp_mulVecE {r n : ℕ} (Z : Fin r → Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n))
    (i : Fin r) : (mulVecE r n Z u).ofLp i = ∑ j, Z i j * u.ofLp j := by
  simp only [mulVecE, Matrix.mulVec, Matrix.of, dotProduct, ofLp_equiv_symm, equiv_apply_eq_ofLp]
  exact Finset.sum_congr rfl fun j _ => rfl

/-! ### The law of a nonzero linear form of one standard Gaussian row -/

theorem map_linForm_row {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    Measure.map (fun z : Fin n → ℝ => ∑ i, z i * u.ofLp i)
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = gaussianReal 0 (Real.toNNReal (‖u‖ ^ 2)) := by
  have hfun : (fun z : Fin n → ℝ => ∑ i, z i * u.ofLp i)
      = (innerSL ℝ u) ∘ (WithLp.toLp 2) := by
    funext z
    rw [Function.comp_apply, innerSL_apply_apply, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rw [hfun, ← Measure.map_map (innerSL ℝ u).continuous.measurable
      (WithLp.measurable_toLp 2 (Fin n → ℝ)),
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

theorem measure_linForm_row_eq_zero {n : ℕ} {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)
      {z : Fin n → ℝ | ∑ i, z i * u.ofLp i = 0} = 0 := by
  have hpos : 0 < ‖u‖ ^ 2 := by
    have h : 0 < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  have hne : Real.toNNReal (‖u‖ ^ 2) ≠ 0 := by
    have h : 0 < Real.toNNReal (‖u‖ ^ 2) := by rwa [Real.toNNReal_pos]
    exact h.ne'
  have hmeas : Measurable (fun z : Fin n → ℝ => ∑ i, z i * u.ofLp i) := by fun_prop
  have hpre : {z : Fin n → ℝ | ∑ i, z i * u.ofLp i = 0}
      = (fun z : Fin n → ℝ => ∑ i, z i * u.ofLp i) ⁻¹' {0} := rfl
  rw [hpre, ← Measure.map_apply hmeas (measurableSet_singleton 0), map_linForm_row]
  exact (nullSingletonClass_gaussianReal hne).measure_singleton 0

/-! ### Target 1: `Zu ≠ 0` almost surely -/

theorem ae_mulVecE_ne_zero {r n : ℕ} (hr : 1 ≤ r) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) : ∀ᵐ Z ∂(gaussianMatrix r n), mulVecE r n Z u ≠ 0 := by
  rw [ae_iff, gaussianMatrix]
  have hnull : (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {Z : Fin r → Fin n → ℝ | Z ⟨0, hr⟩ ∈ {z : Fin n → ℝ | ∑ i, z i * u.ofLp i = 0}} = 0 :=
    Measure.pi_eval_preimage_null
      (μ := fun _ : Fin r => Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (i := ⟨0, hr⟩) (s := {z : Fin n → ℝ | ∑ i, z i * u.ofLp i = 0})
      (measure_linForm_row_eq_zero hu)
  refine measure_mono_null (fun Z hZ => ?_) hnull
  simp only [Set.mem_setOf_eq] at hZ ⊢
  have h0 : mulVecE r n Z u = 0 := not_not.mp hZ
  rw [← ofLp_mulVecE, h0]
  simp

/-! ### Target 2: the expectation of `u` against itself -/

lemma inner_normalize_self {r : ℕ} {y : EuclideanSpace ℝ (Fin r)} (hy : y ≠ 0) :
    inner ℝ (normalize r y) (normalize r y) = 1 := by
  have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  simp only [normalize]
  calc inner ℝ (‖y‖⁻¹ • y) (‖y‖⁻¹ • y)
      = ‖y‖⁻¹ * (‖y‖⁻¹ * inner ℝ y y) := by
        rw [real_inner_smul_left, real_inner_smul_right]
    _ = 1 := by
        rw [real_inner_self_eq_norm_sq, pow_two]
        have hmul : ‖y‖⁻¹ * (‖y‖⁻¹ * (‖y‖ * ‖y‖))
            = (‖y‖⁻¹ * ‖y‖) * (‖y‖⁻¹ * ‖y‖) := by ring
        rw [hmul, inv_mul_cancel₀ hnorm, one_mul]

theorem grothendieckExpectation_self {r n : ℕ} (hr : 1 ≤ r) (u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) : grothendieckExpectation r n u u = 1 := by
  haveI hrow : ∀ _ : Fin n, IsProbabilityMeasure (gaussianReal 0 1) := fun _ => inferInstance
  haveI hpi : IsProbabilityMeasure (Measure.pi fun _ : Fin n => gaussianReal 0 1) := inferInstance
  haveI hcol : ∀ _ : Fin r, IsProbabilityMeasure
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := fun _ => hpi
  haveI hmat : IsProbabilityMeasure (gaussianMatrix r n) := by
    rw [gaussianMatrix]
    infer_instance
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have hae : ∀ᵐ Z ∂(gaussianMatrix r n), mulVecE r n Z u ≠ 0 := ae_mulVecE_ne_zero hr hu0
  have hcongr : (fun Z => inner ℝ (normalize r (mulVecE r n Z u))
        (normalize r (mulVecE r n Z u)))
      =ᵐ[gaussianMatrix r n] fun _ => (1 : ℝ) := by
    filter_upwards [hae] with Z hZ
    exact inner_normalize_self hZ
  have hone : ∫ _ : Fin r → Fin n → ℝ, (1 : ℝ) ∂(gaussianMatrix r n) = 1 := by
    rw [integral_const]
    have hprob : (gaussianMatrix r n).real Set.univ = 1 := by
      show ((gaussianMatrix r n) Set.univ).toReal = 1
      rw [measure_univ]
      simp
    rw [hprob, one_smul]
  rw [grothendieckExpectation, integral_congr_ae hcongr, hone]

end Grothendieck

open Grothendieck in
theorem solution {r n : ℕ} (hr : 1 ≤ r) {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) :
    ∀ᵐ Z ∂(gaussianMatrix r n), mulVecE r n Z u ≠ 0 :=
  ae_mulVecE_ne_zero hr hu
