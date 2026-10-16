-- Prove2me | solution 1 for MeasureTheory.integral_signed_coordinate_fold
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T18:20:24.874494+00:00
-- url     : https://prove2.me/submissions/5e28400e-608d-4fee-895f-4a739c7d0e62

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
set_option autoImplicit false

theorem solution (n : ℕ) (i : Fin n) (c : ℝ)
    (f φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict {x | 0 < x i}))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      (if x i < 0 then c * f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))
       else f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))) * φ x) =
    ∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i},
      f x * (φ x + c * φ (WithLp.toLp 2 (fun j => if j = i then -x j else x j))) := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x i}
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).measurableSet
  let S : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
      if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hS (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
      S x j = if j = i then -x j else x j := by
    by_cases hj : j = i <;> simp [S, LinearIsometryEquiv.piLpCongrRight_apply, hj]
  have hSS (x : EuclideanSpace ℝ (Fin n)) : S (S x) = x := by
    ext j
    by_cases hj : j = i <;> simp [hS, hj]
  have hA : Integrable (H.indicator (fun x => f x * φ x)) volume := by
    apply (integrable_indicator_iff hH).2
    exact hf.integrable_smul_right_of_hasCompactSupport hφ hcφ
  have hB : Integrable (H.indicator (fun x => f x * φ (S x))) volume := by
    apply (integrable_indicator_iff hH).2
    exact hf.integrable_smul_right_of_hasCompactSupport (hφ.comp S.continuous)
      (hcφ.comp_homeomorph S.toHomeomorph)
  let A := H.indicator (fun x => f x * φ x)
  let B := H.indicator (fun x => f x * φ (S x))
  have hBS : Integrable (fun x => B (S x)) volume :=
    S.measurePreserving.integrable_comp_of_integrable hB
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (EuclideanSpace.proj i).toLinearMap
  have hker : L.ker ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single i (1 : ℝ) ∈ L.ker := by rw [h]; trivial
    simp [L, LinearMap.mem_ker] at this
  have hnull : volume {x : EuclideanSpace ℝ (Fin n) | x i = 0} = 0 :=
    Measure.addHaar_submodule volume L.ker hker
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x i ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  have heq : (fun x : EuclideanSpace ℝ (Fin n) =>
      (if x i < 0 then c * f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))
       else f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))) * φ x) =ᵐ[volume]
      (fun x => A x + c * B (S x)) := by
    filter_upwards [hae] with x hx
    by_cases hpos : 0 < x i
    · have hxH : x ∈ H := hpos
      have hsH : S x ∉ H := by simp [H, hS, not_lt.mpr (le_of_lt hpos)]
      have hfold : WithLp.toLp 2 (fun j => if j = i then |x j| else x j) = x := by
        ext j
        by_cases hj : j = i
        · subst j; simp [abs_of_pos hpos]
        · simp [hj]
      simp [A, B, Set.indicator_of_mem hxH, Set.indicator_of_notMem hsH,
        hfold, not_lt.mpr (le_of_lt hpos)]
    · have hneg : x i < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
      have hxH : x ∉ H := hpos
      have hsH : S x ∈ H := by simpa [H, hS] using neg_pos.mpr hneg
      have hfold : WithLp.toLp 2 (fun j => if j = i then |x j| else x j) = S x := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hS, abs_of_neg hneg]
        · simp [hj, hS]
      simp [A, B, Set.indicator_of_notMem hxH, Set.indicator_of_mem hsH,
        hfold, hneg, hSS, mul_assoc]
  rw [integral_congr_ae heq, integral_add hA (hBS.const_mul c), integral_const_mul,
    S.measurePreserving.integral_comp S.toHomeomorph.measurableEmbedding B]
  rw [show (∫ x, A x) = ∫ x in H, f x * φ x from integral_indicator hH,
    show (∫ x, B x) = ∫ x in H, f x * φ (S x) from integral_indicator hH]
  rw [← integral_const_mul, ← integral_add
    ((integrable_indicator_iff hH).1 hA) (((integrable_indicator_iff hH).1 hB).const_mul c)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hs : S x = WithLp.toLp 2 (fun j => if j = i then -x j else x j) := by
    ext j; exact hS x j
  simp only [hs]
  ring
