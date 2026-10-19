-- Prove2me | solution 1 for MeasureTheory.integral_finite_halfSpace_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T13:44:30.731062+00:00
-- url     : https://prove2.me/submissions/54e0c25e-fb25-44bb-aaa9-38a69b8e57a5

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
set_option autoImplicit false

theorem solution {n N : ℕ} (i : Fin n) (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (f φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict {x | 0 < x i}))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x, (if 0 < x i then f x else
      ∑ j : Fin N, c j * f (WithLp.toLp 2
        (Function.update (fun k => x k) i (-b j * x i)))) * φ x) =
    ∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i},
      f x * (φ x + ∑ j : Fin N, (c j / b j) *
        φ (WithLp.toLp 2 (Function.update (fun k => x k) i (-(b j)⁻¹ * x i)))) := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x i}
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).measurableSet
  let e (j : Fin N) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans
      ((LinearEquiv.piCongrRight fun l : Fin n =>
        LinearEquiv.smulOfNeZero ℝ ℝ (if l = i then -b j else 1)
          (by split_ifs <;> simp [ne_of_gt (hb j)])).trans
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm)).toContinuousLinearEquiv
  have he (j : Fin N) (x : EuclideanSpace ℝ (Fin n)) (l : Fin n) :
      e j x l = (if l = i then -b j else 1) * x l := by
    by_cases hl : l = i <;>
      simp [e, LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfNeZero,
        LinearEquiv.smulOfUnit, hl]
  have heq (j : Fin N) (x : EuclideanSpace ℝ (Fin n)) :
      e j x = WithLp.toLp 2 (Function.update (fun k => x k) i (-b j * x i)) := by
    ext l
    by_cases hl : l = i <;> simp [he, hl]
  have hinv (j : Fin N) (x : EuclideanSpace ℝ (Fin n)) :
      (e j).symm x = WithLp.toLp 2
        (Function.update (fun k => x k) i (-(b j)⁻¹ * x i)) := by
    apply (e j).injective
    rw [(e j).apply_symm_apply]
    ext l
    by_cases hl : l = i
    · subst l
      simp [he, ne_of_gt (hb j)]
    · simp [he, hl]
  have hd (j : Fin N) : LinearMap.det (e j).toLinearEquiv.toLinearMap = -b j := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
    have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (e j).toLinearEquiv.toLinearMap =
        Matrix.diagonal (fun l => if l = i then -b j else 1) := by
      ext k l
      simp [LinearMap.toMatrix_apply, he, Matrix.diagonal_apply, eq_comm]
    rw [hm, Matrix.det_diagonal]
    simp
  have hm (j : Fin N) : Measure.map (e j) volume =
      ENNReal.ofReal (b j)⁻¹ • volume := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (e j).toLinearEquiv.isUnit_det'.ne_zero
    simpa [hd, abs_of_pos (hb j)] using h
  let A := H.indicator (fun x => f x * φ x)
  let B (j : Fin N) := H.indicator (fun x => f x * φ ((e j).symm x))
  have hA : Integrable A volume := (integrable_indicator_iff hH).2
    (hf.integrable_smul_right_of_hasCompactSupport hφ hcφ)
  have hB (j : Fin N) : Integrable (B j) volume := (integrable_indicator_iff hH).2
    (hf.integrable_smul_right_of_hasCompactSupport (hφ.comp (e j).symm.continuous)
      (hcφ.comp_homeomorph (e j).symm.toHomeomorph))
  have hBe (j : Fin N) : Integrable (fun x => B j (e j x)) volume := by
    have hmap : Integrable (B j) (Measure.map (e j) volume) := by
      rw [hm]
      exact (hB j).smul_measure ENNReal.ofReal_ne_top
    exact ((e j).toHomeomorph.measurableEmbedding.integrable_map_iff
      (g := B j) (μ := volume)).mp hmap
  have hI (j : Fin N) : (∫ x, B j (e j x)) = (b j)⁻¹ * ∫ x, B j x := by
    have hmap := (e j).toHomeomorph.measurableEmbedding.integral_map (μ := volume) (B j)
    change (∫ x, B j x ∂Measure.map (e j) volume) = (∫ x, B j (e j x)) at hmap
    rw [hm, integral_smul_measure] at hmap
    simpa [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (hb j))), smul_eq_mul]
      using hmap.symm
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (EuclideanSpace.proj i).toLinearMap
  have hker : L.ker ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single i (1 : ℝ) ∈ L.ker := by rw [h]; trivial
    simpa [L, LinearMap.mem_ker] using this
  have hnull : volume {x : EuclideanSpace ℝ (Fin n) | x i = 0} = 0 :=
    Measure.addHaar_submodule volume L.ker hker
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x i ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  have heqint : (fun x : EuclideanSpace ℝ (Fin n) =>
      (if 0 < x i then f x else ∑ j : Fin N, c j * f
        (WithLp.toLp 2 (Function.update (fun k => x k) i (-b j * x i)))) * φ x)
      =ᵐ[volume] (fun x => A x + ∑ j : Fin N, c j * B j (e j x)) := by
    filter_upwards [hae] with x hx
    by_cases hpos : 0 < x i
    · have hs (j : Fin N) : e j x ∉ H := by
        simp only [H, Set.mem_setOf_eq, he, ↓reduceIte]
        exact not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos (neg_neg_of_pos (hb j)) hpos))
      simp [A, B, H, hpos, Set.indicator_of_notMem (hs _)]
    · have hneg : x i < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
      have hs (j : Fin N) : e j x ∈ H := by
        simpa [H, he] using mul_pos_of_neg_of_neg (neg_neg_of_pos (hb j)) hneg
      have hxH : x ∉ H := hpos
      simp only [hpos, ↓reduceIte, A, Set.indicator_of_notMem hxH, zero_add]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [show B j (e j x) = f (e j x) * φ x by
        simp [B, Set.indicator_of_mem (hs j), (e j).symm_apply_apply]]
      rw [heq]
      ring
  rw [integral_congr_ae heqint,
    integral_add hA (integrable_finsetSum _ (fun j _ => (hBe j).const_mul (c j))),
    integral_finsetSum _ (fun j _ => (hBe j).const_mul (c j))]
  simp_rw [integral_const_mul, hI]
  have hright : H.indicator (fun x => f x * (φ x + ∑ j : Fin N,
      (c j / b j) * φ (WithLp.toLp 2
        (Function.update (fun k => x k) i (-(b j)⁻¹ * x i))))) =
      (fun x => A x + ∑ j : Fin N, (c j / b j) * B j x) := by
    funext x
    by_cases hx : x ∈ H
    · simp [A, B, Set.indicator_of_mem hx, hinv, mul_add, Finset.mul_sum,
        mul_left_comm, mul_assoc]
    · simp [A, B, Set.indicator_of_notMem hx]
  rw [← integral_indicator hH, hright,
    integral_add hA (integrable_finsetSum _ (fun j _ => (hB j).const_mul (c j / b j))),
    integral_finsetSum _ (fun j _ => (hB j).const_mul (c j / b j))]
  simp_rw [integral_const_mul, div_eq_mul_inv, mul_assoc]
