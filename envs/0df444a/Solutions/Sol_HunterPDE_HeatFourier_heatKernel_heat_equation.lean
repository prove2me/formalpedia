-- Prove2me | solution 1 for HunterPDE.HeatFourier.heatKernel_heat_equation
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:03:19.792495+00:00
-- url     : https://prove2.me/submissions/6cbde683-da25-4ec9-aacc-34d57f57c1ae

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_HeatKernel

open Set Filter Topology
open scoped ContDiff Laplacian RealInnerProductSpace

namespace HeatAux

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hasFDerivAt_gauss (a : ℝ) (y : F) :
    HasFDerivAt (fun y : F => Real.exp (-a * ‖y‖ ^ 2))
      ((-(2 * a) * Real.exp (-a * ‖y‖ ^ 2)) • innerSL ℝ y) y := by
  have h1 : HasFDerivAt (fun y : F => ‖y‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 := (h1.const_mul (-a)).exp
  convert h2 using 1
  ext v
  simp [two_smul]
  ring

lemma fderiv_gauss (a : ℝ) :
    fderiv ℝ (fun y : F => Real.exp (-a * ‖y‖ ^ 2)) =
      fun y => (-(2 * a) * Real.exp (-a * ‖y‖ ^ 2)) • innerSL ℝ y := by
  funext y
  exact (hasFDerivAt_gauss a y).fderiv

lemma iteratedFDeriv_two_gauss (a : ℝ) (x v : F) :
    iteratedFDeriv ℝ 2 (fun y : F => Real.exp (-a * ‖y‖ ^ 2)) x ![v, v] =
      Real.exp (-a * ‖x‖ ^ 2) * (4 * a ^ 2 * ⟪x, v⟫ ^ 2 - 2 * a * ‖v‖ ^ 2) := by
  rw [iteratedFDeriv_two_apply, fderiv_gauss]
  have hc : HasFDerivAt (fun y : F => -(2 * a) * Real.exp (-a * ‖y‖ ^ 2))
      ((-(2 * a)) • ((-(2 * a) * Real.exp (-a * ‖x‖ ^ 2)) • innerSL ℝ x)) x := by
    have := (hasFDerivAt_gauss a x).const_mul (-(2 * a))
    exact this
  have hf : HasFDerivAt (fun y : F => innerSL ℝ y) (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ) x :=
    (innerSL ℝ (E := F)).hasFDerivAt
  have hs : HasFDerivAt (fun y : F => (-(2 * a) * Real.exp (-a * ‖y‖ ^ 2)) • innerSL ℝ y) _ x :=
    hc.smul hf
  rw [hs.fderiv]
  have hvv : (innerSL ℝ v) v = ‖v‖ ^ 2 := by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  simp [hvv]
  ring


lemma contDiffOn_heatKernel (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) × ℝ => HunterPDE.HeatFourier.heatKernel n z.1 z.2)
      (Set.univ ×ˢ Set.Ioi 0) := by
  unfold HunterPDE.HeatFourier.heatKernel
  intro z hz
  have hz2 : 0 < z.2 := hz.2
  have hne : (4 * Real.pi * z.2) ≠ 0 := by positivity
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.mul
  · apply ContDiffAt.div contDiffAt_const
    · apply ContDiffAt.rpow_const_of_ne
      · fun_prop
      · exact hne
    · positivity
  · have hq : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) × ℝ => -‖z.1‖ ^ 2 / (4 * z.2)) z := by
      apply ContDiffAt.div
      · exact ((contDiff_norm_sq ℝ).contDiffAt.comp z contDiffAt_fst).neg
      · fun_prop
      · positivity
    exact Real.contDiff_exp.contDiffAt.comp z hq

lemma laplacian_gauss (n : ℕ) (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Δ (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-a * ‖y‖ ^ 2)) x =
      Real.exp (-a * ‖x‖ ^ 2) * (4 * a ^ 2 * ‖x‖ ^ 2 - 2 * a * n) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_gauss]
  have hb := (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    OrthonormalBasis.sum_sq_inner_left]
  have hn : ∑ i, ‖(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i‖ ^ 2 = (n : ℝ) := by
    simp [(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))).orthonormal.1]
  rw [hn]

lemma hasDerivAt_heatKernel_t (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => HunterPDE.HeatFourier.heatKernel n x s)
      (HunterPDE.HeatFourier.heatKernel n x t * (‖x‖ ^ 2 / (4 * t ^ 2) - n / (2 * t))) t := by
  unfold HunterPDE.HeatFourier.heatKernel
  have hA : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ ((n : ℝ) / 2))
      (4 * Real.pi * ((n : ℝ) / 2) * (4 * Real.pi * t) ^ ((n : ℝ) / 2 - 1)) t := by
    have h1 : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    have := h1.rpow_const (p := (n : ℝ) / 2) (Or.inl (by positivity))
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have hE : HasDerivAt (fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s)))
      (Real.exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) t := by
    have h1 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul 4
    have h2 := (h1.inv (by positivity)).const_mul (-‖x‖ ^ 2)
    have h3 := h2.exp
    have hf : (fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s))) =
        fun s : ℝ => Real.exp (-‖x‖ ^ 2 * (4 * s)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hf]
    refine h3.congr_deriv ?_
    have : (4 * t) ≠ 0 := by positivity
    have e : ((fun s : ℝ => 4 * s)⁻¹ t) = (4 * t)⁻¹ := rfl
    rw [e]
    simp only [div_eq_mul_inv]
    field_simp
  have hAne : (4 * Real.pi * t) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have h := (hA.inv hAne).mul hE
  have hf : (fun s : ℝ => 1 / (4 * Real.pi * s) ^ ((n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s))) =
      (fun s : ℝ => (4 * Real.pi * s) ^ ((n : ℝ) / 2))⁻¹ *
        fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s)) := by
    funext s; simp [one_div]
  rw [hf]
  refine h.congr_deriv ?_
  have hr : (4 * Real.pi * t) ^ ((n : ℝ) / 2 - 1) =
      (4 * Real.pi * t) ^ ((n : ℝ) / 2) / (4 * Real.pi * t) := by
    rw [Real.rpow_sub_one (by positivity)]
  simp only [hr, Pi.inv_apply]
  field_simp
  ring

lemma laplacian_heatKernel (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    Δ (fun y : EuclideanSpace ℝ (Fin n) => HunterPDE.HeatFourier.heatKernel n y t) x =
      HunterPDE.HeatFourier.heatKernel n x t * (‖x‖ ^ 2 / (4 * t ^ 2) - n / (2 * t)) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => HunterPDE.HeatFourier.heatKernel n y t) =
      (1 / (4 * Real.pi * t) ^ ((n : ℝ) / 2)) • (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-(1 / (4 * t)) * ‖y‖ ^ 2)) := by
    funext y
    simp only [HunterPDE.HeatFourier.heatKernel, Pi.smul_apply, smul_eq_mul]
    congr 2
    field_simp
  rw [hfun]
  have hcd : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(1 / (4 * t)) * ‖y‖ ^ 2)) x := by
    apply (Real.contDiff_exp.contDiffAt.comp x _)
    exact (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt
  rw [InnerProductSpace.laplacian_smul _ hcd, laplacian_gauss]
  simp only [HunterPDE.HeatFourier.heatKernel, smul_eq_mul]
  have : -‖x‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖x‖ ^ 2 := by field_simp
  rw [this]
  field_simp
  ring

end HeatAux

theorem solution (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      HunterPDE.HeatFourier.heatKernel n z.1 z.2) (Set.univ ×ˢ Set.Ioi 0) ∧
    ∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      deriv (fun s : ℝ => HunterPDE.HeatFourier.heatKernel n x s) t =
        Δ (fun y => HunterPDE.HeatFourier.heatKernel n y t) x := by
  refine ⟨HeatAux.contDiffOn_heatKernel n, fun x t ht => ?_⟩
  rw [(HeatAux.hasDerivAt_heatKernel_t n x ht).deriv, HeatAux.laplacian_heatKernel n x ht]
