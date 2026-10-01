-- Prove2me | solution 1 for NonsmoothNewton.AugLagrangian.eta_C1_grad_locLip
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:39:24.128005+00:00
-- url     : https://prove2.me/submissions/10d8d615-e9e1-41ad-8d19-fd45fed61d90

import Mathlib
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

open Filter Topology

namespace NonsmoothNewton.AugLagrangian

private theorem positive_sq_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max 0 y)^2) (2 * max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : (fun y : ℝ => (max 0 y)^2) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [max_eq_left hy.le]
    simpa [max_eq_left hx.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · rw [show 2 * max (0 : ℝ) 0 = 0 by norm_num, hasDerivAt_iff_tendsto_slope]
    have heq : slope (fun y : ℝ => (max 0 y)^2) 0 = fun y => max 0 y := by
      funext y
      rw [slope_fun_def_field]
      by_cases hy : 0 ≤ y
      · simp [max_eq_right hy, pow_two, mul_div_cancel_right₀]
      · simp [max_eq_left (le_of_not_ge hy)]
    rw [heq]
    simpa using ((show Continuous (fun y : ℝ => max 0 y) by fun_prop).continuousAt (x := 0)).tendsto.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · have heq : (fun y : ℝ => (max 0 y)^2) =ᶠ[𝓝 x] fun y => y^2 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp [max_eq_right hy.le]
    simpa [max_eq_right hx.le] using ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq heq

private theorem positive_sq_C1 : ContDiff ℝ 1 (fun y : ℝ => (max 0 y)^2) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (positive_sq_deriv x).differentiableAt, ?_⟩
  have heq : deriv (fun y : ℝ => (max 0 y)^2) = fun x => 2 * max 0 x :=
    funext fun x => (positive_sq_deriv x).deriv
  rw [heq]
  fun_prop

private theorem eta_max {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    eta r g = fun z => ((max 0 (z.2 + r * g z.1))^2 - z.2^2) / (2*r) := by
  funext z
  unfold eta phi
  split_ifs with h
  · rw [max_eq_right h]
    field_simp
    <;> ring
  · rw [max_eq_left (le_of_not_ge h)]
    field_simp
    <;> ring

private theorem eta_C1 {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (eta r g) := by
  rw [eta_max r hr g]
  exact ((positive_sq_C1.comp (contDiff_snd.add
    (contDiff_const.mul ((hg.of_le (by norm_num)).comp contDiff_fst)))).sub
    (contDiff_snd.pow 2)).div_const (2*r)

private theorem eta_deriv {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (eta r g) z =
      max 0 (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      ((max 0 (z.2 + r * g z.1) - z.2) / r) •
        ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  have hdg := ((hg.differentiable (by norm_num)) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hdt := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add (hdg.const_mul r)
  have hdp := (positive_sq_deriv (z.2 + r * g z.1)).comp_hasFDerivAt z hdt
  have hd := (hdp.sub ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).pow 2)).mul_const ((2*r)⁻¹)
  rw [eta_max r hr g]
  simp only [div_eq_mul_inv]
  simp only [Function.comp_def, Pi.add_apply, Pi.sub_apply] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst, ContinuousLinearMap.coe_snd, smul_eq_mul]
  norm_num
  field_simp
  <;> ring

private theorem eta_deriv_pos {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : 0 ≤ z.2 + r * g z.1) :
    fderiv ℝ (eta r g) z =
      (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      g z.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  rw [eta_deriv r hr g hg z, max_eq_right hz]
  congr 2
  field_simp
  <;> ring

private theorem eta_deriv_neg {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : z.2 + r * g z.1 ≤ 0) :
    fderiv ℝ (eta r g) z =
      (-(z.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  simp [eta_deriv r hr g hg z, max_eq_left hz, neg_div]

private theorem eta_locLip {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g) :
    LocallyLipschitz (fun z => fderiv ℝ (eta r g) z) := by
  let E := EuclideanSpace ℝ (Fin n)
  let P : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let S : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  have hgd : ContDiff ℝ 1 (fun z : E × ℝ => (fderiv ℝ g z.1).comp P) :=
    ((hg.fderiv_right (by norm_num)).comp contDiff_fst).clm_comp contDiff_const
  have ht : ContDiff ℝ 1 (fun z : E × ℝ => z.2 + r * g z.1) := by
    exact contDiff_snd.add (contDiff_const.mul ((hg.of_le (by norm_num)).comp contDiff_fst))
  have hout : ContDiff ℝ 1
      (fun p : ℝ × (((E × ℝ) →L[ℝ] ℝ) × ℝ) =>
        p.1 • p.2.1 + ((p.1 - p.2.2) / r) • S) := by fun_prop
  have hcomb := hout.locallyLipschitz.comp
    ((ht.locallyLipschitz.const_max 0).prodMk
      (hgd.locallyLipschitz.prodMk
        (show ContDiff ℝ 1 (fun z : E × ℝ => z.2) from contDiff_snd).locallyLipschitz))
  have heq : (fun z => fderiv ℝ (eta r g) z) = fun z =>
      max 0 (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp P +
      ((max 0 (z.2 + r * g z.1) - z.2) / r) • S :=
    funext (eta_deriv r hr g hg)
  rw [heq]
  exact hcomb



theorem _root_.solution {n : ℕ} (r : ℝ) (hr : 0 < r) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (eta r g) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, 0 ≤ z.2 + r * g z.1 →
      fderiv ℝ (eta r g) z =
        (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
            (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
          + g z.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, z.2 + r * g z.1 ≤ 0 →
      fderiv ℝ (eta r g) z =
        (-(z.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    LocallyLipschitz (fun z => fderiv ℝ (eta r g) z) := by
  exact ⟨eta_C1 r hr g hg, eta_deriv_pos r hr g hg, eta_deriv_neg r hr g hg, eta_locLip r hr g hg⟩

end NonsmoothNewton.AugLagrangian
