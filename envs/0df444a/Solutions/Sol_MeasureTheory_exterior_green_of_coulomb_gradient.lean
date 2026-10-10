-- Prove2me | solution 1 for MeasureTheory.exterior_green_of_coulomb_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:18:46.038752+00:00
-- url     : https://prove2.me/submissions/0581d353-2691-4e1d-a443-93f02049c5a4

import Theorems.Thm_MeasureTheory_integral_covector_trace_compl_ball
import Theorems.Thm_InnerProductSpace_coulomb_covector_trace_eq_zero
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Metric Function
open scoped ContDiff Topology
open Laplacian HunterPDE.Harmonic
set_option maxHeartbeats 1200000

theorem solution (n : ℕ) (hn : 2 ≤ n) (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : ContDiffOn ℝ ∞ K {0}ᶜ) (c : ℝ)
    (hDK : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ∀ i : Fin n,
      fderiv ℝ K z (EuclideanSpace.single i 1) =
        c * (1 / ‖z‖ ^ (n - 1)) * (z i / ‖z‖))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 < r) (κ : ℝ)
    (hκ : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ = r → K z = κ) :
    (∫ y in (ball x r)ᶜ, K (x - y) * (Δ f) y) =
      -κ * (∫ y in ball x r, (Δ f) y) +
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * c) *
          sphereAverage f x r := by
  classical
  let S := sphere (0 : (EuclideanSpace ℝ (Fin n))) 1
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let Q : (EuclideanSpace ℝ (Fin n)) → ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := fun z => (c / ‖z‖ ^ n) • innerSL ℝ z
  let A : (EuclideanSpace ℝ (Fin n)) → ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := fun y =>
    K (x - y) • fderiv ℝ f y + f y • Q (x - y)
  have hn0 : 0 < n := by omega
  have hpow (t : ℝ) : t ^ n = t ^ (n - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hn0]
  have hKat (z : (EuclideanSpace ℝ (Fin n))) (hz : z ≠ 0) : ContDiffAt ℝ 1 K z :=
    (hK.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hz))).of_le (by simp)
  have hQat (z : (EuclideanSpace ℝ (Fin n))) (hz : z ≠ 0) : ContDiffAt ℝ 1 Q z := by
    exact (contDiffAt_const.div ((contDiffAt_id.norm ℝ hz).pow n)
      (pow_ne_zero n (norm_ne_zero_iff.mpr hz))).smul
        (innerSL ℝ (E := (EuclideanSpace ℝ (Fin n)))).contDiff.contDiffAt
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hA (y : (EuclideanSpace ℝ (Fin n))) (hy : y ≠ x) : ContDiffAt ℝ 1 A y := by
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
    exact ((hKat _ hz).comp y (contDiffAt_const.sub contDiffAt_id)).smul hDf.contDiffAt
      |>.add (hf.contDiffAt.of_le (by norm_num) |>.smul
        ((hQat _ hz).comp y (contDiffAt_const.sub contDiffAt_id)))
  have hAc : HasCompactSupport A := by
    apply hfc.mono'
    intro y hy
    by_contra hyf
    have hf0 : f y = 0 := notMem_support.mp (fun hm => hyf (subset_tsupport f hm))
    have hdf0 : fderiv ℝ f y = 0 := fderiv_of_notMem_tsupport ℝ hyf
    exact hy (by simp [A, hf0, hdf0])
  have hKD (z : (EuclideanSpace ℝ (Fin n))) (hz : z ≠ 0) (i : Fin n) :
      fderiv ℝ K z (e i) = Q z (e i) := by
    change fderiv ℝ K z (EuclideanSpace.basisFun (Fin n) ℝ i) = _
    rw [EuclideanSpace.basisFun_apply]
    rw [hDK z hz i]
    change c * (1 / ‖z‖ ^ (n - 1)) * (z i / ‖z‖) =
      (c / ‖z‖ ^ n) * inner ℝ z (EuclideanSpace.single i 1)
    rw [← EuclideanSpace.basisFun_apply, EuclideanSpace.inner_basisFun_real, hpow]
    field_simp [norm_ne_zero_iff.mpr hz]
  have hdiv (y : (EuclideanSpace ℝ (Fin n))) (hy : y ≠ x) :
      (∑ i : Fin n, fderiv ℝ A y (e i) (e i)) = K (x - y) * (Δ f) y := by
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
    have hks : DifferentiableAt ℝ (fun t : (EuclideanSpace ℝ (Fin n)) => K (x - t)) y :=
      ((hKat _ hz).differentiableAt (by norm_num)).comp y
        ((differentiableAt_const x).sub differentiableAt_id)
    have hqs : DifferentiableAt ℝ (fun t : (EuclideanSpace ℝ (Fin n)) => Q (x - t)) y :=
      ((hQat _ hz).differentiableAt (by norm_num)).comp y
        ((differentiableAt_const x).sub differentiableAt_id)
    have hs : fderiv ℝ (fun t : EuclideanSpace ℝ (Fin n) => x - t) y =
        -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      simpa using ((hasFDerivAt_id y).const_sub x).fderiv
    have hdi (i : Fin n) : fderiv ℝ A y (e i) (e i) =
        K (x - y) * fderiv ℝ (fderiv ℝ f) y (e i) (e i) -
          f y * fderiv ℝ Q (x - y) (e i) (e i) := by
      dsimp only [A]
      rw [fderiv_fun_add
        (f := fun t => K (x - t) • fderiv ℝ f t)
        (g := fun t => f t • Q (x - t))
        (hks.smul (hDf.differentiable (by norm_num) y))
        ((hf.differentiable (by norm_num) y).smul hqs),
        fderiv_fun_smul hks (hDf.differentiable (by norm_num) y),
        fderiv_fun_smul (hf.differentiable (by norm_num) y) hqs]
      rw [fderiv_fun_comp (f := fun t => x - t) (g := K) y ((hKat _ hz).differentiableAt (by norm_num))
        ((differentiableAt_const x).sub differentiableAt_id),
        fderiv_fun_comp (f := fun t => x - t) (g := Q) y ((hQat _ hz).differentiableAt (by norm_num))
        ((differentiableAt_const x).sub differentiableAt_id)]
      rw [hs]
      simp only [add_apply,
        smul_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg, smul_eq_mul, hKD _ hz i]
      ring
    simp_rw [hdi]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hq := InnerProductSpace.coulomb_covector_trace_eq_zero n hn c (x - y) hz
    change (∑ i : Fin n, fderiv ℝ Q (x - y) (e i) (e i)) = 0 at hq
    rw [hq, mul_zero, sub_zero]
    congr 1
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f e,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hflux := MeasureTheory.integral_covector_trace_compl_ball hn0 A x hA hAc r hr
  have hext : (∫ y in (ball x r)ᶜ, K (x - y) * (Δ f) y) =
      ∫ y in (ball x r)ᶜ, ∑ i : Fin n, fderiv ℝ A y (e i) (e i) := by
    apply setIntegral_congr_fun measurableSet_ball.compl
    intro y hy
    exact (hdiv y (by intro h; subst y; exact hy (mem_ball_self hr))).symm
  rw [hext, hflux]
  have hnorm (w : S) : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
  have hz (w : S) : x - (x + r • w.1) = -r • w.1 := by
    simp [neg_smul]
  have hrad (w : S) : ‖x - (x + r • w.1)‖ = r := by
    rw [hz]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hnorm]
  have hbound (w : S) : A (x + r • w.1) w.1 =
      κ * fderiv ℝ f (x + r • w.1) w.1 -
        (c / r ^ (n - 1)) * f (x + r • w.1) := by
    simp only [A, add_apply, smul_apply, smul_eq_mul]
    rw [hκ _ (hrad w)]
    simp only [Q, smul_apply, smul_eq_mul, hrad, innerSL_apply_apply]
    rw [hz]
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm, one_pow, mul_one]
    rw [hpow]
    field_simp [hr.ne']
    ring
  have hfi : Integrable (fun w : S => f (x + r • w.1)) volume.toSphere :=
    (hf.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdi : Integrable (fun w : S => fderiv ℝ f (x + r • w.1) w.1) volume.toSphere :=
    ((hDf.continuous.comp (by fun_prop)).clm_apply (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : (∫ w : S, A (x + r • w.1) w.1 ∂volume.toSphere) =
      κ * (∫ w : S, fderiv ℝ f (x + r • w.1) w.1 ∂volume.toSphere) -
        (c / r ^ (n - 1)) * ∫ w : S, f (x + r • w.1) ∂volume.toSphere := by
    simp_rw [hbound]
    rw [integral_sub (hdi.const_mul κ) (hfi.const_mul _), integral_const_mul, integral_const_mul]
  rw [hb]
  have hα : volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1) ≠ 0 := by
    rw [measureReal_ne_zero_iff measure_ball_lt_top.ne]
    exact (measure_ball_pos volume (0 : (EuclideanSpace ℝ (Fin n))) zero_lt_one).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hmass : (volume.toSphere : Measure S).real univ =
      (n : ℝ) * volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1) := by simp
  have hvol : volume.real (ball x r) = r ^ n * volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    simp [measureReal_def]
  have hball : r ^ (n - 1) * (∫ w : S,
      fderiv ℝ f (x + r • w.1) w.1 ∂volume.toSphere) = ∫ y in ball x r, (Δ f) y := by
    have h := sphereAverage_radial_eq_ball_laplacian (u := f) (x := x) hn0 hr
      (fun y _ => hf.contDiffAt)
    rw [average_eq, setAverage_eq, hmass, hvol, hpow] at h
    simp only [smul_eq_mul] at h
    field_simp [hnR, hα, hr.ne'] at h
    nlinarith [h]
  have havg : sphereAverage f x r =
      ((n : ℝ) * volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1))⁻¹ *
        ∫ w : S, f (x + r • w.1) ∂volume.toSphere := by
    unfold sphereAverage
    rw [average_eq, hmass]
    rfl
  rw [havg]
  calc
    _ = -κ * (r ^ (n - 1) * (∫ w : S,
        fderiv ℝ f (x + r • w.1) w.1 ∂volume.toSphere)) +
        c * (∫ w : S, f (x + r • w.1) ∂volume.toSphere) := by
      field_simp [hr.ne']
      ring
    _ = _ := by
      rw [hball]
      field_simp [hnR, hα]
