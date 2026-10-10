-- Prove2me | solution 1 for MeasureTheory.integral_covector_trace_compl_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:07:25.737114+00:00
-- url     : https://prove2.me/submissions/720d74e3-3beb-4852-9f81-96d3a178445e

import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Function Metric
open scoped Topology
set_option maxHeartbeats 1200000

theorem solution {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (x : EuclideanSpace ℝ (Fin n))
    (hA : ∀ y, y ≠ x → ContDiffAt ℝ 1 A y)
    (hAc : HasCompactSupport A)
    (r : ℝ) (hr : 0 < r) :
    (∫ y in (ball x r)ᶜ, ∑ i : Fin n,
      fderiv ℝ A y (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      -(r ^ (n - 1)) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        A (x + r • ω.1) ω.1 ∂volume.toSphere := by
  classical
  let S := sphere (0 : (EuclideanSpace ℝ (Fin n))) 1
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let b : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let B : (EuclideanSpace ℝ (Fin n)) → ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := fun y => (1 - b y) • A y
  have hBc : HasCompactSupport B := by
    apply hAc.mono
    intro y hy
    by_contra h
    have hz : A y = 0 := notMem_support.mp h
    exact hy (by simp [B, hz])
  have hB : ContDiff ℝ 1 B := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = x
    · subst y
      have he : B =ᶠ[𝓝 x] 0 := by
        filter_upwards [b.eventuallyEq_one] with z hz
        simp [B, hz]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact (contDiffAt_const.sub b.contDiffAt).smul (hA y hy)
  have hBeq (y : (EuclideanSpace ℝ (Fin n))) (hy : r / 2 < dist y x) : B =ᶠ[𝓝 y] A := by
    have ho : {z : (EuclideanSpace ℝ (Fin n)) | r / 2 < dist z x} ∈ 𝓝 y :=
      (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hy
    filter_upwards [ho] with z hz
    simp [B, b.zero_of_le_dist hz.le]
  let d (i : Fin n) (y : (EuclideanSpace ℝ (Fin n))) := fderiv ℝ B y (e i) (e i)
  let g (i : Fin n) (y : (EuclideanSpace ℝ (Fin n))) := B y (e i)
  have hg (i : Fin n) : ContDiff ℝ 1 (g i) := hB.clm_apply contDiff_const
  have hgc (i : Fin n) : HasCompactSupport (g i) := by
    apply hBc.mono
    intro y hy
    by_contra h
    have hz : B y = 0 := notMem_support.mp h
    exact hy (by simp [g, hz])
  have hd (i : Fin n) : d i = fun y => fderiv ℝ (g i) y (e i) := by
    funext y
    simp [d, g, fderiv_clm_apply (hB.differentiable (by norm_num) y)
      (differentiableAt_const (e i))]
  have hdi (i : Fin n) : Integrable (d i) := by
    rw [hd]
    exact ((hg i).continuous_fderiv (by norm_num)).clm_apply continuous_const
      |>.integrable_of_hasCompactSupport ((hgc i).fderiv_apply ℝ (e i))
  have hzero (i : Fin n) : (∫ y, d i y) = 0 := by
    rw [hd]
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun _ : (EuclideanSpace ℝ (Fin n)) => (1 : ℝ)) (g := g i) (v := e i)
      (by simp) (by simpa [hd] using hdi i)
      (by simpa using (hg i).continuous.integrable_of_hasCompactSupport (hgc i))
      (fun _ _ => differentiableAt_const _) (fun y _ => (hg i).differentiable (by norm_num) y)
    simpa using h
  have hall : (∫ y, ∑ i : Fin n, d i y) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hdi i)]
    simp [hzero]
  have hsumint : Integrable (fun y => ∑ i : Fin n, d i y) :=
    integrable_finsetSum _ (fun i _ => hdi i)
  have hball (i : Fin n) : (∫ y in ball x r, d i y) =
      r ^ (n - 1) * ∫ ω : S, B (x + r • ω.1) (e i) * inner ℝ (e i) ω.1 ∂volume.toSphere := by
    rw [hd]
    exact integral_directional_derivative_ball hn hr
      (fun y _ => (hg i).contDiffAt) (e i)
  have hω (ω : S) : dist (x + r • ω.1) x = r := by
    simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp ω.2]
  have hboundary (i : Fin n) : Integrable
      (fun ω : S => B (x + r • ω.1) (e i) * inner ℝ (e i) ω.1) volume.toSphere := by
    have hc : Continuous (fun ω : S => B (x + r • ω.1) (e i) * inner ℝ (e i) ω.1) := by
      exact (((hB.continuous.clm_apply continuous_const).comp
        (show Continuous (fun ω : S => x + r • ω.1) by fun_prop))).mul (by fun_prop)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : (∫ y in ball x r, ∑ i : Fin n, d i y) =
      r ^ (n - 1) * ∫ ω : S, A (x + r • ω.1) ω.1 ∂volume.toSphere := by
    rw [integral_finsetSum _ (fun i _ => (hdi i).integrableOn)]
    simp_rw [hball]
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hboundary i)]
    congr 1
    apply integral_congr_ae (.of_forall _)
    intro ω
    have he := e.sum_repr' ω.1
    apply_fun B (x + r • ω.1) at he
    have heq := (hBeq (x + r • ω.1) (by rw [hω]; linarith)).eq_of_nhds
    simpa [map_sum, map_smul, smul_eq_mul, mul_comm, heq] using he
  have hs := integral_add_compl (s := ball x r) measurableSet_ball hsumint
  rw [hall, hb] at hs
  have hext : (∫ y in (ball x r)ᶜ, ∑ i : Fin n,
      fderiv ℝ A y (e i) (e i)) = ∫ y in (ball x r)ᶜ, ∑ i : Fin n, d i y := by
    apply setIntegral_congr_fun measurableSet_ball.compl
    intro y hy
    have hdist : r ≤ dist y x := le_of_not_gt hy
    have heq := (hBeq y (by linarith)).fderiv_eq (𝕜 := ℝ)
    simp only [d, heq]
  rw [hext]
  linarith
