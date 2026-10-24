-- Prove2me | solution 1 for K24.Global.common_circle_haar_projection_identities
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:40:04.636546+00:00
-- url     : https://prove2.me/submissions/9ff6df4f-02d8-47ae-9837-8228c05af617

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 1000
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

local instance tangentNormedAddCommGroup (p : M) : NormedAddCommGroup (TangentSpace I4 p) :=
  inferInstanceAs (NormedAddCommGroup FourSpace)
local instance tangentNormedSpace (p : M) : NormedSpace ℝ (TangentSpace I4 p) :=
  inferInstanceAs (NormedSpace ℝ FourSpace)
local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) :=
  inferInstanceAs (FiniteDimensional ℝ FourSpace)
local instance tangentCompleteSpace (p : M) : CompleteSpace (TangentSpace I4 p) :=
  inferInstanceAs (CompleteSpace FourSpace)

instance circleHaar_isMulLeftInvariant : circleHaar.IsMulLeftInvariant := by
  unfold circleHaar
  infer_instance

theorem circleAction_smooth_slice (rho : CircleAction M) (t : Circle) :
    ContMDiff I4 I4 ∞ (rho.act t) :=
  rho.smooth.comp (contMDiff_const.prodMk contMDiff_id)

theorem circleAction_deriv_mul (rho : CircleAction M) (s t : Circle) (p : M) :
    mfderiv I4 I4 (rho.act (s * t)) p =
      (mfderiv I4 I4 (rho.act s) (rho.act t p)).comp
        (mfderiv I4 I4 (rho.act t) p) := by
  have heq : rho.act (s * t) = rho.act s ∘ rho.act t := funext (rho.mul_act s t)
  rw [heq]
  exact mfderiv_comp p ((circleAction_smooth_slice rho s).mdifferentiable (by simp) _)
    ((circleAction_smooth_slice rho t).mdifferentiable (by simp) _)

theorem actionPullbackCov2_mul (rho : CircleAction M) (s t : Circle) (u : RawCov2 M) :
    actionPullbackCov2 rho (s * t) u =
      actionPullbackCov2 rho t (actionPullbackCov2 rho s u) := by
  ext p v w
  simp only [actionPullbackCov2, pullbackCov2, bilinearPullback_apply,
    circleAction_deriv_mul, ContinuousLinearMap.comp_apply, rho.mul_act]
  change u (rho.act (s * t) p) _ _ = _
  rw [rho.mul_act]
  rfl

theorem actionPullbackCovector_mul (rho : CircleAction M) (s t : Circle)
    (u : RawCovector M) :
    actionPullbackCovector rho (s * t) u =
      actionPullbackCovector rho t (actionPullbackCovector rho s u) := by
  ext p v
  simp only [actionPullbackCovector, pullbackCovector,
    circleAction_deriv_mul, ContinuousLinearMap.comp_apply, rho.mul_act]
  rw [rho.mul_act]
  rfl

theorem actionPullbackVector_mul (rho : CircleAction M) (s t : Circle) (Y : RawVector M) :
    actionPullbackVector rho (s * t) Y =
      actionPullbackVector rho t (actionPullbackVector rho s Y) := by
  funext p
  change mfderiv I4 I4 (rho.act ((s * t)⁻¹)) (rho.act (s * t) p) (Y (rho.act (s * t) p)) = _
  rw [mul_inv_rev, circleAction_deriv_mul]
  change mfderiv I4 I4 (rho.act t⁻¹) (rho.act s⁻¹ (rho.act (s * t) p))
    (mfderiv I4 I4 (rho.act s⁻¹) (rho.act (s * t) p) (Y (rho.act (s * t) p))) = _
  rw [rho.mul_act]
  have h : rho.act s⁻¹ (rho.act s (rho.act t p)) = rho.act t p := by
    rw [← rho.mul_act, inv_mul_cancel, rho.one_act]
  rw [h]
  rfl

def cov2ReconstructCLM (c p : M) : Mat4 →L[ℝ]
    (TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := cov2FromChartAt c p
    map_add' := by
      intro a b
      ext v w
      simp [cov2FromChartAt, matrixToBilinear, add_mul, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext v w
      simp [cov2FromChartAt, matrixToBilinear, Finset.mul_sum, mul_left_comm, mul_assoc] }

def covectorReconstructCLM (c p : M) : (Fin 4 → ℝ) →L[ℝ]
    (TangentSpace I4 p →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := covectorFromChartAt c p
    map_add' := by
      intro a b
      ext v
      simp [covectorFromChartAt, coefficientsToCovector, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext v
      simp [covectorFromChartAt, coefficientsToCovector, Finset.mul_sum, mul_left_comm, mul_assoc] }

def vectorReconstructCLM (c p : M) : (Fin 4 → ℝ) →L[ℝ] TangentSpace I4 p :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
      (∑ i : Fin 4, a i • basisVector i)
    map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }

variable [IsManifold I4 ∞ M]

theorem vector_chart_recovery (Y : RawVector M) (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) :
    vectorReconstructCLM c p (fun i => vectorInChart Y c (chartAt FourSpace c p) i) = Y p := by
  change mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
    (∑ i, vectorInChart Y c (chartAt FourSpace c p) i • basisVector i) = Y p
  rw [sum_basisVector]
  dsimp only [vectorInChart]
  rw [(chartAt FourSpace c).left_inv hp]
  exact congrArg (fun A => A (Y p)) ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hp)


theorem Cov2HaarIntegrable.fiber {rho : CircleAction M} {u : RawCov2 M}
    (hu : Cov2HaarIntegrable rho u) (p : M) :
    Integrable (fun t => actionPullbackCov2 rho t u p) circleHaar := by
  have hc : Integrable (fun t => cov2InChart (actionPullbackCov2 rho t u)
      p (chartAt FourSpace p p)) circleHaar :=
    Integrable.of_eval (fun i => Integrable.of_eval (hu p _
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)) i))
  have hr : ∀ t, cov2ReconstructCLM p p
      (cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p)) =
      actionPullbackCov2 rho t u p := fun t =>
    cov2_chart_recovery _ p p (mem_chart_source FourSpace p)
  simpa only [hr] using (cov2ReconstructCLM p p).integrable_comp hc

theorem CovectorHaarIntegrable.fiber {rho : CircleAction M} {u : RawCovector M}
    (hu : CovectorHaarIntegrable rho u) (p : M) :
    Integrable (fun t => actionPullbackCovector rho t u p) circleHaar := by
  have hc : Integrable (fun t => covectorInChart (actionPullbackCovector rho t u)
      p (chartAt FourSpace p p)) circleHaar :=
    Integrable.of_eval (hu p _
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)))
  have hr : ∀ t, covectorReconstructCLM p p
      (covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p)) =
      actionPullbackCovector rho t u p := fun t =>
    covector_chart_recovery _ p p (mem_chart_source FourSpace p)
  simpa only [hr] using (covectorReconstructCLM p p).integrable_comp hc

theorem VectorHaarIntegrable.fiber {rho : CircleAction M} {Y : RawVector M}
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    Integrable (fun t => actionPullbackVector rho t Y p) circleHaar := by
  have hc : Integrable (fun t i => vectorInChart (actionPullbackVector rho t Y)
      p (chartAt FourSpace p p) i) circleHaar :=
    Integrable.of_eval (hY p _
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)))
  have hr : ∀ t, vectorReconstructCLM p p
      (fun i => vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i) =
      actionPullbackVector rho t Y p := fun t =>
    vector_chart_recovery _ p p (mem_chart_source FourSpace p)
  simpa only [hr] using (vectorReconstructCLM p p).integrable_comp hc

theorem cov2Pi0_eq_fiberIntegral (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (p : M) :
    cov2Pi0 rho u p = ∫ t, actionPullbackCov2 rho t u p ∂circleHaar := by
  have hc := fun i j => hu p _
    ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)) i j
  have hci := Integrable.of_eval (fun i => Integrable.of_eval (hc i))
  change cov2ReconstructCLM p p
    (fun i j => ∫ t, cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p) i j ∂circleHaar) = _
  have heq : (fun i j => ∫ t, cov2InChart (actionPullbackCov2 rho t u)
      p (chartAt FourSpace p p) i j ∂circleHaar) =
      ∫ t, cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p) ∂circleHaar := by
    funext i j
    rw [eval_integral (fun i => Integrable.of_eval (hc i)), eval_integral (hc i)]
  rw [heq, ← (cov2ReconstructCLM p p).integral_comp_comm hci]
  apply integral_congr_ae
  filter_upwards [] with t
  exact cov2_chart_recovery _ p p (mem_chart_source FourSpace p)

theorem covectorPi0_eq_fiberIntegral (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (p : M) :
    covectorPi0 rho u p = ∫ t, actionPullbackCovector rho t u p ∂circleHaar := by
  have hc := hu p _ ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p))
  have hci := Integrable.of_eval hc
  change covectorReconstructCLM p p
    (fun i => ∫ t, covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p) i ∂circleHaar) = _
  have heq : (fun i => ∫ t, covectorInChart (actionPullbackCovector rho t u)
      p (chartAt FourSpace p p) i ∂circleHaar) =
      ∫ t, covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p) ∂circleHaar := by
    funext i
    rw [eval_integral hc]
  rw [heq, ← (covectorReconstructCLM p p).integral_comp_comm hci]
  apply integral_congr_ae
  filter_upwards [] with t
  exact covector_chart_recovery _ p p (mem_chart_source FourSpace p)

theorem vectorPi0_eq_fiberIntegral (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    vectorPi0 rho Y p = ∫ t, actionPullbackVector rho t Y p ∂circleHaar := by
  have hc := hY p _ ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p))
  have hci := Integrable.of_eval hc
  change vectorReconstructCLM p p
    (fun i => ∫ t, vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i ∂circleHaar) = _
  have heq : (fun i => ∫ t, vectorInChart (actionPullbackVector rho t Y)
      p (chartAt FourSpace p p) i ∂circleHaar) =
      ∫ t, (fun i => vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i) ∂circleHaar := by
    funext i
    rw [eval_integral hc]
  rw [heq, ← (vectorReconstructCLM p p).integral_comp_comm hci]
  apply integral_congr_ae
  filter_upwards [] with t
  exact vector_chart_recovery _ p p (mem_chart_source FourSpace p)


def cov2FiberPullCLM {p q : M} (d : TangentSpace I4 p →L[ℝ] TangentSpace I4 q) :
    (TangentSpace I4 q →L[ℝ] TangentSpace I4 q →L[ℝ] ℝ) →L[ℝ]
      (TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => bilinearPullback a d
    map_add' := by intros; ext v w; simp
    map_smul' := by intros; ext v w; simp }

theorem cov2Pi0_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) : IsInvariantCov2 rho (cov2Pi0 rho u) := by
  intro s
  funext p
  change bilinearPullback (cov2Pi0 rho u (rho.act s p)) (mfderiv I4 I4 (rho.act s) p) = _
  rw [cov2Pi0_eq_fiberIntegral rho u hu, cov2Pi0_eq_fiberIntegral rho u hu]
  change cov2FiberPullCLM (mfderiv I4 I4 (rho.act s) p)
    (∫ t, actionPullbackCov2 rho t u (rho.act s p) ∂circleHaar) = _
  rw [← (cov2FiberPullCLM (mfderiv I4 I4 (rho.act s) p)).integral_comp_comm (hu.fiber _)]
  calc
    _ = ∫ t, actionPullbackCov2 rho (s * t) u p ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (congrFun (actionPullbackCov2_mul rho t s u) p).symm.trans
        (congrArg (fun a => actionPullbackCov2 rho a u p) (mul_comm t s))
    _ = _ := integral_mul_left_eq_self (μ := circleHaar) (fun t => actionPullbackCov2 rho t u p) s

theorem covectorPi0_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) : IsInvariantCovector rho (covectorPi0 rho u) := by
  intro s
  funext p
  change (covectorPi0 rho u (rho.act s p)).comp (mfderiv I4 I4 (rho.act s) p) = _
  rw [covectorPi0_eq_fiberIntegral rho u hu, covectorPi0_eq_fiberIntegral rho u hu]
  change (ContinuousLinearMap.precomp ℝ (mfderiv I4 I4 (rho.act s) p))
    (∫ t, actionPullbackCovector rho t u (rho.act s p) ∂circleHaar) = _
  rw [← (ContinuousLinearMap.precomp ℝ (mfderiv I4 I4 (rho.act s) p)).integral_comp_comm (hu.fiber _)]
  calc
    _ = ∫ t, actionPullbackCovector rho (s * t) u p ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (congrFun (actionPullbackCovector_mul rho t s u) p).symm.trans
        (congrArg (fun a => actionPullbackCovector rho a u p) (mul_comm t s))
    _ = _ := integral_mul_left_eq_self (μ := circleHaar) (fun t => actionPullbackCovector rho t u p) s

theorem vectorPi0_invariant (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) : IsInvariantVector rho (vectorPi0 rho Y) := by
  intro s
  funext p
  change mfderiv I4 I4 (rho.act s⁻¹) (rho.act s p) (vectorPi0 rho Y (rho.act s p)) = _
  rw [vectorPi0_eq_fiberIntegral rho Y hY, vectorPi0_eq_fiberIntegral rho Y hY]
  rw [← (mfderiv I4 I4 (rho.act s⁻¹) (rho.act s p)).integral_comp_comm (hY.fiber _)]
  calc
    _ = ∫ t, actionPullbackVector rho (s * t) Y p ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (congrFun (actionPullbackVector_mul rho t s Y) p).symm.trans
        (congrArg (fun a => actionPullbackVector rho a Y p) (mul_comm t s))
    _ = _ := integral_mul_left_eq_self (μ := circleHaar) (fun t => actionPullbackVector rho t Y p) s

theorem IsInvariantCov2.haarIntegrable {rho : CircleAction M} {u : RawCov2 M}
    (h : IsInvariantCov2 rho u) : Cov2HaarIntegrable rho u := by
  unfold IsInvariantCov2 at h
  intro c x hx i j
  simp only [h]
  exact integrable_const _

theorem cov2Pi0_of_invariant {rho : CircleAction M} {u : RawCov2 M}
    (h : IsInvariantCov2 rho u) : cov2Pi0 rho u = u := by
  funext p
  rw [cov2Pi0_eq_fiberIntegral rho u h.haarIntegrable]
  unfold IsInvariantCov2 at h
  simp only [h]
  simp

theorem cov2Pi0_idempotent (rho : CircleAction M) (u : RawCov2 M)
    (h : Cov2HaarIntegrable rho u) :
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u :=
  cov2Pi0_of_invariant (cov2Pi0_invariant rho u h)

theorem IsInvariantCovector.haarIntegrable {rho : CircleAction M} {u : RawCovector M}
    (h : IsInvariantCovector rho u) : CovectorHaarIntegrable rho u := by
  unfold IsInvariantCovector at h
  intro c x hx i
  simp only [h]
  exact integrable_const _

theorem covectorPi0_of_invariant {rho : CircleAction M} {u : RawCovector M}
    (h : IsInvariantCovector rho u) : covectorPi0 rho u = u := by
  funext p
  rw [covectorPi0_eq_fiberIntegral rho u h.haarIntegrable]
  unfold IsInvariantCovector at h
  simp only [h]
  simp

theorem covectorPi0_idempotent (rho : CircleAction M) (u : RawCovector M)
    (h : CovectorHaarIntegrable rho u) :
    covectorPi0 rho (covectorPi0 rho u) = covectorPi0 rho u :=
  covectorPi0_of_invariant (covectorPi0_invariant rho u h)

theorem IsInvariantVector.haarIntegrable {rho : CircleAction M} {Y : RawVector M}
    (h : IsInvariantVector rho Y) : VectorHaarIntegrable rho Y := by
  unfold IsInvariantVector at h
  intro c x hx i
  simp only [h]
  exact integrable_const _

theorem vectorPi0_of_invariant {rho : CircleAction M} {Y : RawVector M}
    (h : IsInvariantVector rho Y) : vectorPi0 rho Y = Y := by
  funext p
  rw [vectorPi0_eq_fiberIntegral rho Y h.haarIntegrable]
  unfold IsInvariantVector at h
  simp only [h]
  simp

theorem vectorPi0_idempotent (rho : CircleAction M) (Y : RawVector M)
    (h : VectorHaarIntegrable rho Y) :
    vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y :=
  vectorPi0_of_invariant (vectorPi0_invariant rho Y h)


theorem actionPullbackCov2_sub (rho : CircleAction M) (t : Circle)
    (u v : RawCov2 M) :
    actionPullbackCov2 rho t (u - v) =
      actionPullbackCov2 rho t u - actionPullbackCov2 rho t v := by
  ext p a b
  simp [actionPullbackCov2, pullbackCov2]

theorem actionPullbackCovector_sub (rho : CircleAction M) (t : Circle)
    (u v : RawCovector M) :
    actionPullbackCovector rho t (u - v) =
      actionPullbackCovector rho t u - actionPullbackCovector rho t v := by
  ext p a
  simp [actionPullbackCovector, pullbackCovector]

theorem actionPullbackVector_sub (rho : CircleAction M) (t : Circle)
    (Y Z : RawVector M) :
    actionPullbackVector rho t (Y - Z) =
      actionPullbackVector rho t Y - actionPullbackVector rho t Z := by
  funext p
  simp [actionPullbackVector]

theorem Cov2HaarIntegrable.sub {rho : CircleAction M} {u v : RawCov2 M}
    (hu : Cov2HaarIntegrable rho u) (hv : Cov2HaarIntegrable rho v) :
    Cov2HaarIntegrable rho (u - v) := by
  intro c x hx i j
  apply ((hu c x hx i j).sub (hv c x hx i j)).congr
  filter_upwards [] with t
  simp [actionPullbackCov2_sub, cov2InChart]

theorem CovectorHaarIntegrable.sub {rho : CircleAction M} {u v : RawCovector M}
    (hu : CovectorHaarIntegrable rho u) (hv : CovectorHaarIntegrable rho v) :
    CovectorHaarIntegrable rho (u - v) := by
  intro c x hx i
  apply ((hu c x hx i).sub (hv c x hx i)).congr
  filter_upwards [] with t
  simp [actionPullbackCovector_sub, covectorInChart]

theorem VectorHaarIntegrable.sub {rho : CircleAction M} {Y Z : RawVector M}
    (hY : VectorHaarIntegrable rho Y) (hZ : VectorHaarIntegrable rho Z) :
    VectorHaarIntegrable rho (Y - Z) := by
  intro c x hx i
  apply ((hY c x hx i).sub (hZ c x hx i)).congr
  filter_upwards [] with t
  simp [actionPullbackVector_sub, vectorInChart, WithLp.ofLp_sub]
  rfl

theorem cov2Pi0_sub (rho : CircleAction M) (u v : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hv : Cov2HaarIntegrable rho v) :
    cov2Pi0 rho (u - v) = cov2Pi0 rho u - cov2Pi0 rho v := by
  funext p
  rw [cov2Pi0_eq_fiberIntegral rho (u - v) (hu.sub hv)]
  simp only [actionPullbackCov2_sub, Pi.sub_apply]
  rw [integral_sub (hu.fiber p) (hv.fiber p),
    ← cov2Pi0_eq_fiberIntegral rho u hu, ← cov2Pi0_eq_fiberIntegral rho v hv]

theorem covectorPi0_sub (rho : CircleAction M) (u v : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hv : CovectorHaarIntegrable rho v) :
    covectorPi0 rho (u - v) = covectorPi0 rho u - covectorPi0 rho v := by
  funext p
  rw [covectorPi0_eq_fiberIntegral rho (u - v) (hu.sub hv)]
  simp only [actionPullbackCovector_sub, Pi.sub_apply]
  rw [integral_sub (hu.fiber p) (hv.fiber p),
    ← covectorPi0_eq_fiberIntegral rho u hu, ← covectorPi0_eq_fiberIntegral rho v hv]

theorem vectorPi0_sub (rho : CircleAction M) (Y Z : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (hZ : VectorHaarIntegrable rho Z) :
    vectorPi0 rho (Y - Z) = vectorPi0 rho Y - vectorPi0 rho Z := by
  funext p
  rw [vectorPi0_eq_fiberIntegral rho (Y - Z) (hY.sub hZ)]
  simp only [actionPullbackVector_sub, Pi.sub_apply]
  rw [integral_sub (hY.fiber p) (hZ.fiber p),
    ← vectorPi0_eq_fiberIntegral rho Y hY, ← vectorPi0_eq_fiberIntegral rho Z hZ]

theorem cov2PiPerp_zeroMean (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) : IsNonzeroCov2 rho (cov2PiPerp rho u) := by
  unfold IsNonzeroCov2 cov2PiPerp
  rw [cov2Pi0_sub rho u _ hu (cov2Pi0_invariant rho u hu).haarIntegrable,
    cov2Pi0_idempotent rho u hu, sub_self]

theorem covectorPiPerp_zeroMean (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) : IsNonzeroCovector rho (covectorPiPerp rho u) := by
  unfold IsNonzeroCovector covectorPiPerp
  rw [covectorPi0_sub rho u _ hu (covectorPi0_invariant rho u hu).haarIntegrable,
    covectorPi0_idempotent rho u hu, sub_self]

theorem vectorPiPerp_zeroMean (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) : IsNonzeroVector rho (vectorPiPerp rho Y) := by
  unfold IsNonzeroVector vectorPiPerp
  rw [vectorPi0_sub rho Y _ hY (vectorPi0_invariant rho Y hY).haarIntegrable,
    vectorPi0_idempotent rho Y hY, sub_self]

/-- The algebraic Haar fields used by all three sectors of
`HolderProjectionConclusions`, for the same actual smooth circle action. -/
theorem common_circle_haar_projection_algebra (rho : CircleAction M) :
    (∀ u : RawCov2 M, Cov2HaarIntegrable rho u →
      IsInvariantCov2 rho (cov2Pi0 rho u) ∧
      cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
      IsNonzeroCov2 rho (cov2PiPerp rho u)) ∧
    (∀ eta : RawCovector M, CovectorHaarIntegrable rho eta →
      IsInvariantCovector rho (covectorPi0 rho eta) ∧
      covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta)) ∧
    (∀ Y : RawVector M, VectorHaarIntegrable rho Y →
      IsInvariantVector rho (vectorPi0 rho Y) ∧
      vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
      IsNonzeroVector rho (vectorPiPerp rho Y)) := by
  exact ⟨fun u hu => ⟨cov2Pi0_invariant rho u hu, cov2Pi0_idempotent rho u hu,
      cov2PiPerp_zeroMean rho u hu⟩,
    fun eta h => ⟨covectorPi0_invariant rho eta h, covectorPi0_idempotent rho eta h,
      covectorPiPerp_zeroMean rho eta h⟩,
    fun Y hY => ⟨vectorPi0_invariant rho Y hY, vectorPi0_idempotent rho Y hY,
      vectorPiPerp_zeroMean rho Y hY⟩⟩

end K24.Global

open scoped Manifold ContDiff

/-- Standalone upload entrypoint; the proposed public declaration has another name. -/
theorem _root_.solution :
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
      [IsManifold K24.Global.I4 ∞ M] (rho : K24.Global.CircleAction M),
    (∀ u : K24.Global.RawCov2 M, K24.Global.Cov2HaarIntegrable rho u →
      K24.Global.IsInvariantCov2 rho (K24.Global.cov2Pi0 rho u) ∧
      K24.Global.cov2Pi0 rho (K24.Global.cov2Pi0 rho u) = K24.Global.cov2Pi0 rho u ∧
      K24.Global.IsNonzeroCov2 rho (K24.Global.cov2PiPerp rho u)) ∧
    (∀ eta : K24.Global.RawCovector M, K24.Global.CovectorHaarIntegrable rho eta →
      K24.Global.IsInvariantCovector rho (K24.Global.covectorPi0 rho eta) ∧
      K24.Global.covectorPi0 rho (K24.Global.covectorPi0 rho eta) = K24.Global.covectorPi0 rho eta ∧
      K24.Global.IsNonzeroCovector rho (K24.Global.covectorPiPerp rho eta)) ∧
    (∀ Y : K24.Global.RawVector M, K24.Global.VectorHaarIntegrable rho Y →
      K24.Global.IsInvariantVector rho (K24.Global.vectorPi0 rho Y) ∧
      K24.Global.vectorPi0 rho (K24.Global.vectorPi0 rho Y) = K24.Global.vectorPi0 rho Y ∧
      K24.Global.IsNonzeroVector rho (K24.Global.vectorPiPerp rho Y)) := by
  intro M _ _ _ rho
  exact K24.Global.common_circle_haar_projection_algebra rho
