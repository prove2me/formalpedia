-- Prove2me | solution 1 for K24.Global.pointwiseHaarProjectionSectors
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:02:36.283679+00:00
-- url     : https://prove2.me/submissions/10f6c179-c19d-40b9-959c-e173495a4bd3

import Definitions.Def_K24GlobalGeometry

/-!
Canonical-only K24 pointwise Haar projection candidate.
The named hypotheses concern continuity of actual bundle evaluations and sections.
No big-Hölder norm continuity, Hölder estimate, Sobolev estimate, or open target is assumed.
The source is a standalone packaging of the independently checked algebraic,
vector, and continuous-section proofs; the namespace avoids conflict with the
separately frozen projection-subtraction helper used by the operator route.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace K24.Global.HaarSectors

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

lemma circleHaar_leftInvariant : circleHaar.IsMulLeftInvariant := by
  unfold circleHaar
  infer_instance

attribute [local instance] circleHaar_leftInvariant

lemma coefficientsToCovector_apply (a : Fin 4 → ℝ) (v : FourSpace) :
    coefficientsToCovector a v = ∑ i : Fin 4, a i * v i := by
  simp [coefficientsToCovector, coordProj]

lemma matrixToBilinear_apply (a : Mat4) (v w : FourSpace) :
    matrixToBilinear a v w = ∑ i : Fin 4, ∑ j : Fin 4, v i * (a i j * w j) := by
  simp [matrixToBilinear, coordProj]

lemma integrable_covector_coordinates (a : Circle → Fin 4 → ℝ)
    (ha : ∀ i, Integrable (fun t => a t i) circleHaar) (v : FourSpace) :
    Integrable (fun t => coefficientsToCovector (a t) v) circleHaar := by
  simp_rw [coefficientsToCovector_apply]
  exact integrable_finsetSum _ (fun i _ => (ha i).mul_const _)

lemma integral_covector_coordinates (a : Circle → Fin 4 → ℝ)
    (ha : ∀ i, Integrable (fun t => a t i) circleHaar) (v : FourSpace) :
    coefficientsToCovector (fun i => ∫ t, a t i ∂circleHaar) v =
      ∫ t, coefficientsToCovector (a t) v ∂circleHaar := by
  simp_rw [coefficientsToCovector_apply]
  rw [integral_finsetSum _ (fun i _ => (ha i).mul_const _)]
  simp_rw [integral_mul_const]

lemma integrable_cov2_coordinates (a : Circle → Mat4)
    (ha : ∀ i j, Integrable (fun t => a t i j) circleHaar) (v w : FourSpace) :
    Integrable (fun t => matrixToBilinear (a t) v w) circleHaar := by
  simp_rw [matrixToBilinear_apply]
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => ((ha i j).mul_const _).const_mul _))

lemma integral_cov2_coordinates (a : Circle → Mat4)
    (ha : ∀ i j, Integrable (fun t => a t i j) circleHaar) (v w : FourSpace) :
    matrixToBilinear (fun i j => ∫ t, a t i j ∂circleHaar) v w =
      ∫ t, matrixToBilinear (a t) v w ∂circleHaar := by
  simp_rw [matrixToBilinear_apply]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => ((ha i j).mul_const _).const_mul _))]
  congr 1
  funext i
  rw [integral_finsetSum _ (fun j _ => ((ha i j).mul_const _).const_mul _)]
  simp_rw [integral_const_mul, integral_mul_const]

variable [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
lemma action_smooth (rho : CircleAction M) (t : Circle) : ContMDiff I4 I4 ∞ (rho.act t) :=
  rho.smooth.comp (contMDiff_const.prodMk contMDiff_id)

lemma action_derivative_mul (rho : CircleAction M) (s t : Circle) (p : M) :
    mfderiv I4 I4 (rho.act (s * t)) p =
      (mfderiv I4 I4 (rho.act s) (rho.act t p)).comp (mfderiv I4 I4 (rho.act t) p) := by
  have heq : rho.act (s * t) = rho.act s ∘ rho.act t := funext (rho.mul_act s t)
  rw [heq]
  exact mfderiv_comp p ((action_smooth rho s).mdifferentiable (by simp) _)
    ((action_smooth rho t).mdifferentiable (by simp) _)

lemma pullback_covector_mul (rho : CircleAction M) (s t : Circle) (u : RawCovector M) :
    actionPullbackCovector rho s (actionPullbackCovector rho t u) =
      actionPullbackCovector rho (t * s) u := by
  funext p
  ext v
  simp only [actionPullbackCovector, pullbackCovector, ContinuousLinearMap.comp_apply]
  rw [action_derivative_mul, rho.mul_act]
  rfl

lemma pullback_cov2_mul (rho : CircleAction M) (s t : Circle) (u : RawCov2 M) :
    actionPullbackCov2 rho s (actionPullbackCov2 rho t u) =
      actionPullbackCov2 rho (t * s) u := by
  funext p
  ext v w
  simp only [actionPullbackCov2, pullbackCov2, bilinearPullback_apply]
  rw [action_derivative_mul, rho.mul_act]
  rfl

lemma covector_chart_eval (u : RawCovector M) (p : M) (v : TangentSpace I4 p) :
    coefficientsToCovector (covectorInChart u p (chartAt FourSpace p p))
      (mfderiv I4 I4 (chartAt FourSpace p) p v) = u p v := by
  have h := covector_chart_recovery u p p (mem_chart_source FourSpace p)
  exact congrArg (fun L => L v) h

lemma cov2_chart_eval (u : RawCov2 M) (p : M) (v w : TangentSpace I4 p) :
    matrixToBilinear (cov2InChart u p (chartAt FourSpace p p))
      (mfderiv I4 I4 (chartAt FourSpace p) p v)
      (mfderiv I4 I4 (chartAt FourSpace p) p w) = u p v w := by
  have h := cov2_chart_recovery u p p (mem_chart_source FourSpace p)
  exact congrArg (fun L => L v w) h

lemma covector_orbit_integrable (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (p : M) (v : TangentSpace I4 p) :
    Integrable (fun t => actionPullbackCovector rho t u p v) circleHaar := by
  have h := integrable_covector_coordinates
    (fun t => covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p))
    (hu p _ (mem_chart_target FourSpace p)) (mfderiv I4 I4 (chartAt FourSpace p) p v)
  simpa only [covector_chart_eval] using h

lemma cov2_orbit_integrable (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (p : M) (v w : TangentSpace I4 p) :
    Integrable (fun t => actionPullbackCov2 rho t u p v w) circleHaar := by
  have h := integrable_cov2_coordinates
    (fun t => cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p))
    (hu p _ (mem_chart_target FourSpace p))
    (mfderiv I4 I4 (chartAt FourSpace p) p v)
    (mfderiv I4 I4 (chartAt FourSpace p) p w)
  simpa only [cov2_chart_eval] using h

lemma covectorPi0_apply (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (p : M) (v : TangentSpace I4 p) :
    covectorPi0 rho u p v = ∫ t, actionPullbackCovector rho t u p v ∂circleHaar := by
  change coefficientsToCovector
    (fun i => ∫ t, covectorInChart (actionPullbackCovector rho t u) p
      (chartAt FourSpace p p) i ∂circleHaar)
      (mfderiv I4 I4 (chartAt FourSpace p) p v) = _
  rw [integral_covector_coordinates _ (hu p _ (mem_chart_target FourSpace p))]
  simp only [covector_chart_eval]

lemma cov2Pi0_apply (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (p : M) (v w : TangentSpace I4 p) :
    cov2Pi0 rho u p v w = ∫ t, actionPullbackCov2 rho t u p v w ∂circleHaar := by
  change matrixToBilinear
    (fun i j => ∫ t, cov2InChart (actionPullbackCov2 rho t u) p
      (chartAt FourSpace p p) i j ∂circleHaar)
      (mfderiv I4 I4 (chartAt FourSpace p) p v)
      (mfderiv I4 I4 (chartAt FourSpace p) p w) = _
  rw [integral_cov2_coordinates _ (hu p _ (mem_chart_target FourSpace p))]
  simp only [cov2_chart_eval]

lemma covectorPi0_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) : IsInvariantCovector rho (covectorPi0 rho u) := by
  intro s
  funext p
  ext v
  change covectorPi0 rho u (rho.act s p) (mfderiv I4 I4 (rho.act s) p v) = _
  rw [covectorPi0_apply rho u hu, covectorPi0_apply rho u hu]
  calc
    _ = ∫ t, actionPullbackCovector rho (s * t) u p v ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      change actionPullbackCovector rho s (actionPullbackCovector rho t u) p v = _
      rw [pullback_covector_mul, mul_comm]
    _ = _ := integral_mul_left_eq_self (μ := circleHaar)
      (fun t => actionPullbackCovector rho t u p v) s

lemma cov2Pi0_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) : IsInvariantCov2 rho (cov2Pi0 rho u) := by
  intro s
  funext p
  ext v w
  change cov2Pi0 rho u (rho.act s p) (mfderiv I4 I4 (rho.act s) p v)
    (mfderiv I4 I4 (rho.act s) p w) = _
  rw [cov2Pi0_apply rho u hu, cov2Pi0_apply rho u hu]
  calc
    _ = ∫ t, actionPullbackCov2 rho (s * t) u p v w ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      change actionPullbackCov2 rho s (actionPullbackCov2 rho t u) p v w = _
      rw [pullback_cov2_mul, mul_comm]
    _ = _ := integral_mul_left_eq_self (μ := circleHaar)
      (fun t => actionPullbackCov2 rho t u p v w) s

omit [IsManifold I4 ∞ M] in
lemma covector_integrable_of_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : IsInvariantCovector rho u) : CovectorHaarIntegrable rho u := by
  intro c x hx i
  simp_rw [show ∀ t, actionPullbackCovector rho t u = u from hu]
  exact integrable_const _

omit [IsManifold I4 ∞ M] in
lemma cov2_integrable_of_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : IsInvariantCov2 rho u) : Cov2HaarIntegrable rho u := by
  intro c x hx i j
  simp_rw [show ∀ t, actionPullbackCov2 rho t u = u from hu]
  exact integrable_const _

lemma covectorPi0_eq_of_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : IsInvariantCovector rho u) : covectorPi0 rho u = u := by
  funext p
  ext v
  rw [covectorPi0_apply rho u (covector_integrable_of_invariant rho u hu)]
  simp_rw [show ∀ t, actionPullbackCovector rho t u = u from hu]
  simp

lemma cov2Pi0_eq_of_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : IsInvariantCov2 rho u) : cov2Pi0 rho u = u := by
  funext p
  ext v w
  rw [cov2Pi0_apply rho u (cov2_integrable_of_invariant rho u hu)]
  simp_rw [show ∀ t, actionPullbackCov2 rho t u = u from hu]
  simp

omit [IsManifold I4 ∞ M] in
lemma covector_integrable_sub (rho : CircleAction M) (u z : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hz : CovectorHaarIntegrable rho z) :
    CovectorHaarIntegrable rho (u - z) := by
  intro c x hx i
  exact (hu c x hx i).sub (hz c x hx i)

omit [IsManifold I4 ∞ M] in
lemma cov2_integrable_sub (rho : CircleAction M) (u z : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hz : Cov2HaarIntegrable rho z) :
    Cov2HaarIntegrable rho (u - z) := by
  intro c x hx i j
  exact (hu c x hx i j).sub (hz c x hx i j)

lemma covectorPi0_sub (rho : CircleAction M) (u z : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hz : CovectorHaarIntegrable rho z) :
    covectorPi0 rho (u - z) = covectorPi0 rho u - covectorPi0 rho z := by
  funext p
  ext v
  rw [covectorPi0_apply rho (u - z) (covector_integrable_sub rho u z hu hz)]
  change (∫ t, actionPullbackCovector rho t u p v - actionPullbackCovector rho t z p v
    ∂circleHaar) = covectorPi0 rho u p v - covectorPi0 rho z p v
  rw [integral_sub (covector_orbit_integrable rho u hu p v)
    (covector_orbit_integrable rho z hz p v), covectorPi0_apply rho u hu,
    covectorPi0_apply rho z hz]

lemma cov2Pi0_sub (rho : CircleAction M) (u z : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hz : Cov2HaarIntegrable rho z) :
    cov2Pi0 rho (u - z) = cov2Pi0 rho u - cov2Pi0 rho z := by
  funext p
  ext v w
  rw [cov2Pi0_apply rho (u - z) (cov2_integrable_sub rho u z hu hz)]
  change (∫ t, actionPullbackCov2 rho t u p v w - actionPullbackCov2 rho t z p v w
    ∂circleHaar) = cov2Pi0 rho u p v w - cov2Pi0 rho z p v w
  rw [integral_sub (cov2_orbit_integrable rho u hu p v w)
    (cov2_orbit_integrable rho z hz p v w), cov2Pi0_apply rho u hu,
    cov2Pi0_apply rho z hz]

/-- Pointwise projection and sector laws for the canonical tensor Haar average. -/
theorem cov2_projection (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) :
    IsInvariantCov2 rho (cov2Pi0 rho u) ∧
    Cov2HaarIntegrable rho (cov2Pi0 rho u) ∧
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
    Cov2HaarIntegrable rho (cov2PiPerp rho u) ∧
    IsNonzeroCov2 rho (cov2PiPerp rho u) := by
  have hi := cov2Pi0_invariant rho u hu
  have hint := cov2_integrable_of_invariant rho _ hi
  have hid := cov2Pi0_eq_of_invariant rho _ hi
  refine ⟨hi, hint, hid, cov2_integrable_sub rho u _ hu hint, ?_⟩
  change cov2Pi0 rho (u - cov2Pi0 rho u) = 0
  rw [cov2Pi0_sub rho u _ hu hint, hid, sub_self]

/-- Pointwise projection and sector laws for the canonical covector Haar average. -/
theorem covector_projection (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) :
    IsInvariantCovector rho (covectorPi0 rho u) ∧
    CovectorHaarIntegrable rho (covectorPi0 rho u) ∧
    covectorPi0 rho (covectorPi0 rho u) = covectorPi0 rho u ∧
    CovectorHaarIntegrable rho (covectorPiPerp rho u) ∧
    IsNonzeroCovector rho (covectorPiPerp rho u) := by
  have hi := covectorPi0_invariant rho u hu
  have hint := covector_integrable_of_invariant rho _ hi
  have hid := covectorPi0_eq_of_invariant rho _ hi
  refine ⟨hi, hint, hid, covector_integrable_sub rho u _ hu hint, ?_⟩
  change covectorPi0 rho (u - covectorPi0 rho u) = 0
  rw [covectorPi0_sub rho u _ hu hint, hid, sub_self]

/-- The canonical complementary projection respects subtraction on genuinely integrable inputs. -/
theorem covectorPiPerp_sub (rho : CircleAction M) (u z : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hz : CovectorHaarIntegrable rho z) :
    covectorPiPerp rho (u - z) = covectorPiPerp rho u - covectorPiPerp rho z := by
  simp only [covectorPiPerp, covectorPi0_sub rho u z hu hz]
  abel

/-- The tensor complementary projection respects subtraction on genuinely integrable inputs. -/
theorem cov2PiPerp_sub (rho : CircleAction M) (u z : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hz : Cov2HaarIntegrable rho z) :
    cov2PiPerp rho (u - z) = cov2PiPerp rho u - cov2PiPerp rho z := by
  simp only [cov2PiPerp, cov2Pi0_sub rho u z hu hz]
  abel

end K24.Global.HaarSectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace K24.Global.HaarSectors

attribute [local instance] circleHaar_leftInvariant

-- A fixed fiber is integrated using the model norm only inside this module.
-- These instances do not impose or export a section norm or a Riemannian norm.
private noncomputable def modelNormedTangent {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] (p : N) : NormedAddCommGroup (TangentSpace I4 p) :=
  inferInstanceAs (NormedAddCommGroup FourSpace)

attribute [local instance] modelNormedTangent

private noncomputable def modelNormedSpaceTangent {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] (p : N) : NormedSpace ℝ (TangentSpace I4 p) :=
  inferInstanceAs (NormedSpace ℝ FourSpace)

attribute [local instance] modelNormedSpaceTangent

private def modelCompleteTangent {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] (p : N) : CompleteSpace (TangentSpace I4 p) :=
  inferInstanceAs (CompleteSpace FourSpace)

attribute [local instance] modelCompleteTangent

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
lemma action_inv_act (rho : CircleAction M) (t : Circle) (p : M) :
    rho.act t⁻¹ (rho.act t p) = p := by
  rw [← rho.mul_act, inv_mul_cancel, rho.one_act]

lemma pullback_vector_mul (rho : CircleAction M) (s t : Circle) (Y : RawVector M) :
    actionPullbackVector rho s (actionPullbackVector rho t Y) =
      actionPullbackVector rho (t * s) Y := by
  funext p
  unfold actionPullbackVector
  rw [mul_inv_rev, action_derivative_mul]
  change mfderiv I4 I4 (rho.act s⁻¹) (rho.act s p)
    (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t (rho.act s p)) (Y (rho.act t (rho.act s p)))) =
    mfderiv I4 I4 (rho.act s⁻¹) (rho.act t⁻¹ (rho.act (t * s) p))
    (mfderiv I4 I4 (rho.act t⁻¹) (rho.act (t * s) p) (Y (rho.act (t * s) p)))
  rw [rho.mul_act]
  exact (congrArg (fun q : M =>
    (mfderiv I4 I4 (rho.act s⁻¹) q : FourSpace →L[ℝ] FourSpace)
      (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t (rho.act s p))
        (Y (rho.act t (rho.act s p))))) (action_inv_act rho t (rho.act s p))).symm

lemma vector_chart_eval (Y : RawVector M) (p : M) :
    mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)
      (∑ i : Fin 4, vectorInChart Y p (chartAt FourSpace p p) i • basisVector i) = Y p := by
  rw [sum_basisVector]
  change mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)
    (mfderiv I4 I4 (chartAt FourSpace p) ((chartAt FourSpace p).symm (chartAt FourSpace p p))
      (Y ((chartAt FourSpace p).symm (chartAt FourSpace p p)))) = Y p
  rw [(chartAt FourSpace p).left_inv (mem_chart_source FourSpace p)]
  have hd := (mdifferentiable_chart (I := I4) p).symm_comp_deriv
    (mem_chart_source FourSpace p)
  exact congrArg (fun L => L (Y p)) hd

omit [IsManifold I4 ∞ M] in
lemma vector_coordinate_sum_integrable (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    Integrable (fun t => ∑ i : Fin 4,
      vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i • basisVector i)
      circleHaar :=
  integrable_finsetSum _ (fun i _ =>
    (hY p _ (mem_chart_target FourSpace p) i).smul_const (basisVector i))

lemma vector_orbit_integrable (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    Integrable (fun t => actionPullbackVector rho t Y p) circleHaar := by
  have h := (mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)).integrable_comp
    (vector_coordinate_sum_integrable rho Y hY p)
  apply h.congr
  filter_upwards [] with t
  exact vector_chart_eval (actionPullbackVector rho t Y) p

lemma vectorPi0_eq_integral (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    vectorPi0 rho Y p = ∫ t, actionPullbackVector rho t Y p ∂circleHaar := by
  unfold vectorPi0
  calc
    _ = mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)
      (∫ t, ∑ i : Fin 4,
        vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i • basisVector i
        ∂circleHaar) := by
      rw [integral_finsetSum _ (fun i _ =>
        (hY p _ (mem_chart_target FourSpace p) i).smul_const (basisVector i))]
      simp_rw [integral_smul_const]
    _ = ∫ t, mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)
      (∑ i : Fin 4,
        vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i • basisVector i)
        ∂circleHaar := by
      exact ((mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)).integral_comp_comm
        (vector_coordinate_sum_integrable rho Y hY p)).symm
    _ = _ := by simp only [vector_chart_eval]

lemma vectorPi0_invariant (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) : IsInvariantVector rho (vectorPi0 rho Y) := by
  intro s
  funext p
  change mfderiv I4 I4 (rho.act s⁻¹) (rho.act s p) (vectorPi0 rho Y (rho.act s p)) = _
  rw [vectorPi0_eq_integral rho Y hY, vectorPi0_eq_integral rho Y hY]
  rw [← (mfderiv I4 I4 (rho.act s⁻¹) (rho.act s p)).integral_comp_comm
    (vector_orbit_integrable rho Y hY (rho.act s p))]
  calc
    _ = ∫ t, actionPullbackVector rho (s * t) Y p ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      change actionPullbackVector rho s (actionPullbackVector rho t Y) p = _
      rw [pullback_vector_mul, mul_comm]
    _ = _ := integral_mul_left_eq_self (μ := circleHaar)
      (fun t => actionPullbackVector rho t Y p) s

omit [IsManifold I4 ∞ M] in
lemma vector_integrable_of_invariant (rho : CircleAction M) (Y : RawVector M)
    (hY : IsInvariantVector rho Y) : VectorHaarIntegrable rho Y := by
  intro c x hx i
  simp_rw [show ∀ t, actionPullbackVector rho t Y = Y from hY]
  exact integrable_const _

lemma vectorPi0_eq_of_invariant (rho : CircleAction M) (Y : RawVector M)
    (hY : IsInvariantVector rho Y) : vectorPi0 rho Y = Y := by
  funext p
  rw [vectorPi0_eq_integral rho Y (vector_integrable_of_invariant rho Y hY)]
  simp_rw [show ∀ t, actionPullbackVector rho t Y = Y from hY]
  simp

omit [IsManifold I4 ∞ M] in
lemma vector_integrable_sub (rho : CircleAction M) (Y Z : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (hZ : VectorHaarIntegrable rho Z) :
    VectorHaarIntegrable rho (Y - Z) := by
  intro c x hx i
  have h := (hY c x hx i).sub (hZ c x hx i)
  convert h using 1
  funext t
  simp only [vectorInChart, actionPullbackVector, Pi.sub_apply, map_sub]
  rfl

lemma vectorPi0_sub (rho : CircleAction M) (Y Z : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (hZ : VectorHaarIntegrable rho Z) :
    vectorPi0 rho (Y - Z) = vectorPi0 rho Y - vectorPi0 rho Z := by
  funext p
  rw [vectorPi0_eq_integral rho (Y - Z) (vector_integrable_sub rho Y Z hY hZ)]
  simp only [actionPullbackVector, Pi.sub_apply, map_sub]
  change (∫ t, actionPullbackVector rho t Y p - actionPullbackVector rho t Z p ∂circleHaar) =
    vectorPi0 rho Y p - vectorPi0 rho Z p
  rw [integral_sub (vector_orbit_integrable rho Y hY p) (vector_orbit_integrable rho Z hZ p)]
  rw [vectorPi0_eq_integral rho Y hY, vectorPi0_eq_integral rho Z hZ]

/-- Pointwise projection and sector laws for the inverse-differential vector average. -/
theorem vector_projection (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) :
    IsInvariantVector rho (vectorPi0 rho Y) ∧
    VectorHaarIntegrable rho (vectorPi0 rho Y) ∧
    vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
    VectorHaarIntegrable rho (vectorPiPerp rho Y) ∧
    IsNonzeroVector rho (vectorPiPerp rho Y) := by
  have hi := vectorPi0_invariant rho Y hY
  have hint := vector_integrable_of_invariant rho _ hi
  have hid := vectorPi0_eq_of_invariant rho _ hi
  refine ⟨hi, hint, hid, vector_integrable_sub rho Y _ hY hint, ?_⟩
  change vectorPi0 rho (Y - vectorPi0 rho Y) = 0
  rw [vectorPi0_sub rho Y _ hY hint, hid, sub_self]

end K24.Global.HaarSectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators

namespace K24.Global.HaarSectors

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Continuity of evaluation on the actual tangent bundle. -/
def CovectorEvaluationContinuous (u : RawCovector M) : Prop :=
  Continuous (fun q : TangentBundle I4 M => u q.proj q.2)

/-- The fiber product of two copies of the actual tangent bundle. -/
abbrev TangentPair (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  {q : TangentBundle I4 M × TangentBundle I4 M // q.1.proj = q.2.proj}

/-- Continuity of bilinear evaluation on pairs of vectors in the same tangent fiber. -/
def Cov2EvaluationContinuous (u : RawCov2 M) : Prop :=
  Continuous (fun q : TangentPair M => u q.val.1.proj q.val.1.2 q.val.2.2)

/-- Joint continuity of the actual tangent lift of the smooth circle action. -/
lemma action_tangent_continuous (rho : CircleAction M) :
    Continuous (fun q : Circle × TangentBundle I4 M =>
      (⟨rho.act q.1 q.2.proj, mfderiv I4 I4 (rho.act q.1) q.2.proj q.2.2⟩ :
        TangentBundle I4 M)) := by
  have hz : Continuous (fun t : Circle => (⟨t, 0⟩ : TangentBundle (𝓡 1) Circle)) :=
    Bundle.Trivialization.continuous_zeroSection ℝ
  have hi := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓡 1) (M := Circle) (I' := I4) (M' := M) (n := 0)).continuous.comp
      ((hz.comp continuous_fst).prodMk (continuous_snd :
        Continuous (Prod.snd : Circle × TangentBundle I4 M → TangentBundle I4 M)))
  have h := (rho.smooth.continuous_tangentMap (by simp)).comp hi
  convert h using 1
  funext ⟨t, p, v⟩
  change (⟨rho.act t p, mfderiv I4 I4 (rho.act t) p v⟩ : TangentBundle I4 M) =
    ⟨rho.act t p, mfderiv ((𝓡 1).prod I4) I4
      (fun q : Circle × M => rho.act q.1 q.2) (t, p) (0, v)⟩
  congr 1
  have hd := mfderiv_comp (I := I4) (I' := (𝓡 1).prod I4) (I'' := I4) p
    (rho.smooth.mdifferentiable (by simp) (t, p))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [mfderiv_prod_right] at hd
  exact congrArg (fun L => L v) hd

lemma action_tangent_orbit_continuous (rho : CircleAction M) (p : M)
    (v : TangentSpace I4 p) :
    Continuous (fun t : Circle => (⟨rho.act t p, mfderiv I4 I4 (rho.act t) p v⟩ :
      TangentBundle I4 M)) :=
  (action_tangent_continuous rho).comp
    (continuous_id.prodMk (continuous_const (y := (⟨p, v⟩ : TangentBundle I4 M))))

lemma covector_orbit_continuous (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) (p : M) (v : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCovector rho t u p v) :=
  hu.comp (action_tangent_orbit_continuous rho p v)

lemma cov2_orbit_continuous (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2EvaluationContinuous u) (p : M) (v w : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCov2 rho t u p v w) := by
  have h := (action_tangent_orbit_continuous rho p v).prodMk
    (action_tangent_orbit_continuous rho p w)
  exact hu.comp (h.subtype_mk (fun _ => rfl))

lemma covector_haar_integrable_of_continuous (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) : CovectorHaarIntegrable rho u := by
  intro c x hx i
  exact (covector_orbit_continuous rho u hu ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma cov2_haar_integrable_of_continuous (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2EvaluationContinuous u) : Cov2HaarIntegrable rho u := by
  intro c x hx i j
  exact (cov2_orbit_continuous rho u hu ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Ordinary continuity of an actual vector section into the tangent bundle. -/
def VectorSectionContinuous (Y : RawVector M) : Prop :=
  Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M))

lemma vector_orbit_continuous (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorSectionContinuous Y) (p : M) :
    Continuous (fun t : Circle => actionPullbackVector rho t Y p) := by
  have ha : Continuous (fun t : Circle => rho.act t p) :=
    rho.smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have h := (action_tangent_continuous rho).comp (continuous_inv.prodMk (hY.comp ha))
  have hb : Continuous (fun t : Circle =>
      (⟨p, actionPullbackVector rho t Y p⟩ : TangentBundle I4 M)) := by
    convert h using 1
    funext t
    change (⟨p, actionPullbackVector rho t Y p⟩ : TangentBundle I4 M) =
      ⟨rho.act t⁻¹ (rho.act t p), actionPullbackVector rho t Y p⟩
    congr 1
    exact (action_inv_act rho t p).symm
  exact (FiberBundle.totalSpaceMk_isInducing FourSpace (TangentSpace I4) p).continuous_iff.mpr hb

lemma vector_haar_integrable_of_continuous (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorSectionContinuous Y) : VectorHaarIntegrable rho Y := by
  intro c x hx i
  have h := (coordProj i).continuous.comp
    ((mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)).continuous.comp
      (vector_orbit_continuous rho Y hY ((chartAt FourSpace c).symm x)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Continuous actual tensor sections have genuine, invariant, idempotent Haar averages
and genuinely integrable zero-average complements. -/
theorem continuous_cov2_projection (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2EvaluationContinuous u) :
    Cov2HaarIntegrable rho u ∧
    IsInvariantCov2 rho (cov2Pi0 rho u) ∧
    Cov2HaarIntegrable rho (cov2Pi0 rho u) ∧
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
    Cov2HaarIntegrable rho (cov2PiPerp rho u) ∧
    IsNonzeroCov2 rho (cov2PiPerp rho u) := by
  have hint := cov2_haar_integrable_of_continuous rho u hu
  exact ⟨hint, cov2_projection rho u hint⟩

/-- The corresponding pointwise theorem for continuous actual covector sections. -/
theorem continuous_covector_projection (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) :
    CovectorHaarIntegrable rho u ∧
    IsInvariantCovector rho (covectorPi0 rho u) ∧
    CovectorHaarIntegrable rho (covectorPi0 rho u) ∧
    covectorPi0 rho (covectorPi0 rho u) = covectorPi0 rho u ∧
    CovectorHaarIntegrable rho (covectorPiPerp rho u) ∧
    IsNonzeroCovector rho (covectorPiPerp rho u) := by
  have hint := covector_haar_integrable_of_continuous rho u hu
  exact ⟨hint, covector_projection rho u hint⟩

/-- The corresponding pointwise theorem for continuous actual vector sections,
using the differential of the inverse action. -/
theorem continuous_vector_projection (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorSectionContinuous Y) :
    VectorHaarIntegrable rho Y ∧
    IsInvariantVector rho (vectorPi0 rho Y) ∧
    VectorHaarIntegrable rho (vectorPi0 rho Y) ∧
    vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
    VectorHaarIntegrable rho (vectorPiPerp rho Y) ∧
    IsNonzeroVector rho (vectorPiPerp rho Y) := by
  have hint := vector_haar_integrable_of_continuous rho Y hY
  exact ⟨hint, vector_projection rho Y hint⟩

/-- Unified pointwise Haar projection theorem for the three actual section types.
This asserts no Hölder or Sobolev regularity or estimate for either projection. -/
theorem continuous_haar_projection_sectors (rho : CircleAction M) :
    (∀ u : RawCov2 M, Cov2EvaluationContinuous u →
      Cov2HaarIntegrable rho u ∧
      IsInvariantCov2 rho (cov2Pi0 rho u) ∧
      Cov2HaarIntegrable rho (cov2Pi0 rho u) ∧
      cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
      Cov2HaarIntegrable rho (cov2PiPerp rho u) ∧
      IsNonzeroCov2 rho (cov2PiPerp rho u)) ∧
    (∀ eta : RawCovector M, CovectorEvaluationContinuous eta →
      CovectorHaarIntegrable rho eta ∧
      IsInvariantCovector rho (covectorPi0 rho eta) ∧
      CovectorHaarIntegrable rho (covectorPi0 rho eta) ∧
      covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
      CovectorHaarIntegrable rho (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta)) ∧
    (∀ Y : RawVector M, VectorSectionContinuous Y →
      VectorHaarIntegrable rho Y ∧
      IsInvariantVector rho (vectorPi0 rho Y) ∧
      VectorHaarIntegrable rho (vectorPi0 rho Y) ∧
      vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
      VectorHaarIntegrable rho (vectorPiPerp rho Y) ∧
      IsNonzeroVector rho (vectorPiPerp rho Y)) :=
  ⟨continuous_cov2_projection rho, continuous_covector_projection rho,
    continuous_vector_projection rho⟩

end K24.Global.HaarSectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff
universe u

theorem solution {M : Type u} [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold I4 ∞ M] (rho : CircleAction M) :
    (∀ U : RawCov2 M,
      Continuous (fun q : {q : TangentBundle I4 M × TangentBundle I4 M //
        q.1.proj = q.2.proj} => U q.val.1.proj q.val.1.2 q.val.2.2) →
      Cov2HaarIntegrable rho U ∧
      IsInvariantCov2 rho (cov2Pi0 rho U) ∧
      Cov2HaarIntegrable rho (cov2Pi0 rho U) ∧
      cov2Pi0 rho (cov2Pi0 rho U) = cov2Pi0 rho U ∧
      Cov2HaarIntegrable rho (cov2PiPerp rho U) ∧
      IsNonzeroCov2 rho (cov2PiPerp rho U)) ∧
    (∀ eta : RawCovector M,
      Continuous (fun q : TangentBundle I4 M => eta q.proj q.2) →
      CovectorHaarIntegrable rho eta ∧
      IsInvariantCovector rho (covectorPi0 rho eta) ∧
      CovectorHaarIntegrable rho (covectorPi0 rho eta) ∧
      covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
      CovectorHaarIntegrable rho (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta)) ∧
    (∀ Y : RawVector M,
      Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M)) →
      VectorHaarIntegrable rho Y ∧
      IsInvariantVector rho (vectorPi0 rho Y) ∧
      VectorHaarIntegrable rho (vectorPi0 rho Y) ∧
      vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
      VectorHaarIntegrable rho (vectorPiPerp rho Y) ∧
      IsNonzeroVector rho (vectorPiPerp rho Y)) :=
  K24.Global.HaarSectors.continuous_haar_projection_sectors rho

theorem K24HAARProtocolExactType {M : Type u} [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold I4 ∞ M] (rho : CircleAction M) :
    (∀ U : RawCov2 M,
      Continuous (fun q : {q : TangentBundle I4 M × TangentBundle I4 M //
        q.1.proj = q.2.proj} => U q.val.1.proj q.val.1.2 q.val.2.2) →
      Cov2HaarIntegrable rho U ∧
      IsInvariantCov2 rho (cov2Pi0 rho U) ∧
      Cov2HaarIntegrable rho (cov2Pi0 rho U) ∧
      cov2Pi0 rho (cov2Pi0 rho U) = cov2Pi0 rho U ∧
      Cov2HaarIntegrable rho (cov2PiPerp rho U) ∧
      IsNonzeroCov2 rho (cov2PiPerp rho U)) ∧
    (∀ eta : RawCovector M,
      Continuous (fun q : TangentBundle I4 M => eta q.proj q.2) →
      CovectorHaarIntegrable rho eta ∧
      IsInvariantCovector rho (covectorPi0 rho eta) ∧
      CovectorHaarIntegrable rho (covectorPi0 rho eta) ∧
      covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
      CovectorHaarIntegrable rho (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta)) ∧
    (∀ Y : RawVector M,
      Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M)) →
      VectorHaarIntegrable rho Y ∧
      IsInvariantVector rho (vectorPi0 rho Y) ∧
      VectorHaarIntegrable rho (vectorPi0 rho Y) ∧
      vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
      VectorHaarIntegrable rho (vectorPiPerp rho Y) ∧
      IsNonzeroVector rho (vectorPiPerp rho Y)) :=
  solution rho

set_option pp.universes true in
#check @solution
#print axioms solution
#print axioms K24HAARProtocolExactType
