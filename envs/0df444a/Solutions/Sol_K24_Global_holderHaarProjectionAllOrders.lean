-- Prove2me | solution 1 for K24.Global.holderHaarProjectionAllOrders
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:14:55.438015+00:00
-- url     : https://prove2.me/submissions/4ca94120-0e1e-4efb-977c-39f3442f1620

import Definitions.Def_K24GlobalStatement


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
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise

namespace K24.Global.NativeContinuity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable {k : ℕ∞ω}

lemma trivialization_eq_chart_differential (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) (v : TangentSpace I4 p) :
    (trivializationAt FourSpace (TangentSpace I4) c ⟨p, v⟩).2 =
      mfderiv I4 I4 (chartAt FourSpace c) p v := by
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hp v,
    TangentBundle.continuousLinearMapAt_trivializationAt hp]
  rfl

lemma vector_trivialization_eq_coordinates (Y : RawVector M) (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) :
    (trivializationAt FourSpace (TangentSpace I4) c ⟨p, Y p⟩).2 =
      vectorInChart Y c (chartAt FourSpace c p) := by
  rw [trivialization_eq_chart_differential c p hp]
  change mfderiv I4 I4 (chartAt FourSpace c) p (Y p) =
    mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (Y ((chartAt FourSpace c).symm (chartAt FourSpace c p)))
  rw [(chartAt FourSpace c).left_inv hp]

lemma vector_section_continuous (Y : RawVector M) (hY : VectorContDiff k Y) :
    Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [FiberBundle.continuousAt_section FourSpace]
  have hcoord : ContinuousAt (vectorInChart Y p) (chartAt FourSpace p p) :=
    (hY p).continuousOn.continuousAt
      ((chartAt FourSpace p).open_target.mem_nhds (mem_chart_target FourSpace p))
  have hchart : ContinuousAt (chartAt FourSpace p) p :=
    (chartAt FourSpace p).continuousOn.continuousAt (chart_source_mem_nhds FourSpace p)
  apply (hcoord.comp hchart).congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds FourSpace p] with q hq
  exact vector_trivialization_eq_coordinates Y p q hq

lemma covector_evaluation_in_trivialization (eta : RawCovector M) (c : M)
    (q : TangentBundle I4 M) (hq : q.proj ∈ (chartAt FourSpace c).source) :
    eta q.proj q.2 = ∑ i : Fin 4,
      covectorInChart eta c (chartAt FourSpace c q.proj) i *
        (trivializationAt FourSpace (TangentSpace I4) c q).2 i := by
  have hr := congrArg (fun L => L q.2) (covector_chart_recovery eta c q.proj hq)
  rw [← hr]
  change coefficientsToCovector (covectorInChart eta c (chartAt FourSpace c q.proj))
    (mfderiv I4 I4 (chartAt FourSpace c) q.proj q.2) = _
  rw [← trivialization_eq_chart_differential c q.proj hq q.2]
  simp [coefficientsToCovector, coordProj]

lemma covector_evaluation_continuous (eta : RawCovector M)
    (heta : CovectorContDiff k eta) :
    Continuous (fun q : TangentBundle I4 M => eta q.proj q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := q.proj
  have hproj : ContinuousAt (fun z : TangentBundle I4 M => z.proj) q :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt
  have hchart : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousOn.continuousAt (chart_source_mem_nhds FourSpace c)
  have hcoord : ContinuousAt (covectorInChart eta c) (chartAt FourSpace c c) :=
    (heta c).continuousOn.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds (mem_chart_target FourSpace c))
  have hc := hcoord.comp_of_eq (hchart.comp_of_eq hproj rfl) rfl
  have htriv : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.proj ∈ (chartAt FourSpace c).source
        exact mem_chart_source FourSpace c))
  have hlocal : ContinuousAt (fun z : TangentBundle I4 M => ∑ i : Fin 4,
      covectorInChart eta c (chartAt FourSpace c z.proj) i *
        (trivializationAt FourSpace (TangentSpace I4) c z).2 i) q := by
    apply tendsto_finsetSum
    intro i hi
    exact ((continuous_apply i).continuousAt.comp hc).mul
      ((coordProj i).continuous.continuousAt.comp htriv.snd)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.preimage_mem_nhds (chart_source_mem_nhds FourSpace c)] with z hz
  exact covector_evaluation_in_trivialization eta c z hz

abbrev TangentPair (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  {q : TangentBundle I4 M × TangentBundle I4 M // q.1.proj = q.2.proj}

lemma cov2_evaluation_in_trivialization (U : RawCov2 M) (c : M)
    (q : TangentPair M) (hq : q.val.1.proj ∈ (chartAt FourSpace c).source) :
    U q.val.1.proj q.val.1.2 q.val.2.2 = ∑ i : Fin 4, ∑ j : Fin 4,
      (trivializationAt FourSpace (TangentSpace I4) c q.val.1).2 i *
        (cov2InChart U c (chartAt FourSpace c q.val.1.proj) i j *
          (trivializationAt FourSpace (TangentSpace I4) c q.val.2).2 j) := by
  rcases q with ⟨⟨⟨p, v⟩, ⟨r, w⟩⟩, hpr⟩
  change p = r at hpr
  subst r
  have hr := congrArg (fun L => L v w) (cov2_chart_recovery U c p hq)
  rw [← hr]
  change matrixToBilinear (cov2InChart U c (chartAt FourSpace c p))
    (mfderiv I4 I4 (chartAt FourSpace c) p v)
    (mfderiv I4 I4 (chartAt FourSpace c) p w) = _
  rw [← trivialization_eq_chart_differential c p hq v,
    ← trivialization_eq_chart_differential c p hq w]
  simp [matrixToBilinear, coordProj]

lemma cov2_evaluation_continuous (U : RawCov2 M) (hU : Cov2ContDiff k U) :
    Continuous (fun q : TangentPair M => U q.val.1.proj q.val.1.2 q.val.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := q.val.1.proj
  have hp1 : Continuous (fun z : TangentPair M => z.val.1) := continuous_subtype_val.fst
  have hp2 : Continuous (fun z : TangentPair M => z.val.2) := continuous_subtype_val.snd
  have hproj : ContinuousAt (fun z : TangentPair M => z.val.1.proj) q :=
    ((FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp hp1).continuousAt
  have hchart : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousOn.continuousAt (chart_source_mem_nhds FourSpace c)
  have hcoord : ContinuousAt (cov2InChart U c) (chartAt FourSpace c c) :=
    (hU c).continuousOn.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds (mem_chart_target FourSpace c))
  have hc := hcoord.comp_of_eq (hchart.comp_of_eq hproj rfl) rfl
  have ht1 : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q.val.1 :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.val.1.proj ∈ (chartAt FourSpace c).source
        exact mem_chart_source FourSpace c))
  have ht2 : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q.val.2 :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.val.2.proj ∈ (chartAt FourSpace c).source
        rw [← q.property]
        exact mem_chart_source FourSpace c))
  have hlocal : ContinuousAt (fun z : TangentPair M => ∑ i : Fin 4, ∑ j : Fin 4,
      (trivializationAt FourSpace (TangentSpace I4) c z.val.1).2 i *
        (cov2InChart U c (chartAt FourSpace c z.val.1.proj) i j *
          (trivializationAt FourSpace (TangentSpace I4) c z.val.2).2 j)) q := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact ((coordProj i).continuous.continuousAt.comp (ht1.comp_of_eq hp1.continuousAt rfl).snd).mul
      (((continuous_apply_apply i j).continuousAt.comp hc).mul
        ((coordProj j).continuous.continuousAt.comp (ht2.comp_of_eq hp2.continuousAt rfl).snd))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.preimage_mem_nhds (chart_source_mem_nhds FourSpace c)] with z hz
  exact cov2_evaluation_in_trivialization U c z hz

end K24.Global.NativeContinuity


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter IsManifold
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal

namespace K24.Global.CoverContinuity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

lemma projection_isOpenMap (F : LocalFiniteCover M) : IsOpenMap F.projection := by
  exact F.baseOpen.isOpenMap_subtype_val.comp F.covering.isOpenMap

lemma lift_smoothAt (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  have hc : c.coordinate ∈ maximalAtlas I4 ∞ F.TotalSpace :=
    subset_maximalAtlas c.coordinate_mem_atlas
  exact F.projectionSmooth.contMDiffAt.comp x
    (contMDiffAt_symm_of_mem_maximalAtlas hc (c.outerSubsetTarget hx))

lemma lift_map_nhds (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : map c.lift (𝓝 x) = 𝓝 (c.lift x) := by
  change map (F.projection ∘ c.coordinate.symm) (𝓝 x) = _
  rw [← map_map, c.coordinate.symm.map_nhds_eq (c.outerSubsetTarget hx)]
  exact (projection_isOpenMap F).map_nhds_eq F.projectionSmooth.continuous.continuousAt

lemma coord_smoothAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace d) ∘ c.lift) x := by
  exact ((contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I4) (n := ∞) d) hd).comp x
    (lift_smoothAt c x hx)).contDiffAt

lemma coord_map_nhds (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    map ((chartAt FourSpace d) ∘ c.lift) (𝓝 x) =
      𝓝 (chartAt FourSpace d (c.lift x)) := by
  rw [← map_map, lift_map_nhds c x hx, (chartAt FourSpace d).map_nhds_eq hd]

def frame (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) : FourSpace ≃L[ℝ] FourSpace :=
  (c.tangentMap x).trans
    ((trivializationAt FourSpace (TangentSpace I4) d).continuousLinearEquivAt ℝ (c.lift x) hd)

lemma frame_eq_fderiv (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    (frame c d x hd).toContinuousLinearMap =
      fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x := by
  change (((trivializationAt FourSpace (TangentSpace I4) d).continuousLinearEquivAt ℝ
    (c.lift x) hd).toContinuousLinearMap).comp (c.tangentMap x).toContinuousLinearMap = _
  rw [Trivialization.coe_continuousLinearEquivAt_eq',
    TangentBundle.continuousLinearMapAt_trivializationAt hd]
  change (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)).comp
    (c.tangentMap x).toContinuousLinearMap = _
  rw [c.tangentMap_eq x hx]
  erw [← mfderiv_comp x
    ((contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I4) (n := ∞) d) hd).mdifferentiableAt (by simp))
    ((lift_smoothAt c x hx).mdifferentiableAt (by simp))]
  exact mfderiv_eq_fderiv

lemma frame_apply (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (v : FourSpace) :
    frame c d x hd v = mfderiv I4 I4 (chartAt FourSpace d) (c.lift x) (c.tangentMap x v) := by
  change ((trivializationAt FourSpace (TangentSpace I4) d).continuousLinearEquivAt ℝ
    (c.lift x) hd) (c.tangentMap x v) = _
  rw [← ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq',
    TangentBundle.continuousLinearMapAt_trivializationAt hd]
  rfl

lemma liftedCovector_apply (c : LocalCoverChart F) (eta : RawCovector M)
    (x a : FourSpace) :
    coefficientsToCovector (c.liftedCovector eta x) a = eta (c.lift x) (c.tangentMap x a) := by
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L a)
    (coefficientsToCovector_recover ((eta (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap))

lemma liftedCov2_apply (c : LocalCoverChart F) (U : RawCov2 M)
    (x a b : FourSpace) :
    matrixToBilinear (c.liftedCov2 U x) a b =
      U (c.lift x) (c.tangentMap x a) (c.tangentMap x b) := by
  exact congrArg (fun L : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) => L a b)
    (matrixToBilinear_recover (bilinearPullback (U (c.lift x)) (c.tangentMap x).toContinuousLinearMap))

lemma vector_coord_lift (c : LocalCoverChart F) (Y : RawVector M) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    vectorInChart Y d (chartAt FourSpace d (c.lift x)) =
      fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (c.liftedVector Y x) := by
  rw [← frame_eq_fderiv c d x hx hd]
  rw [ContinuousLinearEquiv.coe_coe, frame_apply]
  dsimp only [vectorInChart, LocalCoverChart.liftedVector]
  erw [(chartAt FourSpace d).left_inv hd, ContinuousLinearEquiv.apply_symm_apply]

lemma covector_coord_lift (c : LocalCoverChart F) (eta : RawCovector M) (d : M)
    (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    covectorInChart eta d (chartAt FourSpace d (c.lift x)) i =
      coefficientsToCovector (c.liftedCovector eta x)
        ((fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x).inverse (basisVector i)) := by
  rw [← frame_eq_fderiv c d x hx hd, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.coe_coe, liftedCovector_apply]
  have hr := congrArg (fun L => L (c.tangentMap x ((frame c d x hd).symm (basisVector i))))
    (covector_chart_recovery eta d (c.lift x) hd)
  change coefficientsToCovector (covectorInChart eta d (chartAt FourSpace d (c.lift x)))
    (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)
      (c.tangentMap x ((frame c d x hd).symm (basisVector i)))) = _ at hr
  rw [← frame_apply c d x hd, ContinuousLinearEquiv.apply_symm_apply] at hr
  simpa [coefficientsToCovector, coordProj, basisVector] using hr

lemma cov2_coord_lift (c : LocalCoverChart F) (U : RawCov2 M) (d : M)
    (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    cov2InChart U d (chartAt FourSpace d (c.lift x)) i j =
      matrixToBilinear (c.liftedCov2 U x)
        ((fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x).inverse (basisVector i))
        ((fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x).inverse (basisVector j)) := by
  rw [← frame_eq_fderiv c d x hx hd, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.coe_coe, liftedCov2_apply]
  have hr := congrArg (fun L =>
      L (c.tangentMap x ((frame c d x hd).symm (basisVector i)))
        (c.tangentMap x ((frame c d x hd).symm (basisVector j))))
    (cov2_chart_recovery U d (c.lift x) hd)
  change matrixToBilinear (cov2InChart U d (chartAt FourSpace d (c.lift x)))
    (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)
      (c.tangentMap x ((frame c d x hd).symm (basisVector i))))
    (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)
      (c.tangentMap x ((frame c d x hd).symm (basisVector j)))) = _ at hr
  rw [← frame_apply c d x hd, ← frame_apply c d x hd, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply] at hr
  simpa [matrixToBilinear, coordProj, basisVector] using hr

lemma inverse_frame_continuousAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContinuousAt (fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse) x := by
  have hi := (contDiffAt_map_inverse (𝕜 := ℝ) (n := (0 : ℕ∞ω)) (frame c d x hd)).continuousAt
  rw [frame_eq_fderiv c d x hx hd] at hi
  exact hi.comp ((coord_smoothAt c d x hx hd).continuousAt_fderiv (by simp))

lemma covector_eval_continuous :
    Continuous (fun q : (Fin 4 → ℝ) × FourSpace => coefficientsToCovector q.1 q.2) := by
  simp only [coefficientsToCovector, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, coordProj]
  fun_prop

lemma cov2_eval_continuous :
    Continuous (fun q : Mat4 × (FourSpace × FourSpace) => matrixToBilinear q.1 q.2.1 q.2.2) := by
  simp only [matrixToBilinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, coordProj]
  fun_prop

lemma continuousAt_of_coord_lift {E : Type*} [TopologicalSpace E]
    (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (f : FourSpace → E) (hf : ContinuousAt (f ∘ (chartAt FourSpace d) ∘ c.lift) x) :
    ContinuousAt f (chartAt FourSpace d (c.lift x)) := by
  change map f (𝓝 (chartAt FourSpace d (c.lift x))) ≤ _
  rw [← coord_map_nhds c d x hx hd, map_map]
  exact hf

lemma vector_coord_lift_continuousAt (c : LocalCoverChart F) (Y : RawVector M) (d : M)
    (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hY : ContinuousOn (c.liftedVector Y) c.innerDomain) :
    ContinuousAt (vectorInChart Y d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hY.continuousAt (c.innerOpen.mem_nhds hx)
  have hderiv := (coord_smoothAt c d x hxo hd).continuousAt_fderiv (by simp)
  have hlocal := hderiv.clm_apply hcoeff
  apply continuousAt_of_coord_lift c d x hxo hd
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact vector_coord_lift c Y d y hy hyd

lemma covector_coord_lift_continuousAt (c : LocalCoverChart F) (eta : RawCovector M) (d : M)
    (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (heta : ContinuousOn (c.liftedCovector eta) c.innerDomain) :
    ContinuousAt (covectorInChart eta d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := heta.continuousAt (c.innerOpen.mem_nhds hx)
  have hinv := inverse_frame_continuousAt c d x hxo hd
  apply continuousAt_of_coord_lift c d x hxo hd
  apply continuousAt_pi.mpr
  intro i
  have hlocal := covector_eval_continuous.continuousAt.comp
    (hcoeff.prodMk (hinv.clm_apply (continuousAt_const (y := basisVector i))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact covector_coord_lift c eta d y hy hyd i

lemma cov2_coord_lift_continuousAt (c : LocalCoverChart F) (U : RawCov2 M) (d : M)
    (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hU : ContinuousOn (c.liftedCov2 U) c.innerDomain) :
    ContinuousAt (cov2InChart U d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hU.continuousAt (c.innerOpen.mem_nhds hx)
  have hinv := inverse_frame_continuousAt c d x hxo hd
  apply continuousAt_of_coord_lift c d x hxo hd
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hlocal := cov2_eval_continuous.continuousAt.comp
    (hcoeff.prodMk ((hinv.clm_apply (continuousAt_const (y := basisVector i))).prodMk
      (hinv.clm_apply (continuousAt_const (y := basisVector j)))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact cov2_coord_lift c U d y hy hyd i j

theorem vectorContDiff_zero_of_lifted_continuous (C : BoundedLocalCover M) (Y : RawVector M)
    (hY : ∀ ν : C.Index, ContinuousOn ((C.chart ν).liftedVector Y) (C.chart ν).innerDomain) :
    VectorContDiff 0 Y := by
  intro d
  rw [contDiffOn_zero]
  intro z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := vector_coord_lift_continuousAt (C.chart ν) Y d x hx hd (hY ν)
  rw [hchart] at h
  exact h.continuousWithinAt

theorem covectorContDiff_zero_of_lifted_continuous (C : BoundedLocalCover M) (eta : RawCovector M)
    (heta : ∀ ν : C.Index, ContinuousOn ((C.chart ν).liftedCovector eta) (C.chart ν).innerDomain) :
    CovectorContDiff 0 eta := by
  intro d
  rw [contDiffOn_zero]
  intro z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := covector_coord_lift_continuousAt (C.chart ν) eta d x hx hd (heta ν)
  rw [hchart] at h
  exact h.continuousWithinAt

theorem cov2ContDiff_zero_of_lifted_continuous (C : BoundedLocalCover M) (U : RawCov2 M)
    (hU : ∀ ν : C.Index, ContinuousOn ((C.chart ν).liftedCov2 U) (C.chart ν).innerDomain) :
    Cov2ContDiff 0 U := by
  intro d
  rw [contDiffOn_zero]
  intro z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := cov2_coord_lift_continuousAt (C.chart ν) U d x hx hd (hU ν)
  rw [hchart] at h
  exact h.continuousWithinAt

theorem vectorHolder_native_contDiff_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (Y : RawVector M) (hY : C.VectorHolder k α Y) : VectorContDiff 0 Y :=
  vectorContDiff_zero_of_lifted_continuous C Y (fun ν => (hY.1 ν).continuousOn)

theorem covectorHolder_native_contDiff_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (eta : RawCovector M) (heta : C.CovectorHolder k α eta) : CovectorContDiff 0 eta :=
  covectorContDiff_zero_of_lifted_continuous C eta (fun ν => (heta.1 ν).continuousOn)

theorem cov2Holder_native_contDiff_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U : RawCov2 M) (hU : C.Cov2Holder k α U) : Cov2ContDiff 0 U :=
  cov2ContDiff_zero_of_lifted_continuous C U (fun ν => (hU.1 ν).continuousOn)

end K24.Global.CoverContinuity


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global.HolderProjectionZero

variable {D V : Type*} [MetricSpace D] [NormedAddCommGroup V] [NormedSpace ℝ V]

def zeroENorm (α : ℝ≥0) (f : D → V) : ℝ≥0∞ :=
  (⨆ x, ‖f x‖ₑ) + eHolderNorm α f

lemma eHolderNorm_eq_iSup_ratio (α : ℝ≥0) (f : D → V) :
    eHolderNorm α f = ⨆ x, ⨆ y, edist (f x) (f y) / edist x y ^ (α : ℝ) := by
  have hd0 (x y : D) (hxy : x ≠ y) : edist x y ^ (α : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (edist_pos.mpr hxy) (edist_lt_top x y).ne).ne'
  have hdt (x y : D) : edist x y ^ (α : ℝ) ≠ ⊤ := by
    exact (ENNReal.rpow_lt_top_of_nonneg α.coe_nonneg (edist_lt_top x y).ne).ne
  apply le_antisymm
  · by_cases ht : (⨆ x, ⨆ y, edist (f x) (f y) / edist x y ^ (α : ℝ)) = ⊤
    · simp [ht]
    let C := (⨆ x, ⨆ y, edist (f x) (f y) / edist x y ^ (α : ℝ)).toNNReal
    have hC : HolderWith C α f := by
      intro x y
      change edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (α : ℝ)
      rw [show (C : ℝ≥0∞) = _ from ENNReal.coe_toNNReal ht]
      by_cases hxy : x = y
      · simp [hxy]
      exact (ENNReal.div_le_iff (hd0 x y hxy) (hdt x y)).mp
        (le_iSup_of_le x (le_iSup (fun y => edist (f x) (f y) / edist x y ^ (α : ℝ)) y))
    exact hC.eHolderNorm_le.trans_eq (ENNReal.coe_toNNReal ht)
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : x = y
    · simp [hxy]
    exact le_iInf₂ fun C hC => (ENNReal.div_le_iff (hd0 x y hxy) (hdt x y)).mpr (hC x y)

lemma zeroENorm_integral_le {T : Type*} [MeasurableSpace T] (μ : Measure T)
    [IsProbabilityMeasure μ] [CompleteSpace V] [Nonempty D]
    (α : ℝ≥0) (f : T → D → V) (B : ℝ≥0∞)
    (hf : ∀ x, Integrable (fun t => f t x) μ)
    (hbound : ∀ t, zeroENorm α (f t) ≤ B) :
    zeroENorm α (fun x => ∫ t, f t x ∂μ) ≤ B := by
  rw [zeroENorm, eHolderNorm_eq_iSup_ratio, ENNReal.iSup_add]
  apply iSup_le
  intro x
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro y
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro z
  rw [edist_eq_enorm_sub, ← integral_sub (hf y) (hf z)]
  calc
    _ ≤ (∫⁻ t, ‖f t x‖ₑ ∂μ) +
        (∫⁻ t, ‖f t y - f t z‖ₑ ∂μ) / edist y z ^ (α : ℝ) := by
      exact add_le_add (enorm_integral_le_lintegral_enorm _)
        (by gcongr; exact enorm_integral_le_lintegral_enorm _)
    _ = ∫⁻ t, ‖f t x‖ₑ + ‖f t y - f t z‖ₑ / edist y z ^ (α : ℝ) ∂μ := by
      have hm : AEMeasurable (fun t => ‖f t y - f t z‖ₑ) μ :=
        ((hf y).sub (hf z)).aestronglyMeasurable.enorm
      rw [div_eq_mul_inv, ← lintegral_mul_const'' _ hm,
        ← lintegral_add_left' (hf x).aestronglyMeasurable.enorm]
      rfl
    _ ≤ ∫⁻ _ : T, B ∂μ := by
      apply lintegral_mono
      intro t
      apply le_trans _ (hbound t)
      rw [zeroENorm, eHolderNorm_eq_iSup_ratio]
      exact add_le_add (le_iSup (fun x => ‖f t x‖ₑ) x)
        (by rw [← edist_eq_enorm_sub]; exact le_iSup_of_le y (le_iSup (fun z => edist (f t y) (f t z) / edist y z ^ (α : ℝ)) z))
    _ = B := by simp

lemma zeroENorm_add_le (α : ℝ≥0) (f g : D → V) :
    zeroENorm α (f + g) ≤ zeroENorm α f + zeroENorm α g := by
  calc
    _ ≤ ((⨆ x, ‖f x‖ₑ) + (⨆ x, ‖g x‖ₑ)) +
      (eHolderNorm α f + eHolderNorm α g) := by
      exact add_le_add (iSup_le fun x => (enorm_add_le (f x) (g x)).trans
        (add_le_add (le_iSup (fun x => ‖f x‖ₑ) x) (le_iSup (fun x => ‖g x‖ₑ) x)))
        eHolderNorm_add_le
    _ = _ := by unfold zeroENorm; ac_rfl

lemma zeroENorm_neg (α : ℝ≥0) (f : D → V) : zeroENorm α (-f) = zeroENorm α f := by
  have hh : eHolderNorm α (-f) = eHolderNorm α f := by
    simpa using (eHolderNorm_smul (r := α) (f := f) (-1 : ℝ))
  simp only [zeroENorm, Pi.neg_apply, enorm_neg, hh]

lemma zeroENorm_sub_le (α : ℝ≥0) (f g : D → V) :
    zeroENorm α (f - g) ≤ zeroENorm α f + zeroENorm α g := by
  simpa only [sub_eq_add_neg, zeroENorm_neg] using zeroENorm_add_le α f (-g)

lemma coordinateHolderENorm_zero_eq (α : ℝ≥0) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) (f : E → V) :
    coordinateHolderENorm 0 α s f = zeroENorm α (fun x : s => f x) := by
  have hnorm (x : s) :
      (‖iteratedFDerivWithin ℝ 0 f s x‖₊ : ℝ≥0∞) = ‖f x‖ₑ := by
    change (‖iteratedFDerivWithin ℝ 0 f s x‖₊ : ℝ≥0∞) = (‖f x‖₊ : ℝ≥0∞)
    congr 1
    apply Subtype.ext
    exact norm_iteratedFDerivWithin_zero
  have hholder (C : ℝ≥0) :
      HolderWith C α (fun x : s => iteratedFDerivWithin ℝ 0 f s x) ↔
        HolderWith C α (fun x : s => f x) := by
    simp only [HolderWith, edist_dist, dist_iteratedFDerivWithin_zero]
  simp only [coordinateHolderENorm, zero_add, Finset.range_one, Finset.sum_singleton,
    derivativeENorm, hnorm, zeroENorm, eHolderNorm, hholder]

lemma contDiffOn_zero_of_coordinateHolderENorm_finite (α : ℝ≥0) (hα : 0 < α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (f : E → V) (hf : coordinateHolderENorm 0 α s f < ⊤) :
    ContDiffOn ℝ 0 f s := by
  rw [coordinateHolderENorm_zero_eq] at hf
  have hm : MemHolder α (fun x : s => f x) := eHolderNorm_lt_top.mp (lt_of_le_of_lt le_add_self hf)
  exact contDiffOn_zero.mpr (continuousOn_iff_continuous_domRestrict.mpr
    (hm.holderWith.continuous hα))

end K24.Global.HolderProjectionZero


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.HolderProjectionZero
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

lemma liftedCov2_orbit_integrable (c : LocalCoverChart F) (rho : CircleAction M)
    (U : RawCov2 M) (hU : Cov2HaarIntegrable rho U) (x : FourSpace) :
    Integrable (fun t => c.liftedCov2 (actionPullbackCov2 rho t U) x) circleHaar := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  exact HaarSectors.cov2_orbit_integrable rho U hU (c.lift x)
    (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j))

lemma liftedCovector_orbit_integrable (c : LocalCoverChart F) (rho : CircleAction M)
    (eta : RawCovector M) (heta : CovectorHaarIntegrable rho eta) (x : FourSpace) :
    Integrable (fun t => c.liftedCovector (actionPullbackCovector rho t eta) x) circleHaar := by
  apply Integrable.of_eval
  intro i
  exact HaarSectors.covector_orbit_integrable rho eta heta (c.lift x)
    (c.tangentMap x (basisVector i))

lemma liftedVector_orbit_integrable (c : LocalCoverChart F) (rho : CircleAction M)
    (Y : RawVector M) (hY : VectorHaarIntegrable rho Y) (x : FourSpace) :
    Integrable (fun t => c.liftedVector (actionPullbackVector rho t Y) x) circleHaar := by
  let L : FourSpace →L[ℝ] FourSpace := (c.tangentMap x).symm.toContinuousLinearMap
  have hi : Integrable (fun t => (actionPullbackVector rho t Y (c.lift x) : FourSpace)) circleHaar :=
    HaarSectors.vector_orbit_integrable rho Y hY (c.lift x)
  exact L.integrable_comp hi

lemma liftedCov2_Pi0 (c : LocalCoverChart F) (rho : CircleAction M)
    (U : RawCov2 M) (hU : Cov2HaarIntegrable rho U) (x : FourSpace) :
    c.liftedCov2 (cov2Pi0 rho U) x =
      ∫ t, c.liftedCov2 (actionPullbackCov2 rho t U) x ∂circleHaar := by
  have hi := liftedCov2_orbit_integrable c rho U hU x
  ext i j
  rw [eval_integral (fun i => hi.eval i), eval_integral (fun j => (hi.eval i).eval j)]
  exact HaarSectors.cov2Pi0_apply rho U hU (c.lift x)
    (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j))

lemma liftedCovector_Pi0 (c : LocalCoverChart F) (rho : CircleAction M)
    (eta : RawCovector M) (heta : CovectorHaarIntegrable rho eta) (x : FourSpace) :
    c.liftedCovector (covectorPi0 rho eta) x =
      ∫ t, c.liftedCovector (actionPullbackCovector rho t eta) x ∂circleHaar := by
  have hi := liftedCovector_orbit_integrable c rho eta heta x
  ext i
  rw [eval_integral (fun i => hi.eval i)]
  exact HaarSectors.covectorPi0_apply rho eta heta (c.lift x)
    (c.tangentMap x (basisVector i))

lemma liftedVector_Pi0 (c : LocalCoverChart F) (rho : CircleAction M)
    (Y : RawVector M) (hY : VectorHaarIntegrable rho Y) (x : FourSpace) :
    c.liftedVector (vectorPi0 rho Y) x =
      ∫ t, c.liftedVector (actionPullbackVector rho t Y) x ∂circleHaar := by
  let L : FourSpace →L[ℝ] FourSpace := (c.tangentMap x).symm.toContinuousLinearMap
  have hi : Integrable (fun t => (actionPullbackVector rho t Y (c.lift x) : FourSpace)) circleHaar :=
    HaarSectors.vector_orbit_integrable rho Y hY (c.lift x)
  change L (vectorPi0 rho Y (c.lift x)) = ∫ t, L (actionPullbackVector rho t Y (c.lift x)) ∂circleHaar
  rw [HaarSectors.vectorPi0_eq_integral rho Y hY]
  exact (L.integral_comp_comm hi).symm



lemma liftedCov2_sub (c : LocalCoverChart F) (U V : RawCov2 M) (x : FourSpace) :
    c.liftedCov2 (U - V) x = c.liftedCov2 U x - c.liftedCov2 V x := by
  rfl

lemma cov2Pi0_enorm_le (C : BoundedLocalCover M) (α : ℝ≥0) (rho : CircleAction M)
    (U : RawCov2 M) (hU : Cov2HaarIntegrable rho U) (B : ℝ≥0∞)
    (hb : ∀ t, C.cov2ENorm 0 α (actionPullbackCov2 rho t U) ≤ B) :
    C.cov2ENorm 0 α (cov2Pi0 rho U) ≤ B := by
  apply iSup_le
  intro ν
  letI : Nonempty (C.chart ν).innerDomain := (C.chart ν).innerNonempty.to_subtype
  rw [coordinateHolderENorm_zero_eq]
  have hi := zeroENorm_integral_le circleHaar α
    (fun t (x : (C.chart ν).innerDomain) => (C.chart ν).liftedCov2 (actionPullbackCov2 rho t U) x)
    B (fun x => liftedCov2_orbit_integrable (C.chart ν) rho U hU x) ?_
  · simpa only [← liftedCov2_Pi0 (C.chart ν) rho U hU] using hi
  · intro t
    rw [← coordinateHolderENorm_zero_eq]
    exact (le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCov2 (actionPullbackCov2 rho t U))) ν).trans (hb t)

lemma cov2ENorm_zero_sub_le (C : BoundedLocalCover M) (α : ℝ≥0) (U V : RawCov2 M) :
    C.cov2ENorm 0 α (U - V) ≤ C.cov2ENorm 0 α U + C.cov2ENorm 0 α V := by
  apply iSup_le
  intro ν
  rw [coordinateHolderENorm_zero_eq]
  simp only [liftedCov2_sub]
  have hh := zeroENorm_sub_le α
    (fun x : (C.chart ν).innerDomain => (C.chart ν).liftedCov2 U x)
    (fun x : (C.chart ν).innerDomain => (C.chart ν).liftedCov2 V x)
  apply hh.trans
  apply add_le_add
  · rw [← coordinateHolderENorm_zero_eq]
    exact le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCov2 U)) ν
  · rw [← coordinateHolderENorm_zero_eq]
    exact le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCov2 V)) ν

lemma cov2Holder_zero_of_finite (C : BoundedLocalCover M) (α : ℝ≥0) (hα : 0 < α)
    (U : RawCov2 M) (hU : C.cov2ENorm 0 α U < ⊤) : C.Cov2Holder 0 α U := by
  refine ⟨?_, hU⟩
  intro ν
  apply contDiffOn_zero_of_coordinateHolderENorm_finite α hα
  exact (le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
    ((C.chart ν).liftedCov2 U)) ν).trans_lt hU

lemma liftedCovector_sub (c : LocalCoverChart F) (U V : RawCovector M) (x : FourSpace) :
    c.liftedCovector (U - V) x = c.liftedCovector U x - c.liftedCovector V x := by
  rfl

lemma covectorPi0_enorm_le (C : BoundedLocalCover M) (α : ℝ≥0) (rho : CircleAction M)
    (U : RawCovector M) (hU : CovectorHaarIntegrable rho U) (B : ℝ≥0∞)
    (hb : ∀ t, C.covectorENorm 0 α (actionPullbackCovector rho t U) ≤ B) :
    C.covectorENorm 0 α (covectorPi0 rho U) ≤ B := by
  apply iSup_le
  intro ν
  letI : Nonempty (C.chart ν).innerDomain := (C.chart ν).innerNonempty.to_subtype
  rw [coordinateHolderENorm_zero_eq]
  have hi := zeroENorm_integral_le circleHaar α
    (fun t (x : (C.chart ν).innerDomain) => (C.chart ν).liftedCovector (actionPullbackCovector rho t U) x)
    B (fun x => liftedCovector_orbit_integrable (C.chart ν) rho U hU x) ?_
  · simpa only [← liftedCovector_Pi0 (C.chart ν) rho U hU] using hi
  · intro t
    rw [← coordinateHolderENorm_zero_eq]
    exact (le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCovector (actionPullbackCovector rho t U))) ν).trans (hb t)

lemma covectorENorm_zero_sub_le (C : BoundedLocalCover M) (α : ℝ≥0) (U V : RawCovector M) :
    C.covectorENorm 0 α (U - V) ≤ C.covectorENorm 0 α U + C.covectorENorm 0 α V := by
  apply iSup_le
  intro ν
  rw [coordinateHolderENorm_zero_eq]
  simp only [liftedCovector_sub]
  have hh := zeroENorm_sub_le α
    (fun x : (C.chart ν).innerDomain => (C.chart ν).liftedCovector U x)
    (fun x : (C.chart ν).innerDomain => (C.chart ν).liftedCovector V x)
  apply hh.trans
  apply add_le_add
  · rw [← coordinateHolderENorm_zero_eq]
    exact le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCovector U)) ν
  · rw [← coordinateHolderENorm_zero_eq]
    exact le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCovector V)) ν

lemma covectorHolder_zero_of_finite (C : BoundedLocalCover M) (α : ℝ≥0) (hα : 0 < α)
    (U : RawCovector M) (hU : C.covectorENorm 0 α U < ⊤) : C.CovectorHolder 0 α U := by
  refine ⟨?_, hU⟩
  intro ν
  apply contDiffOn_zero_of_coordinateHolderENorm_finite α hα
  exact (le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
    ((C.chart ν).liftedCovector U)) ν).trans_lt hU

lemma liftedVector_sub (c : LocalCoverChart F) (U V : RawVector M) (x : FourSpace) :
    c.liftedVector (U - V) x = c.liftedVector U x - c.liftedVector V x := by
  simp only [LocalCoverChart.liftedVector, Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply]

lemma vectorPi0_enorm_le (C : BoundedLocalCover M) (α : ℝ≥0) (rho : CircleAction M)
    (U : RawVector M) (hU : VectorHaarIntegrable rho U) (B : ℝ≥0∞)
    (hb : ∀ t, C.vectorENorm 0 α (actionPullbackVector rho t U) ≤ B) :
    C.vectorENorm 0 α (vectorPi0 rho U) ≤ B := by
  apply iSup_le
  intro ν
  letI : Nonempty (C.chart ν).innerDomain := (C.chart ν).innerNonempty.to_subtype
  rw [coordinateHolderENorm_zero_eq]
  have hi := zeroENorm_integral_le circleHaar α
    (fun t (x : (C.chart ν).innerDomain) => (C.chart ν).liftedVector (actionPullbackVector rho t U) x)
    B (fun x => liftedVector_orbit_integrable (C.chart ν) rho U hU x) ?_
  · simpa only [← liftedVector_Pi0 (C.chart ν) rho U hU] using hi
  · intro t
    rw [← coordinateHolderENorm_zero_eq]
    exact (le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedVector (actionPullbackVector rho t U))) ν).trans (hb t)

lemma vectorENorm_zero_sub_le (C : BoundedLocalCover M) (α : ℝ≥0) (U V : RawVector M) :
    C.vectorENorm 0 α (U - V) ≤ C.vectorENorm 0 α U + C.vectorENorm 0 α V := by
  apply iSup_le
  intro ν
  rw [coordinateHolderENorm_zero_eq]
  simp only [liftedVector_sub]
  have hh := zeroENorm_sub_le α
    (fun x : (C.chart ν).innerDomain => (C.chart ν).liftedVector U x)
    (fun x : (C.chart ν).innerDomain => (C.chart ν).liftedVector V x)
  apply hh.trans
  apply add_le_add
  · rw [← coordinateHolderENorm_zero_eq]
    exact le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedVector U)) ν
  · rw [← coordinateHolderENorm_zero_eq]
    exact le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedVector V)) ν

lemma vectorHolder_zero_of_finite (C : BoundedLocalCover M) (α : ℝ≥0) (hα : 0 < α)
    (U : RawVector M) (hU : C.vectorENorm 0 α U < ⊤) : C.VectorHolder 0 α U := by
  refine ⟨?_, hU⟩
  intro ν
  apply contDiffOn_zero_of_coordinateHolderENorm_finite α hα
  exact (le_iSup (fun ν => coordinateHolderENorm 0 α (C.chart ν).innerDomain
    ((C.chart ν).liftedVector U)) ν).trans_lt hU

lemma complement_enorm_bound (a b : ℝ≥0∞) (H : ℝ≥0) (hb : b ≤ (H : ℝ≥0∞) * a) :
    a + b ≤ ((1 + H : ℝ≥0) : ℝ≥0∞) * a := by
  calc
    a + b ≤ a + (H : ℝ≥0∞) * a := add_le_add le_rfl hb
    _ = _ := by simp only [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]

theorem holder_projection_order_zero (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (rho : CircleAction M) (hact : HolderActionControl C α H 0 rho) :
    HolderProjectionConclusions C α H 0 rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk U hU
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    have hc := NativeContinuity.cov2_evaluation_continuous U
      (CoverContinuity.cov2Holder_native_contDiff_zero C 0 α U hU)
    obtain ⟨hi, hinv, hii, hidem, hip, hnz⟩ := HaarSectors.continuous_cov2_projection rho U hc
    have hb : C.cov2ENorm 0 α (cov2Pi0 rho U) ≤ (H : ℝ≥0∞) * C.cov2ENorm 0 α U :=
      cov2Pi0_enorm_le C α rho U hi _ (fun t => (hact.tensor 0 le_rfl t U hU).2)
    have hbf : C.cov2ENorm 0 α (cov2Pi0 rho U) < ⊤ :=
      hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)
    have hp : C.cov2ENorm 0 α (cov2PiPerp rho U) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm 0 α U :=
      (cov2ENorm_zero_sub_le C α U (cov2Pi0 rho U)).trans
        (complement_enorm_bound (C.cov2ENorm 0 α U) (C.cov2ENorm 0 α (cov2Pi0 rho U)) H hb)
    have hpf : C.cov2ENorm 0 α (cov2PiPerp rho U) < ⊤ :=
      hp.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)
    exact ⟨hi, cov2Holder_zero_of_finite C α hα _ hbf,
      cov2Holder_zero_of_finite C α hα _ hpf, hinv, hidem, hnz, hb, hp⟩
  · intro k hk U hU
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    have hc := NativeContinuity.covector_evaluation_continuous U
      (CoverContinuity.covectorHolder_native_contDiff_zero C 0 α U hU)
    obtain ⟨hi, hinv, hii, hidem, hip, hnz⟩ := HaarSectors.continuous_covector_projection rho U hc
    have hb : C.covectorENorm 0 α (covectorPi0 rho U) ≤ (H : ℝ≥0∞) * C.covectorENorm 0 α U :=
      covectorPi0_enorm_le C α rho U hi _ (fun t => (hact.covector 0 le_rfl t U hU).2)
    have hbf : C.covectorENorm 0 α (covectorPi0 rho U) < ⊤ :=
      hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)
    have hp : C.covectorENorm 0 α (covectorPiPerp rho U) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * C.covectorENorm 0 α U :=
      (covectorENorm_zero_sub_le C α U (covectorPi0 rho U)).trans
        (complement_enorm_bound (C.covectorENorm 0 α U) (C.covectorENorm 0 α (covectorPi0 rho U)) H hb)
    have hpf : C.covectorENorm 0 α (covectorPiPerp rho U) < ⊤ :=
      hp.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)
    exact ⟨hi, covectorHolder_zero_of_finite C α hα _ hbf,
      covectorHolder_zero_of_finite C α hα _ hpf, hinv, hidem, hnz, hb, hp⟩
  · intro k hk U hU
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    have hc := NativeContinuity.vector_section_continuous U
      (CoverContinuity.vectorHolder_native_contDiff_zero C 0 α U hU)
    obtain ⟨hi, hinv, hii, hidem, hip, hnz⟩ := HaarSectors.continuous_vector_projection rho U hc
    have hb : C.vectorENorm 0 α (vectorPi0 rho U) ≤ (H : ℝ≥0∞) * C.vectorENorm 0 α U :=
      vectorPi0_enorm_le C α rho U hi _ (fun t => (hact.vector 0 le_rfl t U hU).2)
    have hbf : C.vectorENorm 0 α (vectorPi0 rho U) < ⊤ :=
      hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)
    have hp : C.vectorENorm 0 α (vectorPiPerp rho U) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * C.vectorENorm 0 α U :=
      (vectorENorm_zero_sub_le C α U (vectorPi0 rho U)).trans
        (complement_enorm_bound (C.vectorENorm 0 α U) (C.vectorENorm 0 α (vectorPi0 rho U)) H hb)
    have hpf : C.vectorENorm 0 α (vectorPiPerp rho U) < ⊤ :=
      hp.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)
    exact ⟨hi, vectorHolder_zero_of_finite C α hα _ hbf,
      vectorHolder_zero_of_finite C α hα _ hpf, hinv, hidem, hnz, hb, hp⟩

end K24.Global.HolderProjectionZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global.HolderProjectionFinite

variable {T V : Type*} [MeasurableSpace T] {μ : Measure T}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma derivative_reconstruct (L : FourSpace →L[ℝ] V) :
    (∑ i : Fin 4, (coordProj i).smulRight (L (basisVector i))) = L := by
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  change (∑ i : Fin 4, v i • L (basisVector i)) = L v
  calc
    _ = L (∑ i : Fin 4, v i • basisVector i) := by simp
    _ = L v := by rw [sum_basisVector]

lemma aestronglyMeasurable_derivative_apply
    (f : T → FourSpace → V) {s : Set FourSpace} {x : FourSpace} (hs : s ∈ 𝓝 x)
    (L : T → FourSpace →L[ℝ] V)
    (hf : ∀ y ∈ s, AEStronglyMeasurable (fun t => f t y) μ)
    (hd : ∀ t, HasFDerivAt (f t) (L t) x) (v : FourSpace) :
    AEStronglyMeasurable (fun t => L t v) μ := by
  classical
  let g : T → FourSpace → V := fun t y => if y ∈ s then f t y else 0
  have hg (y : FourSpace) : AEStronglyMeasurable (fun t => g t y) μ := by
    by_cases hy : y ∈ s
    · simpa only [g, if_pos hy] using hf y hy
    · simp only [g, if_neg hy]
      exact aestronglyMeasurable_const
  have hgd (t : T) : HasFDerivAt (g t) (L t) x := by
    apply (hd t).congr_of_eventuallyEq
    filter_upwards [hs] with y hy
    simp only [g, if_pos hy]
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ))
    (f := fun r t => r⁻¹ • (g t (x + r • v) - g t x))
  · intro r
    exact ((hg _).sub (hg _)).const_smul _
  · exact ae_of_all _ (fun t => (hgd t).hasLineDerivAt v |>.tendsto_slope_zero)

lemma aestronglyMeasurable_derivative
    (f : T → FourSpace → V) {s : Set FourSpace} {x : FourSpace} (hs : s ∈ 𝓝 x)
    (L : T → FourSpace →L[ℝ] V)
    (hf : ∀ y ∈ s, AEStronglyMeasurable (fun t => f t y) μ)
    (hd : ∀ t, HasFDerivAt (f t) (L t) x) :
    AEStronglyMeasurable L μ := by
  have hi (i : Fin 4) : AEStronglyMeasurable
      (fun t => (coordProj i).smulRight (L t (basisVector i))) μ :=
    (ContinuousLinearMap.smulRightL ℝ FourSpace V (coordProj i)).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_derivative_apply f hs L hf hd (basisVector i))
  have hsum := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hi i)
  change AEStronglyMeasurable (fun t => ∑ i : Fin 4, (coordProj i).smulRight (L t (basisVector i))) μ at hsum
  simpa only [derivative_reconstruct] using hsum

lemma aestronglyMeasurable_jet (f : T → FourSpace → V) (k : ℕ)
    {s : Set FourSpace} (hs : IsOpen s)
    (hf : ∀ t, ContDiffOn ℝ k (f t) s)
    (hm : ∀ x ∈ s, AEStronglyMeasurable (fun t => f t x) μ) :
    ∀ j : ℕ, j ≤ k → ∀ x ∈ s,
      AEStronglyMeasurable (fun t => iteratedFDerivWithin ℝ j (f t) s x) μ := by
  intro j
  induction j with
  | zero =>
    intro hj x hx
    simpa only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply] using
      (continuousMultilinearCurryFin0 ℝ FourSpace V).symm.continuous.comp_aestronglyMeasurable (hm x hx)
  | succ j ih =>
    intro hj x hx
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => FourSpace) V
    have hd (t : T) : HasFDerivAt (iteratedFDerivWithin ℝ j (f t) s)
        (curry (iteratedFDerivWithin ℝ (j + 1) (f t) s x)) x :=
      ((hf t).ftaylorSeriesWithin hs.uniqueDiffOn |>.fderivWithin j
        (by exact_mod_cast Nat.lt_of_succ_le hj) x hx).hasFDerivAt (hs.mem_nhds hx)
    have hmeas := aestronglyMeasurable_derivative
      (fun t => iteratedFDerivWithin ℝ j (f t) s) (hs.mem_nhds hx)
      (fun t => curry (iteratedFDerivWithin ℝ (j + 1) (f t) s x))
      (fun y hy => ih (Nat.le_of_succ_le hj) y hy) hd
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      curry.symm.continuous.comp_aestronglyMeasurable hmeas

lemma jet_enorm_le_coordinate (f : FourSpace → V) (k j : ℕ) (α : ℝ≥0)
    {s : Set FourSpace} (hj : j ≤ k) {x : FourSpace} (hx : x ∈ s) :
    ‖iteratedFDerivWithin ℝ j f s x‖ₑ ≤ coordinateHolderENorm k α s f := by
  apply le_trans (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)) ⟨x,hx⟩)
  apply le_trans (Finset.single_le_sum (fun i hi => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  exact le_add_right le_rfl

lemma contDiffOn_integral_and_jets [IsFiniteMeasure μ] [CompleteSpace V]
    (f : T → FourSpace → V) (k : ℕ) (α B : ℝ≥0)
    {s : Set FourSpace} (hs : IsOpen s)
    (hf : ∀ t, ContDiffOn ℝ k (f t) s)
    (hm : ∀ x ∈ s, AEStronglyMeasurable (fun t => f t x) μ)
    (hb : ∀ t, coordinateHolderENorm k α s (f t) ≤ (B : ℝ≥0∞)) :
    ContDiffOn ℝ k (fun x => ∫ t, f t x ∂μ) s ∧
      ∀ j : ℕ, j ≤ k → ∀ x ∈ s,
        iteratedFDerivWithin ℝ j (fun y => ∫ t, f t y ∂μ) s x =
          ∫ t, iteratedFDerivWithin ℝ j (f t) s x ∂μ := by
  have hmj := aestronglyMeasurable_jet f k hs hf hm
  have hbj (j : ℕ) (hj : j ≤ k) (x : FourSpace) (hx : x ∈ s) (t : T) :
      ‖iteratedFDerivWithin ℝ j (f t) s x‖ ≤ (B : ℝ) := by
    apply ENNReal.ofReal_le_coe.mp
    rw [ofReal_norm]
    exact (jet_enorm_le_coordinate (f t) k j α hj hx).trans (hb t)
  have hij (j : ℕ) (hj : j ≤ k) (x : FourSpace) (hx : x ∈ s) :
      Integrable (fun t => iteratedFDerivWithin ℝ j (f t) s x) μ :=
    (integrable_const (B : ℝ)).mono' (hmj j hj x hx) (ae_of_all _ (hbj j hj x hx))
  let J : FourSpace → FormalMultilinearSeries ℝ FourSpace V :=
    fun x j => ∫ t, iteratedFDerivWithin ℝ j (f t) s x ∂μ
  have ht : HasFTaylorSeriesUpToOn (k : ℕ∞) (fun x => ∫ t, f t x ∂μ) J s := by
    constructor
    · intro x hx
      let L := (continuousMultilinearCurryFin0 ℝ FourSpace V).toContinuousLinearEquiv.toContinuousLinearMap
      have hcomm := L.integral_comp_comm (hij 0 (Nat.zero_le k) x hx)
      change L (∫ t, iteratedFDerivWithin ℝ 0 (f t) s x ∂μ) = _
      rw [← hcomm]
      congr 1
    · intro j hj x hx
      have hjk : j < k := by exact_mod_cast hj
      let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => FourSpace) V
      let L : (FourSpace [×(j + 1)]→L[ℝ] V) →L[ℝ] (FourSpace →L[ℝ] (FourSpace [×j]→L[ℝ] V)) :=
        { toLinearMap := curry.toLinearEquiv.toLinearMap, cont := curry.continuous }
      have hd (t : T) (y : FourSpace) (hy : y ∈ s) :
          HasFDerivAt (iteratedFDerivWithin ℝ j (f t) s)
            (L (iteratedFDerivWithin ℝ (j + 1) (f t) s y)) y :=
        ((hf t).ftaylorSeriesWithin hs.uniqueDiffOn |>.fderivWithin j
          (by exact_mod_cast hjk) y hy).hasFDerivAt (hs.mem_nhds hy)
      have hdiff := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
        (F := fun y t => iteratedFDerivWithin ℝ j (f t) s y)
        (F' := fun y t => L (iteratedFDerivWithin ℝ (j + 1) (f t) s y))
        (bound := fun _ => (B : ℝ)) (hs.mem_nhds hx)
        (Filter.mem_of_superset (hs.mem_nhds hx) (fun y hy => hmj j hjk.le y hy))
        (hij j hjk.le x hx)
        (L.continuous.comp_aestronglyMeasurable (hmj (j + 1) hjk x hx))
        (ae_of_all _ (fun t y hy => by
          change ‖curry (iteratedFDerivWithin ℝ (j + 1) (f t) s y)‖ ≤ (B : ℝ)
          rw [curry.norm_map]
          exact hbj (j + 1) hjk y hy t))
        (integrable_const _) (ae_of_all _ hd)
      have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
        (E := FourSpace [×(j + 1)]→L[ℝ] V)
        (Fₗ := FourSpace →L[ℝ] (FourSpace [×j]→L[ℝ] V)) L (hij (j + 1) hjk x hx)
      rw [hc] at hdiff
      exact hdiff.hasFDerivWithinAt
    · intro j hj
      have hjk : j ≤ k := by exact_mod_cast hj
      apply continuousOn_of_dominated (bound := fun _ => (B : ℝ))
        (fun x hx => hmj j hjk x hx)
        (fun x hx => ae_of_all _ (hbj j hjk x hx)) (integrable_const _)
      exact ae_of_all _ (fun t => (hf t).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast hjk) hs.uniqueDiffOn)
  refine ⟨ht.contDiffOn, ?_⟩
  intro j hj x hx
  exact (ht.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hj) hs.uniqueDiffOn hx).symm

end K24.Global.HolderProjectionFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global.HolderProjectionFinite
open HolderProjectionZero

lemma sum_iSup_eq_iSup_witness {D : Type*} [Nonempty D]
    (s : Finset ℕ) (a : ℕ → D → ℝ≥0∞) :
    (∑ j ∈ s, ⨆ x, a j x) = ⨆ w : ℕ → D, ∑ j ∈ s, a j (w j) := by
  classical
  have he (j : ℕ) : (⨆ x, a j x) = ⨆ w : ℕ → D, a j (w j) := by
    apply le_antisymm
    · exact iSup_le (fun x => le_iSup_of_le (fun _ => x) le_rfl)
    · exact iSup_le (fun w => le_iSup _ (w j))
  simp_rw [he]
  apply ENNReal.finsetSum_iSup
  intro w z
  refine ⟨fun j => if a j (w j) ≤ a j (z j) then z j else w j, ?_⟩
  intro j
  by_cases hj : a j (w j) ≤ a j (z j)
  · simp only [if_pos hj]
    exact ⟨hj, le_rfl⟩
  · simp only [if_neg hj]
    exact ⟨le_rfl, le_of_not_ge hj⟩

variable {D T : Type*} [MetricSpace D] [Nonempty D] [MeasurableSpace T]
    {W : ℕ → Type*} [∀ j, NormedAddCommGroup (W j)] [∀ j, NormedSpace ℝ (W j)]
    [∀ j, CompleteSpace (W j)]

def jetENorm (k : ℕ) (α : ℝ≥0) (g : ∀ j, D → W j) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (k + 1), ⨆ x, ‖g j x‖ₑ) + eHolderNorm α (g k)

lemma jetENorm_integral_le (μ : Measure T) [IsProbabilityMeasure μ]
    (k : ℕ) (α : ℝ≥0) (f : T → ∀ j, D → W j) (B : ℝ≥0∞)
    (hf : ∀ j ≤ k, ∀ x, Integrable (fun t => f t j x) μ)
    (hb : ∀ t, jetENorm k α (f t) ≤ B) :
    jetENorm k α (fun j x => ∫ t, f t j x ∂μ) ≤ B := by
  rw [jetENorm, sum_iSup_eq_iSup_witness, eHolderNorm_eq_iSup_ratio, ENNReal.iSup_add]
  apply iSup_le
  intro w
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro y
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro z
  rw [edist_eq_enorm_sub, ← integral_sub (hf k le_rfl y) (hf k le_rfl z)]
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), ∫⁻ t, ‖f t j (w j)‖ₑ ∂μ) +
        (∫⁻ t, ‖f t k y - f t k z‖ₑ ∂μ) / edist y z ^ (α : ℝ) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun j hj => enorm_integral_le_lintegral_enorm _
      · gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, (∑ j ∈ Finset.range (k + 1), ‖f t j (w j)‖ₑ) +
        ‖f t k y - f t k z‖ₑ / edist y z ^ (α : ℝ) ∂μ := by
      have hmj (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
          AEMeasurable (fun t => ‖f t j (w j)‖ₑ) μ :=
        (hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (w j)).aestronglyMeasurable.enorm
      have hm : AEMeasurable (fun t => ‖f t k y - f t k z‖ₑ) μ :=
        ((hf k le_rfl y).sub (hf k le_rfl z)).aestronglyMeasurable.enorm
      have hmsum : AEMeasurable
          (fun t => ∑ j ∈ Finset.range (k + 1), ‖f t j (w j)‖ₑ) μ := by
        simpa only [Finset.sum_fn] using Finset.aemeasurable_sum (Finset.range (k + 1)) hmj
      rw [← lintegral_finsetSum' _ hmj, div_eq_mul_inv, ← lintegral_mul_const'' _ hm,
        ← lintegral_add_left' hmsum]
      rfl
    _ ≤ ∫⁻ _ : T, B ∂μ := by
      apply lintegral_mono
      intro t
      apply le_trans _ (hb t)
      rw [jetENorm, eHolderNorm_eq_iSup_ratio]
      apply add_le_add
      · exact Finset.sum_le_sum fun j hj => le_iSup (fun x => ‖f t j x‖ₑ) (w j)
      · rw [← edist_eq_enorm_sub]
        exact le_iSup_of_le y (le_iSup (fun z => edist (f t k y) (f t k z) / edist y z ^ (α : ℝ)) z)
    _ = B := by simp

lemma jetENorm_sub_le (k : ℕ) (α : ℝ≥0) (f g : ∀ j, D → W j) :
    jetENorm k α (fun j x => f j x - g j x) ≤ jetENorm k α f + jetENorm k α g := by
  have hsup (j : ℕ) : (⨆ x, ‖f j x - g j x‖ₑ) ≤ (⨆ x, ‖f j x‖ₑ) + (⨆ x, ‖g j x‖ₑ) := by
    apply iSup_le
    intro x
    exact (show ‖f j x - g j x‖ₑ ≤ ‖f j x‖ₑ + ‖g j x‖ₑ from enorm_sub_le).trans (add_le_add (le_iSup (fun x => ‖f j x‖ₑ) x) (le_iSup (fun x => ‖g j x‖ₑ) x))
  have he : eHolderNorm α (fun x => f k x - g k x) ≤ eHolderNorm α (f k) + eHolderNorm α (g k) := by
    have hneg : eHolderNorm α (-g k) = eHolderNorm α (g k) := by
      simpa using (eHolderNorm_smul (r := α) (f := g k) (-1 : ℝ))
    change eHolderNorm α (f k - g k) ≤ _
    simpa only [sub_eq_add_neg, hneg] using
      (eHolderNorm_add_le (r := α) (f := f k) (g := -g k))
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), ((⨆ x, ‖f j x‖ₑ) + (⨆ x, ‖g j x‖ₑ))) +
        (eHolderNorm α (f k) + eHolderNorm α (g k)) :=
      add_le_add (Finset.sum_le_sum (fun j hj => hsup j)) he
    _ = _ := by rw [Finset.sum_add_distrib]; unfold jetENorm; ac_rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma coordinate_average (μ : Measure T) [IsProbabilityMeasure μ]
    (f : T → FourSpace → V) (k : ℕ) (α B : ℝ≥0)
    {s : Set FourSpace} (hs : IsOpen s) (hne : s.Nonempty)
    (hf : ∀ t, ContDiffOn ℝ k (f t) s)
    (hm : ∀ x ∈ s, AEStronglyMeasurable (fun t => f t x) μ)
    (hb : ∀ t, coordinateHolderENorm k α s (f t) ≤ (B : ℝ≥0∞)) :
    ContDiffOn ℝ k (fun x => ∫ t, f t x ∂μ) s ∧
      coordinateHolderENorm k α s (fun x => ∫ t, f t x ∂μ) ≤ (B : ℝ≥0∞) := by
  letI : Nonempty s := hne.to_subtype
  obtain ⟨hc, hjet⟩ := contDiffOn_integral_and_jets f k α B hs hf hm hb
  refine ⟨hc, ?_⟩
  have hint (j : ℕ) (hj : j ≤ k) (x : s) :
      Integrable (fun t => iteratedFDerivWithin ℝ j (f t) s x) μ := by
    apply (integrable_const (B : ℝ)).mono'
      (aestronglyMeasurable_jet f k hs hf hm j hj x x.property)
    apply ae_of_all
    intro t
    apply ENNReal.ofReal_le_coe.mp
    rw [ofReal_norm]
    exact (jet_enorm_le_coordinate (f t) k j α hj x.property).trans (hb t)
  have hi := jetENorm_integral_le μ k α
    (fun t j (x : s) => iteratedFDerivWithin ℝ j (f t) s x)
    (B : ℝ≥0∞) hint (fun t => hb t)
  have heq : coordinateHolderENorm k α s (fun x => ∫ t, f t x ∂μ) =
      jetENorm k α (fun j (x : s) => ∫ t, iteratedFDerivWithin ℝ j (f t) s x ∂μ) := by
    unfold coordinateHolderENorm derivativeENorm jetENorm
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      apply iSup_congr
      intro x
      rw [hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x x.property]
      rfl
    · congr 1
      funext x
      exact hjet k le_rfl x x.property
  exact heq ▸ hi

lemma coordinateHolderENorm_sub_le (k : ℕ) (α : ℝ≥0)
    {s : Set FourSpace} (hs : IsOpen s) (hne : s.Nonempty)
    (f g : FourSpace → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k α s (f - g) ≤
      coordinateHolderENorm k α s f + coordinateHolderENorm k α s g := by
  letI : Nonempty s := hne.to_subtype
  have hd (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (f - g) s x =
        iteratedFDerivWithin ℝ j f s x - iteratedFDerivWithin ℝ j g s x :=
    iteratedFDerivWithin_sub_apply
      ((hf.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property)
      ((hg.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property) hs.uniqueDiffOn x.property
  have hi := jetENorm_sub_le k α
    (fun j (x : s) => iteratedFDerivWithin ℝ j f s x)
    (fun j (x : s) => iteratedFDerivWithin ℝ j g s x)
  have heq : coordinateHolderENorm k α s (f - g) =
      jetENorm k α (fun j (x : s) => iteratedFDerivWithin ℝ j f s x - iteratedFDerivWithin ℝ j g s x) := by
    unfold coordinateHolderENorm derivativeENorm jetENorm
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      apply iSup_congr
      intro x
      rw [hd j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x]
      rfl
    · congr 1
      funext x
      exact hd k le_rfl x
  exact heq ▸ hi

end K24.Global.HolderProjectionFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.HolderProjectionFinite
open HolderProjectionZero
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

lemma cov2Pi0_holder_bound (C : BoundedLocalCover M) (k : ℕ) (α H : ℝ≥0)
    (rho : CircleAction M) (U : RawCov2 M) (hU : C.Cov2Holder k α U)
    (hi : Cov2HaarIntegrable rho U)
    (hf : ∀ t, C.Cov2Holder k α (actionPullbackCov2 rho t U))
    (hb : ∀ t, C.cov2ENorm k α (actionPullbackCov2 rho t U) ≤
      (H : ℝ≥0∞) * C.cov2ENorm k α U) :
    C.Cov2Holder k α (cov2Pi0 rho U) ∧
      C.cov2ENorm k α (cov2Pi0 rho U) ≤ (H : ℝ≥0∞) * C.cov2ENorm k α U := by
  let B : ℝ≥0 := H * (C.cov2ENorm k α U).toNNReal
  have hB : (B : ℝ≥0∞) = (H : ℝ≥0∞) * C.cov2ENorm k α U := by
    simp only [B, ENNReal.coe_mul, ENNReal.coe_toNNReal (ne_of_lt hU.2)]
  have hlocal (ν : C.Index) :
      ContDiffOn ℝ k ((C.chart ν).liftedCov2 (cov2Pi0 rho U)) (C.chart ν).innerDomain ∧
      coordinateHolderENorm k α (C.chart ν).innerDomain
        ((C.chart ν).liftedCov2 (cov2Pi0 rho U)) ≤ (B : ℝ≥0∞) := by
    have hh := coordinate_average circleHaar
      (fun t => (C.chart ν).liftedCov2 (actionPullbackCov2 rho t U)) k α B
      (C.chart ν).innerOpen (C.chart ν).innerNonempty
      (fun t => (hf t).1 ν)
      (fun x hx => (liftedCov2_orbit_integrable (C.chart ν) rho U hi x).aestronglyMeasurable)
      (fun t => (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
        ((C.chart ν).liftedCov2 (actionPullbackCov2 rho t U))) ν).trans
          ((hb t).trans_eq hB.symm))
    simpa only [← liftedCov2_Pi0 (C.chart ν) rho U hi] using hh
  have hnorm : C.cov2ENorm k α (cov2Pi0 rho U) ≤ (H : ℝ≥0∞) * C.cov2ENorm k α U :=
    (iSup_le (fun ν => (hlocal ν).2)).trans_eq hB
  exact ⟨⟨fun ν => (hlocal ν).1, hnorm.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)⟩, hnorm⟩

lemma cov2ENorm_sub_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawCov2 M) (hU : C.Cov2Holder k α U) (hV : C.Cov2Holder k α V) :
    C.cov2ENorm k α (U - V) ≤ C.cov2ENorm k α U + C.cov2ENorm k α V := by
  apply iSup_le
  intro ν
  have hsub : (C.chart ν).liftedCov2 (U - V) =
      (C.chart ν).liftedCov2 U - (C.chart ν).liftedCov2 V := by
    funext x
    exact liftedCov2_sub (C.chart ν) U V x
  rw [hsub]
  apply (coordinateHolderENorm_sub_le k α (C.chart ν).innerOpen (C.chart ν).innerNonempty
    _ _ (hU.1 ν) (hV.1 ν)).trans
  exact add_le_add (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedCov2 U)) ν) (le_iSup (fun ν => coordinateHolderENorm k α
      (C.chart ν).innerDomain ((C.chart ν).liftedCov2 V)) ν)

lemma cov2Holder_sub (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawCov2 M) (hU : C.Cov2Holder k α U) (hV : C.Cov2Holder k α V) :
    C.Cov2Holder k α (U - V) := by
  constructor
  · intro ν
    have hsub : (C.chart ν).liftedCov2 (U - V) =
        (C.chart ν).liftedCov2 U - (C.chart ν).liftedCov2 V := by
      funext x
      exact liftedCov2_sub (C.chart ν) U V x
    rw [hsub]
    exact (hU.1 ν).sub (hV.1 ν)
  · exact (cov2ENorm_sub_le C k α U V hU hV).trans_lt (ENNReal.add_lt_top.mpr ⟨hU.2,hV.2⟩)

lemma covectorPi0_holder_bound (C : BoundedLocalCover M) (k : ℕ) (α H : ℝ≥0)
    (rho : CircleAction M) (U : RawCovector M) (hU : C.CovectorHolder k α U)
    (hi : CovectorHaarIntegrable rho U)
    (hf : ∀ t, C.CovectorHolder k α (actionPullbackCovector rho t U))
    (hb : ∀ t, C.covectorENorm k α (actionPullbackCovector rho t U) ≤
      (H : ℝ≥0∞) * C.covectorENorm k α U) :
    C.CovectorHolder k α (covectorPi0 rho U) ∧
      C.covectorENorm k α (covectorPi0 rho U) ≤ (H : ℝ≥0∞) * C.covectorENorm k α U := by
  let B : ℝ≥0 := H * (C.covectorENorm k α U).toNNReal
  have hB : (B : ℝ≥0∞) = (H : ℝ≥0∞) * C.covectorENorm k α U := by
    simp only [B, ENNReal.coe_mul, ENNReal.coe_toNNReal (ne_of_lt hU.2)]
  have hlocal (ν : C.Index) :
      ContDiffOn ℝ k ((C.chart ν).liftedCovector (covectorPi0 rho U)) (C.chart ν).innerDomain ∧
      coordinateHolderENorm k α (C.chart ν).innerDomain
        ((C.chart ν).liftedCovector (covectorPi0 rho U)) ≤ (B : ℝ≥0∞) := by
    have hh := coordinate_average circleHaar
      (fun t => (C.chart ν).liftedCovector (actionPullbackCovector rho t U)) k α B
      (C.chart ν).innerOpen (C.chart ν).innerNonempty
      (fun t => (hf t).1 ν)
      (fun x hx => (liftedCovector_orbit_integrable (C.chart ν) rho U hi x).aestronglyMeasurable)
      (fun t => (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
        ((C.chart ν).liftedCovector (actionPullbackCovector rho t U))) ν).trans
          ((hb t).trans_eq hB.symm))
    simpa only [← liftedCovector_Pi0 (C.chart ν) rho U hi] using hh
  have hnorm : C.covectorENorm k α (covectorPi0 rho U) ≤ (H : ℝ≥0∞) * C.covectorENorm k α U :=
    (iSup_le (fun ν => (hlocal ν).2)).trans_eq hB
  exact ⟨⟨fun ν => (hlocal ν).1, hnorm.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)⟩, hnorm⟩

lemma covectorENorm_sub_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawCovector M) (hU : C.CovectorHolder k α U) (hV : C.CovectorHolder k α V) :
    C.covectorENorm k α (U - V) ≤ C.covectorENorm k α U + C.covectorENorm k α V := by
  apply iSup_le
  intro ν
  have hsub : (C.chart ν).liftedCovector (U - V) =
      (C.chart ν).liftedCovector U - (C.chart ν).liftedCovector V := by
    funext x
    exact liftedCovector_sub (C.chart ν) U V x
  rw [hsub]
  apply (coordinateHolderENorm_sub_le k α (C.chart ν).innerOpen (C.chart ν).innerNonempty
    _ _ (hU.1 ν) (hV.1 ν)).trans
  exact add_le_add (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedCovector U)) ν) (le_iSup (fun ν => coordinateHolderENorm k α
      (C.chart ν).innerDomain ((C.chart ν).liftedCovector V)) ν)

lemma covectorHolder_sub (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawCovector M) (hU : C.CovectorHolder k α U) (hV : C.CovectorHolder k α V) :
    C.CovectorHolder k α (U - V) := by
  constructor
  · intro ν
    have hsub : (C.chart ν).liftedCovector (U - V) =
        (C.chart ν).liftedCovector U - (C.chart ν).liftedCovector V := by
      funext x
      exact liftedCovector_sub (C.chart ν) U V x
    rw [hsub]
    exact (hU.1 ν).sub (hV.1 ν)
  · exact (covectorENorm_sub_le C k α U V hU hV).trans_lt (ENNReal.add_lt_top.mpr ⟨hU.2,hV.2⟩)

lemma vectorPi0_holder_bound (C : BoundedLocalCover M) (k : ℕ) (α H : ℝ≥0)
    (rho : CircleAction M) (U : RawVector M) (hU : C.VectorHolder k α U)
    (hi : VectorHaarIntegrable rho U)
    (hf : ∀ t, C.VectorHolder k α (actionPullbackVector rho t U))
    (hb : ∀ t, C.vectorENorm k α (actionPullbackVector rho t U) ≤
      (H : ℝ≥0∞) * C.vectorENorm k α U) :
    C.VectorHolder k α (vectorPi0 rho U) ∧
      C.vectorENorm k α (vectorPi0 rho U) ≤ (H : ℝ≥0∞) * C.vectorENorm k α U := by
  let B : ℝ≥0 := H * (C.vectorENorm k α U).toNNReal
  have hB : (B : ℝ≥0∞) = (H : ℝ≥0∞) * C.vectorENorm k α U := by
    simp only [B, ENNReal.coe_mul, ENNReal.coe_toNNReal (ne_of_lt hU.2)]
  have hlocal (ν : C.Index) :
      ContDiffOn ℝ k ((C.chart ν).liftedVector (vectorPi0 rho U)) (C.chart ν).innerDomain ∧
      coordinateHolderENorm k α (C.chart ν).innerDomain
        ((C.chart ν).liftedVector (vectorPi0 rho U)) ≤ (B : ℝ≥0∞) := by
    have hh := coordinate_average circleHaar
      (fun t => (C.chart ν).liftedVector (actionPullbackVector rho t U)) k α B
      (C.chart ν).innerOpen (C.chart ν).innerNonempty
      (fun t => (hf t).1 ν)
      (fun x hx => (liftedVector_orbit_integrable (C.chart ν) rho U hi x).aestronglyMeasurable)
      (fun t => (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
        ((C.chart ν).liftedVector (actionPullbackVector rho t U))) ν).trans
          ((hb t).trans_eq hB.symm))
    simpa only [← liftedVector_Pi0 (C.chart ν) rho U hi] using hh
  have hnorm : C.vectorENorm k α (vectorPi0 rho U) ≤ (H : ℝ≥0∞) * C.vectorENorm k α U :=
    (iSup_le (fun ν => (hlocal ν).2)).trans_eq hB
  exact ⟨⟨fun ν => (hlocal ν).1, hnorm.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hU.2)⟩, hnorm⟩

lemma vectorENorm_sub_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawVector M) (hU : C.VectorHolder k α U) (hV : C.VectorHolder k α V) :
    C.vectorENorm k α (U - V) ≤ C.vectorENorm k α U + C.vectorENorm k α V := by
  apply iSup_le
  intro ν
  have hsub : (C.chart ν).liftedVector (U - V) =
      (C.chart ν).liftedVector U - (C.chart ν).liftedVector V := by
    funext x
    exact liftedVector_sub (C.chart ν) U V x
  rw [hsub]
  apply (coordinateHolderENorm_sub_le k α (C.chart ν).innerOpen (C.chart ν).innerNonempty
    _ _ (hU.1 ν) (hV.1 ν)).trans
  exact add_le_add (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedVector U)) ν) (le_iSup (fun ν => coordinateHolderENorm k α
      (C.chart ν).innerDomain ((C.chart ν).liftedVector V)) ν)

lemma vectorHolder_sub (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawVector M) (hU : C.VectorHolder k α U) (hV : C.VectorHolder k α V) :
    C.VectorHolder k α (U - V) := by
  constructor
  · intro ν
    have hsub : (C.chart ν).liftedVector (U - V) =
        (C.chart ν).liftedVector U - (C.chart ν).liftedVector V := by
      funext x
      exact liftedVector_sub (C.chart ν) U V x
    rw [hsub]
    exact (hU.1 ν).sub (hV.1 ν)
  · exact (vectorENorm_sub_le C k α U V hU hV).trans_lt (ENNReal.add_lt_top.mpr ⟨hU.2,hV.2⟩)

theorem holder_projection_finite (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (order : ℕ) (rho : CircleAction M) (hact : HolderActionControl C α H order rho) :
    HolderProjectionConclusions C α H order rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk U hU
    have hc := NativeContinuity.cov2_evaluation_continuous U
      (CoverContinuity.cov2Holder_native_contDiff_zero C k α U hU)
    obtain ⟨hi, hinv, hii, hidem, hip, hnz⟩ := HaarSectors.continuous_cov2_projection rho U hc
    obtain ⟨havg, hb⟩ := cov2Pi0_holder_bound C k α H rho U hU hi
      (fun t => (hact.tensor k hk t U hU).1) (fun t => (hact.tensor k hk t U hU).2)
    have hp : C.cov2ENorm k α (cov2PiPerp rho U) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm k α U :=
      (cov2ENorm_sub_le C k α U (cov2Pi0 rho U) hU havg).trans
        (complement_enorm_bound _ _ H hb)
    exact ⟨hi, havg, cov2Holder_sub C k α U (cov2Pi0 rho U) hU havg,
      hinv, hidem, hnz, hb, hp⟩
  · intro k hk U hU
    have hc := NativeContinuity.covector_evaluation_continuous U
      (CoverContinuity.covectorHolder_native_contDiff_zero C k α U hU)
    obtain ⟨hi, hinv, hii, hidem, hip, hnz⟩ := HaarSectors.continuous_covector_projection rho U hc
    obtain ⟨havg, hb⟩ := covectorPi0_holder_bound C k α H rho U hU hi
      (fun t => (hact.covector k hk t U hU).1) (fun t => (hact.covector k hk t U hU).2)
    have hp : C.covectorENorm k α (covectorPiPerp rho U) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * C.covectorENorm k α U :=
      (covectorENorm_sub_le C k α U (covectorPi0 rho U) hU havg).trans
        (complement_enorm_bound _ _ H hb)
    exact ⟨hi, havg, covectorHolder_sub C k α U (covectorPi0 rho U) hU havg,
      hinv, hidem, hnz, hb, hp⟩
  · intro k hk U hU
    have hc := NativeContinuity.vector_section_continuous U
      (CoverContinuity.vectorHolder_native_contDiff_zero C k α U hU)
    obtain ⟨hi, hinv, hii, hidem, hip, hnz⟩ := HaarSectors.continuous_vector_projection rho U hc
    obtain ⟨havg, hb⟩ := vectorPi0_holder_bound C k α H rho U hU hi
      (fun t => (hact.vector k hk t U hU).1) (fun t => (hact.vector k hk t U hU).2)
    have hp : C.vectorENorm k α (vectorPiPerp rho U) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * C.vectorENorm k α U :=
      (vectorENorm_sub_le C k α U (vectorPi0 rho U) hU havg).trans
        (complement_enorm_bound _ _ H hb)
    exact ⟨hi, havg, vectorHolder_sub C k α U (vectorPi0 rho U) hU havg,
      hinv, hidem, hnz, hb, hp⟩

end K24.Global.HolderProjectionFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff NNReal
universe u

theorem solution {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (order : ℕ) (rho : CircleAction M) :
    HolderActionControl C α H order rho → HolderProjectionConclusions C α H order rho := by
  intro hact
  exact HolderProjectionFinite.holder_projection_finite C α H hα order rho hact

theorem K24HPKExactType {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (order : ℕ) (rho : CircleAction M) :
    HolderActionControl C α H order rho → HolderProjectionConclusions C α H order rho :=
  solution C α H hα order rho

set_option pp.universes true in
#check @solution
#print axioms solution
#print axioms K24HPKExactType
