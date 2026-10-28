-- Prove2me | solution 1 for K24.Global.actual_inverse_metric_uniform_remainder
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:44:11.294723+00:00
-- url     : https://prove2.me/submissions/be67a529-66e8-4788-b8d5-579d710ed134

import Definitions.Def_K24GlobalStatement





/- K24PERPAll: actual all-order zero-average Holder section Banach spaces.
Reused inspected proof bodies, not assumed theorem stubs:
* Pointwise Haar integral identities and cover-to-bundle continuity from HP0
  source161bcd0d3ad79c38a467a899ad203fe5325efdb3, standalone SHA256
  24b7d61cbab4bcad271b5104d98197da7e93859ac4aea232586eb78048d34c90.
  The order-zero Holder projection estimates are not needed or included.
* All-order actual tensor completeness HB2 source2a069df20d73d303e930fd16b9f57bf67fbc166d.
* Actual vector/covector completeness VCB source37875d0eb68b58b5e8eed96e70faf78ea7b7f9c0.
* Restricted Haar linearity PERP source6d71e461e74d9ee72ab49b23b4e1e48cdad42637.
* Exact normed-submodule adapter INV source35b6b77d6dd76b87bbf54fb49b73bc6b9fed156b.
New proof: actual bounded evaluations, compact scalar orbit continuity,
Banach-Steinhaus, and closedness of the original kernels. No action norm
control or Holder exponent positivity is assumed; no higher-order Holder
projection preservation or bound is concluded. -/



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



/- K24HB2: finite-order big Hölder Banach theorem for actual tensor sections.
The two matrix reconstruction helpers immediately below are reused verbatim
from the inspected K24HB source commit
0de8f6e6525f6012f32adda89cb7178d66708b4d, Solutions/K24HB_Tensor.lean.
The derivative-limit, canonical norm, and finite-order completeness arguments
are the K24HB2 continuation. No hidden inclusionsPerpFoundation_solution-module imports are required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem matrixToBilinear_eval_continuous (v w : FourSpace) :
    Continuous (fun a : Mat4 => matrixToBilinear a v w) := by
  unfold matrixToBilinear
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  fun_prop

theorem LocalCoverChart.matrix_recover_eval {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u : RawCov2 M) (x : FourSpace)
    (v w : TangentSpace I4 (c.lift x)) :
    matrixToBilinear (c.liftedCov2 u x) ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) =
      u (c.lift x) v w := by
  have h := matrixToBilinear_recover
    (bilinearPullback (u (c.lift x)) (c.tangentMap x).toContinuousLinearMap)
  have h' := congrArg (fun a : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) =>
    a ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)) h
  change matrixToBilinear (c.liftedCov2 u x) ((c.tangentMap x).symm v)
    ((c.tangentMap x).symm w) = u (c.lift x)
      ((c.tangentMap x) ((c.tangentMap x).symm v))
      ((c.tangentMap x) ((c.tangentMap x).symm w)) at h'
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h'


end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Completeness produces an actual function limit on the same domain. -/
theorem exists_uniform_limit_of_uniformCauchy {s : Set E} (f : ℕ → E → V)
    (hc : UniformCauchySeqOn f atTop s) :
    ∃ g : E → V, TendstoUniformlyOn f g atTop s := by
  classical
  have hp (x : s) : CauchySeq (fun n => f n x) := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hc eps heps
    exact ⟨N, fun i hi j hj => hN i hi j hj x x.property⟩
  choose g₀ hg₀ using fun x : s => cauchySeq_tendsto_of_complete (hp x)
  let g : E → V := fun x => if hx : x ∈ s then g₀ ⟨x, hx⟩ else 0
  refine ⟨g, hc.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  simpa only [g, dif_pos hx] using hg₀ ⟨x, hx⟩

/-- Uniform Cauchy control of the actual finite jets forces compatibility of
their limits with derivatives of the actual pointwise function limit. -/
theorem contDiffOn_of_uniformCauchy_iteratedFDerivWithin
    (k : ℕ) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V) (g : E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ j : ℕ, j ≤ k →
      UniformCauchySeqOn (fun n => iteratedFDerivWithin ℝ j (f n) s) atTop s)
    (hlim : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ k g s ∧
      ∀ j : ℕ, j ≤ k → TendstoUniformlyOn
        (fun n => iteratedFDerivWithin ℝ j (f n) s)
        (iteratedFDerivWithin ℝ j g s) atTop s := by
  induction k generalizing f g with
  | zero =>
    have hcF : UniformCauchySeqOn f atTop s := by
      have hh := Metric.uniformCauchySeqOn_iff.mp (hc 0 le_rfl)
      apply Metric.uniformCauchySeqOn_iff.mpr
      simpa only [dist_iteratedFDerivWithin_zero] using hh
    have huF := hcF.tendstoUniformlyOn_of_tendsto hlim
    refine ⟨contDiffOn_zero.mpr (huF.continuousOn
      (Eventually.of_forall fun n => (hf n).continuousOn).frequently), ?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    apply (hc 0 le_rfl).tendstoUniformlyOn_of_tendsto
    intro x hx
    exact (continuousMultilinearCurryFin0 ℝ E V).symm.continuous.continuousAt.tendsto.comp (hlim x hx)
  | succ k ih =>
    have hfLow : ∀ n, ContDiffOn ℝ k (f n) s := fun n =>
      (hf n).of_le (by exact_mod_cast Nat.le_succ k)
    obtain ⟨hgLow, huLow⟩ := ih f g hfLow (fun j hj => hc j (hj.trans (Nat.le_succ k))) hlim
    obtain ⟨q, huq⟩ := exists_uniform_limit_of_uniformCauchy
      (fun n => iteratedFDerivWithin ℝ (k + 1) (f n) s) (hc (k + 1) le_rfl)
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) V
    have huD := curry.isometry.uniformContinuous.comp_tendstoUniformlyOn huq
    have hd : ∀ x ∈ s,
        HasFDerivAt (iteratedFDerivWithin ℝ k g s) (curry (q x)) x := by
      intro x hx
      apply hasFDerivAt_of_tendstoUniformlyOn (f := fun n => iteratedFDerivWithin ℝ k (f n) s) hs huD _ _ hx
      · intro n y hy
        exact ((hf n).ftaylorSeriesWithin hs.uniqueDiffOn |>.fderivWithin k
          (by exact_mod_cast Nat.lt_succ_self k) y hy).hasFDerivAt (hs.mem_nhds hy)
      · intro y hy
        exact (huLow k le_rfl).tendsto_at hy
    have hqEq : ∀ x ∈ s, q x = iteratedFDerivWithin ℝ (k + 1) g s x := by
      intro x hx
      have hh := (hd x hx).hasFDerivWithinAt.fderivWithin (hs.uniqueDiffOn x hx)
      rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, hh]
      exact (curry.symm_apply_apply (q x)).symm
    have huTop : TendstoUniformlyOn
        (fun n => iteratedFDerivWithin ℝ (k + 1) (f n) s)
        (iteratedFDerivWithin ℝ (k + 1) g s) atTop s :=
      huq.congr_right hqEq
    have hContTop : ContinuousOn (iteratedFDerivWithin ℝ (k + 1) g s) s := by
      apply huTop.continuousOn
      exact (Eventually.of_forall fun n =>
        (hf n).continuousOn_iteratedFDerivWithin (by simp) hs.uniqueDiffOn).frequently
    refine ⟨?_, ?_⟩
    · apply (contDiffOn_nat_iff_continuousOn_differentiableOn hs.uniqueDiffOn).mpr
      constructor
      · intro j hj
        by_cases hjLow : j ≤ k
        · exact hgLow.continuousOn_iteratedFDerivWithin (by exact_mod_cast hjLow) hs.uniqueDiffOn
        · have hjeq : j = k + 1 := by omega
          subst j
          exact hContTop
      · intro j hj
        by_cases hjLow : j < k
        · exact hgLow.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hjLow) hs.uniqueDiffOn
        · have hjeq : j = k := by omega
          subst j
          exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · intro j hj
      by_cases hjLow : j ≤ k
      · exact huLow j hjLow
      · have hjeq : j = k + 1 := by omega
        subst j
        exact huTop

end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivativeENorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (alpha : ℝ≥0) (s : Set E) (f : E → V) :
    derivativeENorm j s f ≤ coordinateHolderENorm k alpha s f := by
  have hsum : derivativeENorm j s f ≤ ∑ l ∈ Finset.range (k+1), derivativeENorm l s f :=
    Finset.single_le_sum (f := fun l => derivativeENorm l s f) (fun _ _ => bot_le)
      (show j ∈ Finset.range (k+1) from Finset.mem_range.mpr (by omega))
  exact hsum.trans le_self_add

theorem jet_enorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (alpha : ℝ≥0) (s : Set E) (f : E → V) (x : E) (hx : x ∈ s) :
    ‖iteratedFDerivWithin ℝ j f s x‖ₑ ≤ coordinateHolderENorm k alpha s f := by
  exact (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)) ⟨x,hx⟩).trans
    (derivativeENorm_le_coordinateHolderENorm k j hj alpha s f)

theorem enorm_le_coordinateHolderENorm (k : ℕ) (alpha : ℝ≥0)
    (s : Set E) (f : E → V) (x : E) (hx : x ∈ s) :
    ‖f x‖ₑ ≤ coordinateHolderENorm k alpha s f := by
  have heq : ‖iteratedFDerivWithin ℝ 0 f s x‖ₑ = ‖f x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDerivWithin_zero]
  rw [← heq]
  exact jet_enorm_le_coordinateHolderENorm k 0 (Nat.zero_le k) alpha s f x hx

theorem coordinateHolderENorm_add_le (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f g : E → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k alpha s (f + g) ≤
      coordinateHolderENorm k alpha s f + coordinateHolderENorm k alpha s g := by
  have hjet (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (f + g) s x =
        iteratedFDerivWithin ℝ j f s x + iteratedFDerivWithin ℝ j g s x :=
    iteratedFDerivWithin_add_apply
      ((hf.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property)
      ((hg.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property) hs.uniqueDiffOn x.property
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (f + g) ≤
      derivativeENorm j s f + derivativeENorm j s g := by
    apply iSup_le
    intro x
    change ‖iteratedFDerivWithin ℝ j (f + g) s x‖ₑ ≤ _
    rw [hjet j hj x]
    exact (enorm_add_le (iteratedFDerivWithin ℝ j f s x) (iteratedFDerivWithin ℝ j g s x)).trans (add_le_add
      (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)) x)
      (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j g s x‖₊ : ℝ≥0∞)) x))
  have heq : (fun x : s => iteratedFDerivWithin ℝ k (f + g) s x) =
      (fun x : s => iteratedFDerivWithin ℝ k f s x) +
      (fun x : s => iteratedFDerivWithin ℝ k g s x) := funext (hjet k le_rfl)
  unfold coordinateHolderENorm
  rw [heq]
  calc
    _ ≤ (∑ j ∈ Finset.range (k+1), (derivativeENorm j s f + derivativeENorm j s g)) +
        (eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k f s x) +
        eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k g s x)) := by
      exact add_le_add (Finset.sum_le_sum fun j hj => hd j (by simpa using hj)) eHolderNorm_add_le
    _ = _ := by rw [Finset.sum_add_distrib]; ac_rfl

theorem coordinateHolderENorm_smul (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (c : ℝ) (f : E → V) (hf : ContDiffOn ℝ k f s) :
    coordinateHolderENorm k alpha s (c • f) =
      ENNReal.ofReal |c| * coordinateHolderENorm k alpha s f := by
  have hjet (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (c • f) s x = c • iteratedFDerivWithin ℝ j f s x :=
    iteratedFDerivWithin_const_smul_apply
      ((hf.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property) hs.uniqueDiffOn x.property
  have hcn : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal |c| := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (c • f) =
      ENNReal.ofReal |c| * derivativeENorm j s f := by
    unfold derivativeENorm
    simp only [hjet j hj, nnnorm_smul, ENNReal.coe_mul, hcn, ENNReal.mul_iSup]
  have heq : (fun x : s => iteratedFDerivWithin ℝ k (c • f) s x) =
      c • (fun x : s => iteratedFDerivWithin ℝ k f s x) := funext (hjet k le_rfl)
  unfold coordinateHolderENorm
  rw [heq]
  have hh := eHolderNorm_smul (r := alpha) (f := fun x : s => iteratedFDerivWithin ℝ k f s x) c
  rw [hh, hcn, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hd j (by simpa using hj)

theorem coordinateHolderENorm_neg (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) (hf : ContDiffOn ℝ k f s) :
    coordinateHolderENorm k alpha s (-f) = coordinateHolderENorm k alpha s f := by
  simpa using coordinateHolderENorm_smul k alpha hs (-1) f hf

theorem coordinateHolderENorm_sub_le (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f g : E → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k alpha s (f - g) ≤
      coordinateHolderENorm k alpha s f + coordinateHolderENorm k alpha s g := by
  simpa only [sub_eq_add_neg, coordinateHolderENorm_neg k alpha hs g hg] using
    coordinateHolderENorm_add_le k alpha hs f (-g) hf hg.neg

theorem coordinateHolderENorm_zero (k : ℕ) (alpha : ℝ≥0) (s : Set E) :
    coordinateHolderENorm k alpha s (0 : E → V) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm]
  exact eHolderNorm_const s alpha (0 : E [×k]→L[ℝ] V)

theorem uniformCauchy_jets_of_coordinateHolderENorm_cauchy
    (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha s (f i - f j) < ENNReal.ofReal eps) :
    ∀ j : ℕ, j ≤ k → UniformCauchySeqOn
      (fun n => iteratedFDerivWithin ℝ j (f n) s) atTop s := by
  intro j hj
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  rw [dist_eq_norm, ofReal_norm]
  have heq := iteratedFDerivWithin_sub_apply
    (((hf m).of_le (by exact_mod_cast hj)).contDiffWithinAt hx)
    (((hf n).of_le (by exact_mod_cast hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx
  rw [← heq]
  exact (jet_enorm_le_coordinateHolderENorm k j hj alpha s (f m-f n) x hx).trans_lt
    (hN m hm n hn)

theorem coordinateHolderENorm_limit_le {k : ℕ} {alpha C : ℝ≥0} {s : Set E}
    {f : ℕ → E → V} {g : E → V}
    (hlim : ∀ j : ℕ, j ≤ k → ∀ x ∈ s, Tendsto
      (fun n => iteratedFDerivWithin ℝ j (f n) s x) atTop
      (𝓝 (iteratedFDerivWithin ℝ j g s x)))
    (hbound : ∀ᶠ n in atTop, coordinateHolderENorm k alpha s (f n) ≤ (C : ℝ≥0∞)) :
    coordinateHolderENorm k alpha s g ≤ (k+2 : ℕ) * (C : ℝ≥0∞) := by
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s g ≤ (C : ℝ≥0∞) := by
    apply iSup_le
    intro x
    apply le_of_tendsto (hlim j hj x x.property).enorm
    exact hbound.mono fun n hn =>
      (jet_enorm_le_coordinateHolderENorm k j hj alpha s (f n) x x.property).trans hn
  have hh : HolderWith C alpha (fun x : s => iteratedFDerivWithin ℝ k g s x) := by
    intro x y
    apply le_of_tendsto ((hlim k le_rfl x x.property).edist (hlim k le_rfl y y.property))
    filter_upwards [hbound] with n hn
    have hle : eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k (f n) s x) ≤
        (C : ℝ≥0∞) := le_add_self.trans hn
    have hm := eHolderNorm_lt_top.mp (hle.trans_lt ENNReal.coe_lt_top)
    have hHolder := hm.holderWith
    have hC : nnHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k (f n) s x) ≤ C := by
      apply ENNReal.coe_le_coe.mp
      rwa [hm.coe_nnHolderNorm_eq_eHolderNorm]
    exact hHolder.mono hC x y
  unfold coordinateHolderENorm
  calc
    _ ≤ (∑ j ∈ Finset.range (k+1), (C : ℝ≥0∞)) + C :=
      add_le_add (Finset.sum_le_sum fun j hj => hd j (by simpa using hj)) hh.eHolderNorm_le
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul]; ring

end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateHolderENorm_sub_limit_le {k : ℕ} {alpha K : ℝ≥0}
    {s : Set E} (hs : IsOpen s) (f : ℕ → E → V) (g : E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s) (hg : ContDiffOn ℝ k g s)
    (hlim : ∀ j : ℕ, j ≤ k → ∀ x ∈ s, Tendsto
      (fun n => iteratedFDerivWithin ℝ j (f n) s x) atTop
      (𝓝 (iteratedFDerivWithin ℝ j g s x)))
    (i : ℕ) (hbound : ∀ᶠ n in atTop,
      coordinateHolderENorm k alpha s (f i-f n) ≤ (K : ℝ≥0∞)) :
    coordinateHolderENorm k alpha s (f i-g) ≤ (k+2 : ℕ) * (K : ℝ≥0∞) := by
  apply coordinateHolderENorm_limit_le (f := fun n => f i-f n) _ hbound
  intro j hj x hx
  have hjet (n : ℕ) := iteratedFDerivWithin_sub_apply
    (((hf i).of_le (by exact_mod_cast hj)).contDiffWithinAt hx)
    (((hf n).of_le (by exact_mod_cast hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx
  have hjetg := iteratedFDerivWithin_sub_apply
    (((hf i).of_le (by exact_mod_cast hj)).contDiffWithinAt hx)
    ((hg.of_le (by exact_mod_cast hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx
  simp_rw [hjet, hjetg]
  exact tendsto_const_nhds.sub (hlim j hj x hx)

theorem coordinateHolderENorm_cauchy_pointwise_limit [CompleteSpace V]
    (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V) (g : E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha s (f i - f j) < ENNReal.ofReal eps)
    (hlim : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ k g s ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      coordinateHolderENorm k alpha s (f i-g) < ENNReal.ofReal eps := by
  obtain ⟨hg, hu⟩ := contDiffOn_of_uniformCauchy_iteratedFDerivWithin k hs f g hf
    (uniformCauchy_jets_of_coordinateHolderENorm_cauchy k alpha hs f hf hc) hlim
  refine ⟨hg, fun eps heps => ?_⟩
  have hdpos : 0 < (k+2 : ℝ) := by positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * (k+2 : ℝ))) (by positivity)
  let K : ℝ≥0 := (ENNReal.ofReal (eps / (2 * (k+2 : ℝ)))).toNNReal
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * (k+2 : ℝ))) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  refine ⟨N, fun i hi => ?_⟩
  have hb : ∀ᶠ n in atTop, coordinateHolderENorm k alpha s (f i-f n) ≤ (K : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hK]
    exact (hN i hi n hn).le
  refine (coordinateHolderENorm_sub_limit_le hs f g hf hg
    (fun j hj x hx => (hu j hj).tendsto_at hx) i hb).trans_lt ?_
  rw [hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
  push_cast
  have heq : (k+2 : ℝ) * (eps / (2 * (k+2 : ℝ))) = eps/2 := by
    field_simp
  rw [heq]
  linarith

/-- Completeness of the actual big Hölder coefficient functions on any open
domain at every finite order, with the canonical derivative-based norm. -/
theorem coordinateHolderENorm_complete [CompleteSpace V]
    (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V)
    (hf : ∀ n, BigHolderOn k alpha s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha s (f i - f j) < ENNReal.ofReal eps) :
    ∃ g : E → V, BigHolderOn k alpha s g ∧
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        coordinateHolderENorm k alpha s (f i-g) < ENNReal.ofReal eps := by
  have hcu : UniformCauchySeqOn f atTop s := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
    rw [dist_eq_norm, ofReal_norm]
    exact (enorm_le_coordinateHolderENorm k alpha s (f m-f n) x hx).trans_lt (hN m hm n hn)
  obtain ⟨g, hu⟩ := exists_uniform_limit_of_uniformCauchy f hcu
  obtain ⟨hg, hconv⟩ := coordinateHolderENorm_cauchy_pointwise_limit k alpha hs f g
    (fun n => (hf n).1) hc (fun x hx => hu.tendsto_at hx)
  refine ⟨g, ⟨hg, ?_⟩, hconv⟩
  obtain ⟨N, hN⟩ := hconv 1 (by norm_num)
  have hEq : g = f N-(f N-g) := by ext x; simp
  have hbound := coordinateHolderENorm_sub_le k alpha hs (f N) (f N-g)
    (hf N).1 ((hf N).1.sub hg)
  rw [← hEq] at hbound
  exact hbound.trans_lt (ENNReal.add_lt_top.mpr
    ⟨(hf N).2, (hN N le_rfl).trans ENNReal.ofReal_lt_top⟩)

end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8

noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def Cov2Regular (C : BoundedLocalCover M) (k : ℕ) (u : RawCov2 M) : Prop :=
  ∀ nu : C.Index, ContDiffOn ℝ k ((C.chart nu).liftedCov2 u) (C.chart nu).innerDomain

theorem Cov2Regular.add {C : BoundedLocalCover M} {k : ℕ} {u v : RawCov2 M}
    (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) : Cov2Regular C k (u+v) :=
  fun nu => (hu nu).add (hv nu)

theorem Cov2Regular.smul {C : BoundedLocalCover M} {k : ℕ} {u : RawCov2 M}
    (hu : Cov2Regular C k u) (c : ℝ) : Cov2Regular C k (c • u) :=
  fun nu => (hu nu).const_smul c

theorem Cov2Regular.sub {C : BoundedLocalCover M} {k : ℕ} {u v : RawCov2 M}
    (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) : Cov2Regular C k (u-v) :=
  fun nu => (hu nu).sub (hv nu)

theorem cov2ENorm_add_le (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u v : RawCov2 M) (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) :
    C.cov2ENorm k alpha (u+v) ≤ C.cov2ENorm k alpha u + C.cov2ENorm k alpha v := by
  apply iSup_le
  intro nu
  exact (coordinateHolderENorm_add_le k alpha (C.chart nu).innerOpen
    _ _ (hu nu) (hv nu)).trans (add_le_add
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 u)) nu)
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 v)) nu))

theorem cov2ENorm_smul (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (c : ℝ) (u : RawCov2 M) (hu : Cov2Regular C k u) :
    C.cov2ENorm k alpha (c • u) = ENNReal.ofReal |c| * C.cov2ENorm k alpha u := by
  unfold BoundedLocalCover.cov2ENorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro nu
  exact coordinateHolderENorm_smul k alpha (C.chart nu).innerOpen c _ (hu nu)

theorem cov2ENorm_sub_le (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u v : RawCov2 M) (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) :
    C.cov2ENorm k alpha (u-v) ≤ C.cov2ENorm k alpha u + C.cov2ENorm k alpha v := by
  apply iSup_le
  intro nu
  exact (coordinateHolderENorm_sub_le k alpha (C.chart nu).innerOpen
    _ _ (hu nu) (hv nu)).trans (add_le_add
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 u)) nu)
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 v)) nu))

theorem cov2ENorm_zero (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    C.cov2ENorm k alpha 0 = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro nu
  exact (coordinateHolderENorm_zero k alpha (C.chart nu).innerDomain).le

theorem liftedCov2_enorm_le_cov2ENorm_order (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (nu : C.Index) (x : FourSpace) (hx : x ∈ (C.chart nu).innerDomain) :
    ‖(C.chart nu).liftedCov2 u x‖ₑ ≤ C.cov2ENorm k alpha u :=
  (enorm_le_coordinateHolderENorm k alpha (C.chart nu).innerDomain
    ((C.chart nu).liftedCov2 u) x hx).trans
      (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCov2 u)) nu)

theorem cov2ENorm_pointwise_limit (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (f : ℕ → RawCov2 M)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k alpha (f i - f j) < ENNReal.ofReal eps) :
    ∃ g : RawCov2 M, ∀ p (v w : TangentSpace I4 p),
      Tendsto (fun n => f n p v w) atTop (𝓝 (g p v w)) := by
  classical
  have hpoint (p : M) : ∃ a : TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ),
      ∀ v w, Tendsto (fun n => f n p v w) atTop (𝓝 (a v w)) := by
    obtain ⟨nu, x, hx, rfl⟩ := C.exists_inner_lift p
    let c := C.chart nu
    have hcauchy : CauchySeq (fun n => c.liftedCov2 (f n) x) := by
      apply Metric.cauchySeq_iff.mpr
      intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
      rw [dist_eq_norm, ofReal_norm]
      exact (liftedCov2_enorm_le_cov2ENorm_order C k alpha (f i - f j) nu x hx).trans_lt
        (hN i hi j hj)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨bilinearPullback (matrixToBilinear a) (c.tangentMap x).symm.toContinuousLinearMap,
      fun v w => ?_⟩
    have hh := (matrixToBilinear_eval_continuous
      ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)).continuousAt.tendsto.comp ha
    change Tendsto (fun n => matrixToBilinear (c.liftedCov2 (f n) x)
      ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)) atTop
      (𝓝 (matrixToBilinear a ((c.tangentMap x).symm v) ((c.tangentMap x).symm w))) at hh
    change Tendsto (fun n => f n (c.lift x) v w) atTop
      (𝓝 (matrixToBilinear a ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)))
    convert hh using 1
    funext n
    exact (c.matrix_recover_eval (f n) x v w).symm
  choose g hg using hpoint
  exact ⟨g, hg⟩


theorem cov2ENorm_definite (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (hu : C.cov2ENorm k alpha u = 0) : u = 0 := by
  ext p v w
  obtain ⟨nu, x, hx, rfl⟩ := C.exists_inner_lift p
  have ha : (C.chart nu).liftedCov2 u x = 0 := by
    apply enorm_eq_zero.mp
    exact le_antisymm (by simpa only [hu] using
      liftedCov2_enorm_le_cov2ENorm_order C k alpha u nu x hx) bot_le
  have hrec := (C.chart nu).matrix_recover_eval u x v w
  rw [ha] at hrec
  simpa [matrixToBilinear] using hrec.symm

/-- Actual global raw tensor limits retain all finite derivatives and converge
in the canonical supremum over every chart with one common Cauchy index. -/
theorem cov2ENorm_cauchy_pointwise_limit (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (f : ℕ → RawCov2 M) (g : RawCov2 M)
    (hf : ∀ n, Cov2Regular C k (f n))
    (hlim : ∀ p (v w : TangentSpace I4 p),
      Tendsto (fun n => f n p v w) atTop (𝓝 (g p v w)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k alpha (f i-f j) < ENNReal.ofReal eps) :
    Cov2Regular C k g ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm k alpha (f i-g) < ENNReal.ofReal eps := by
  have hclocal (nu : C.Index) : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCov2 (f i)-(C.chart nu).liftedCov2 (f j)) < ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨N,hN⟩ := hc eps heps
    exact ⟨N, fun i hi j hj => (le_iSup (fun nu => coordinateHolderENorm k alpha
      (C.chart nu).innerDomain ((C.chart nu).liftedCov2 (f i-f j))) nu).trans_lt (hN i hi j hj)⟩
  have hlimlocal (nu : C.Index) (x : FourSpace) :
      Tendsto (fun n => (C.chart nu).liftedCov2 (f n) x) atTop
        (𝓝 ((C.chart nu).liftedCov2 g x)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    exact hlim _ _ _
  have hlocal (nu : C.Index) := contDiffOn_of_uniformCauchy_iteratedFDerivWithin k
    (C.chart nu).innerOpen (fun n => (C.chart nu).liftedCov2 (f n)) ((C.chart nu).liftedCov2 g)
    (fun n => hf n nu)
    (uniformCauchy_jets_of_coordinateHolderENorm_cauchy k alpha (C.chart nu).innerOpen
      _ (fun n => hf n nu) (hclocal nu)) (fun x _ => hlimlocal nu x)
  have hg : Cov2Regular C k g := fun nu => (hlocal nu).1
  refine ⟨hg, fun eps heps => ?_⟩
  have hdpos : 0 < (k+2 : ℝ) := by positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * (k+2 : ℝ))) (by positivity)
  let K : ℝ≥0 := (ENNReal.ofReal (eps / (2 * (k+2 : ℝ)))).toNNReal
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * (k+2 : ℝ))) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  refine ⟨N, fun i hi => ?_⟩
  have hbound : C.cov2ENorm k alpha (f i-g) ≤ (k+2 : ℕ) * (K : ℝ≥0∞) := by
    apply iSup_le
    intro nu
    apply coordinateHolderENorm_sub_limit_le (C.chart nu).innerOpen
      (fun n => (C.chart nu).liftedCov2 (f n)) ((C.chart nu).liftedCov2 g)
      (fun n => hf n nu) (hg nu)
      (fun j hj x hx => ((hlocal nu).2 j hj).tendsto_at hx) i
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hK]
    exact (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 (f i-f n))) nu).trans (hN i hi n hn).le
  refine hbound.trans_lt ?_
  rw [hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
  push_cast
  have heq : (k+2 : ℝ) * (eps / (2 * (k+2 : ℝ))) = eps/2 := by field_simp
  rw [heq]
  linarith

/-- The actual symmetric tensor big Hölder space is Banach at every finite
order. Completeness is proved on the original raw tensor sections. -/
theorem tensorHolderSpace_sectionBanach (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace (tensorHolderSpace C k alpha) (C.cov2ENorm k alpha) := by
  refine
    { zero_mem := ?_
      add_mem := ?_
      smul_mem := ?_
      finite := fun u hu => hu.2.2
      zero_norm := cov2ENorm_zero C k alpha
      definite := fun u _ hu => cov2ENorm_definite C k alpha u hu
      triangle := fun u hu v hv => cov2ENorm_add_le C k alpha u v hu.2.1 hv.2.1
      homogeneous := fun c u hu => cov2ENorm_smul C k alpha c u hu.2.1
      complete := ?_ }
  · refine ⟨fun p v w => rfl, fun nu => ?_, ?_⟩
    · change ContDiffOn ℝ k (fun _ : FourSpace => (0 : Mat4)) (C.chart nu).innerDomain
      exact contDiffOn_const
    · rw [cov2ENorm_zero]
      exact ENNReal.zero_lt_top
  · intro u hu v hv
    refine ⟨?_, Cov2Regular.add hu.2.1 hv.2.1, ?_⟩
    · intro p a b
      change u p a b + v p a b = u p b a + v p b a
      rw [hu.1 p a b, hv.1 p a b]
    · exact (cov2ENorm_add_le C k alpha u v hu.2.1 hv.2.1).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hu.2.2, hv.2.2⟩)
  · intro c u hu
    refine ⟨?_, Cov2Regular.smul hu.2.1 c, ?_⟩
    · intro p a b
      change c * u p a b = c * u p b a
      rw [hu.1 p a b]
    · rw [cov2ENorm_smul C k alpha c u hu.2.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2.2
  · intro f hf hc
    obtain ⟨g, hg⟩ := cov2ENorm_pointwise_limit C k alpha f hc
    obtain ⟨hgReg, hconv⟩ := cov2ENorm_cauchy_pointwise_limit C k alpha f g
      (fun n => (hf n).2.1) hg hc
    refine ⟨g, ⟨?_, hgReg, ?_⟩, hconv⟩
    · intro p v w
      have heq : (fun n => f n p v w) = (fun n => f n p w v) := by
        funext n
        exact (hf n).1 p v w
      have h₁ := hg p v w
      rw [heq] at h₁
      exact tendsto_nhds_unique h₁ (hg p w v)
    · obtain ⟨N, hN⟩ := hconv 1 (by norm_num)
      have hEq : g = f N-(f N-g) := by
        ext p v w
        exact (sub_sub_cancel _ _).symm
      have hbound := cov2ENorm_sub_le C k alpha (f N) (f N-g) (hf N).2.1
        (Cov2Regular.sub (hf N).2.1 hgReg)
      rw [← hEq] at hbound
      exact hbound.trans_lt (ENNReal.add_lt_top.mpr
        ⟨(hf N).2.2, (hN N le_rfl).trans ENNReal.ofReal_lt_top⟩)

/-- The exact domain Banach input required by the natural C2α-to-C0α inverse. -/
theorem tensorHolderSpace_two_sectionBanach (C : BoundedLocalCover M)
    (alpha : ℝ≥0) (_halpha : 0 < alpha) :
    SectionBanachSpace (tensorHolderSpace C 2 alpha) (C.cov2ENorm 2 alpha) :=
  tensorHolderSpace_sectionBanach C 2 alpha

end K24.Global




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global
namespace CoverHolder
variable {X I E V : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def norm (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E)
    (k : ℕ) (alpha : ℝ≥0) (u : X) : ℝ≥0∞ :=
  ⨆ nu, coordinateHolderENorm k alpha (s nu) (L nu u)

def regular (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (k : ℕ) (u : X) : Prop :=
  ∀ nu, ContDiffOn ℝ k (L nu u) (s nu)

def space (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E)
    (k : ℕ) (alpha : ℝ≥0) : Set X :=
  {u | regular L s k u ∧ norm L s k alpha u < ⊤}

theorem regular_add {L : I → X →ₗ[ℝ] (E → V)} {s : I → Set E} {k : ℕ}
    {u v : X} (hu : regular L s k u) (hv : regular L s k v) : regular L s k (u+v) := by
  intro nu
  rw [map_add]
  exact (hu nu).add (hv nu)

theorem regular_sub {L : I → X →ₗ[ℝ] (E → V)} {s : I → Set E} {k : ℕ}
    {u v : X} (hu : regular L s k u) (hv : regular L s k v) : regular L s k (u-v) := by
  intro nu
  rw [map_sub]
  exact (hu nu).sub (hv nu)

theorem norm_add_le (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (k : ℕ) (alpha : ℝ≥0) (u v : X) (hu : regular L s k u) (hv : regular L s k v) :
    norm L s k alpha (u+v) ≤ norm L s k alpha u + norm L s k alpha v := by
  apply iSup_le
  intro nu
  rw [map_add]
  exact (coordinateHolderENorm_add_le k alpha (hs nu) _ _ (hu nu) (hv nu)).trans
    (add_le_add
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu u)) nu)
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu v)) nu))

theorem norm_sub_le (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (k : ℕ) (alpha : ℝ≥0) (u v : X) (hu : regular L s k u) (hv : regular L s k v) :
    norm L s k alpha (u-v) ≤ norm L s k alpha u + norm L s k alpha v := by
  apply iSup_le
  intro nu
  rw [map_sub]
  exact (coordinateHolderENorm_sub_le k alpha (hs nu) _ _ (hu nu) (hv nu)).trans
    (add_le_add
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu u)) nu)
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu v)) nu))

theorem norm_smul (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (k : ℕ) (alpha : ℝ≥0) (c : ℝ) (u : X) (hu : regular L s k u) :
    norm L s k alpha (c • u) = ENNReal.ofReal |c| * norm L s k alpha u := by
  unfold norm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro nu
  rw [map_smul]
  exact coordinateHolderENorm_smul k alpha (hs nu) c _ (hu nu)

theorem norm_zero (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (k : ℕ) (alpha : ℝ≥0) :
    norm L s k alpha 0 = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro nu
  rw [map_zero, coordinateHolderENorm_zero]
  exact le_rfl

theorem enorm_le_norm (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E)
    (k : ℕ) (alpha : ℝ≥0) (u : X) (nu : I) (x : E) (hx : x ∈ s nu) :
    ‖L nu u x‖ₑ ≤ norm L s k alpha u :=
  (enorm_le_coordinateHolderENorm k alpha (s nu) (L nu u) x hx).trans
    (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu u)) nu)

/-- An analytic assembly principle. Its reconstruction hypothesis is discharged
below on the actual vector and covector fibers; it assumes neither norm
completeness nor compatibility of limiting derivatives. -/
theorem sectionBanach [CompleteSpace V]
    (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (hseparate : ∀ u : X, (∀ nu x, x ∈ s nu → L nu u x = 0) → u = 0)
    (hrecover : ∀ f : ℕ → X,
      (∀ nu x, x ∈ s nu → CauchySeq (fun n => L nu (f n) x)) →
      ∃ g : X, ∀ nu x, x ∈ s nu → Tendsto (fun n => L nu (f n) x) atTop (𝓝 (L nu g x)))
    (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace (space L s k alpha) (norm L s k alpha) := by
  refine
    { zero_mem := ?_
      add_mem := ?_
      smul_mem := ?_
      finite := fun u hu => hu.2
      zero_norm := norm_zero L s k alpha
      definite := ?_
      triangle := fun u hu v hv => norm_add_le L s hs k alpha u v hu.1 hv.1
      homogeneous := fun c u hu => norm_smul L s hs k alpha c u hu.1
      complete := ?_ }
  · refine ⟨?_, ?_⟩
    · intro nu
      rw [map_zero]
      exact contDiffOn_const
    · rw [norm_zero]
      exact ENNReal.zero_lt_top
  · intro u hu v hv
    exact ⟨regular_add hu.1 hv.1, (norm_add_le L s hs k alpha u v hu.1 hv.1).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hu.2,hv.2⟩)⟩
  · intro c u hu
    refine ⟨?_, ?_⟩
    · intro nu
      rw [map_smul]
      exact (hu.1 nu).const_smul c
    · rw [norm_smul L s hs k alpha c u hu.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2
  · intro u _ hzero
    apply hseparate u
    intro nu x hx
    apply enorm_eq_zero.mp
    exact le_antisymm (by simpa only [hzero] using enorm_le_norm L s k alpha u nu x hx) bot_le
  · intro f hf hc
    have hcpoint (nu : I) (x : E) (hx : x ∈ s nu) : CauchySeq (fun n => L nu (f n) x) := by
      apply Metric.cauchySeq_iff.mpr
      intro eps heps
      obtain ⟨N,hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
      rw [dist_eq_norm, ofReal_norm]
      have hb := enorm_le_norm L s k alpha (f i-f j) nu x hx
      rw [map_sub] at hb
      exact hb.trans_lt (hN i hi j hj)
    obtain ⟨g,hg⟩ := hrecover f hcpoint
    have hclocal (nu : I) : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
        coordinateHolderENorm k alpha (s nu) (L nu (f i)-L nu (f j)) < ENNReal.ofReal eps := by
      intro eps heps
      obtain ⟨N,hN⟩ := hc eps heps
      refine ⟨N,fun i hi j hj => ?_⟩
      rw [← map_sub]
      exact (le_iSup _ nu).trans_lt (hN i hi j hj)
    have hlocal (nu : I) := contDiffOn_of_uniformCauchy_iteratedFDerivWithin k
      (hs nu) (fun n => L nu (f n)) (L nu g) (fun n => (hf n).1 nu)
      (uniformCauchy_jets_of_coordinateHolderENorm_cauchy k alpha (hs nu)
        _ (fun n => (hf n).1 nu) (hclocal nu)) (hg nu)
    have hgReg : regular L s k g := fun nu => (hlocal nu).1
    have hconv : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        norm L s k alpha (f i-g) < ENNReal.ofReal eps := by
      intro eps heps
      have hdpos : 0 < (k+2 : ℝ) := by positivity
      obtain ⟨N,hN⟩ := hc (eps / (2 * (k+2 : ℝ))) (by positivity)
      let K : ℝ≥0 := (ENNReal.ofReal (eps / (2 * (k+2 : ℝ)))).toNNReal
      have hK : (K : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * (k+2 : ℝ))) :=
        ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
      refine ⟨N,fun i hi => ?_⟩
      have hb : norm L s k alpha (f i-g) ≤ (k+2 : ℕ) * (K : ℝ≥0∞) := by
        apply iSup_le
        intro nu
        rw [map_sub]
        apply coordinateHolderENorm_sub_limit_le (hs nu) (fun n => L nu (f n)) (L nu g)
          (fun n => (hf n).1 nu) (hgReg nu)
          (fun j hj x hx => ((hlocal nu).2 j hj).tendsto_at hx) i
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [← map_sub,hK]
        exact (le_iSup _ nu).trans (hN i hi n hn).le
      refine hb.trans_lt ?_
      rw [hK,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
      push_cast
      have heq : (k+2 : ℝ) * (eps / (2 * (k+2 : ℝ))) = eps/2 := by field_simp
      rw [heq]
      linarith
    refine ⟨g,⟨hgReg,?_⟩,hconv⟩
    obtain ⟨N,hN⟩ := hconv 1 (by norm_num)
    have hbound := norm_sub_le L s hs k alpha (f N) (f N-g) (hf N).1
      (regular_sub (hf N).1 hgReg)
    rw [sub_sub_cancel] at hbound
    exact hbound.trans_lt (ENNReal.add_lt_top.mpr
      ⟨(hf N).2,(hN N le_rfl).trans ENNReal.ofReal_lt_top⟩)

end CoverHolder
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def liftedCovectorLinear (C : BoundedLocalCover M) (nu : C.Index) :
    RawCovector M →ₗ[ℝ] (FourSpace → Fin 4 → ℝ) where
  toFun := (C.chart nu).liftedCovector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liftedVectorLinear (C : BoundedLocalCover M) (nu : C.Index) :
    RawVector M →ₗ[ℝ] (FourSpace → FourSpace) where
  toFun := (C.chart nu).liftedVector
  map_add' u v := by
    funext x
    exact map_add ((C.chart nu).tangentMap x).symm _ _
  map_smul' c u := by
    funext x
    exact map_smul ((C.chart nu).tangentMap x).symm c (u ((C.chart nu).lift x))

theorem coefficientsToCovector_eval_continuous (v : FourSpace) :
    Continuous (fun a : Fin 4 → ℝ => coefficientsToCovector a v) := by
  unfold coefficientsToCovector
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  fun_prop

theorem LocalCoverChart.covector_recover_eval {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u : RawCovector M) (x : FourSpace)
    (v : TangentSpace I4 (c.lift x)) :
    coefficientsToCovector (c.liftedCovector u x) ((c.tangentMap x).symm v) = u (c.lift x) v := by
  have h := coefficientsToCovector_recover ((u (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap)
  have h' := congrArg (fun a : FourSpace →L[ℝ] ℝ => a ((c.tangentMap x).symm v)) h
  change coefficientsToCovector (c.liftedCovector u x) ((c.tangentMap x).symm v) =
    u (c.lift x) ((c.tangentMap x) ((c.tangentMap x).symm v)) at h'
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h'

theorem covector_lifts_separate (C : BoundedLocalCover M) (u : RawCovector M)
    (h : ∀ nu x, x ∈ (C.chart nu).innerDomain → liftedCovectorLinear C nu u x = 0) : u = 0 := by
  ext p v
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  have hrec := (C.chart nu).covector_recover_eval u x v
  have hh : (C.chart nu).liftedCovector u x = 0 := h nu x hx
  rw [hh] at hrec
  simpa [coefficientsToCovector] using hrec.symm

/-- Coordinate Cauchy data reconstructs actual continuous linear covectors on
the original fibers. The result converges in every chart, not only the chosen
chart used in its construction. -/
theorem covector_lifts_reconstruct (C : BoundedLocalCover M) (f : ℕ → RawCovector M)
    (hc : ∀ nu x, x ∈ (C.chart nu).innerDomain →
      CauchySeq (fun n => liftedCovectorLinear C nu (f n) x)) :
    ∃ g : RawCovector M, ∀ nu x, x ∈ (C.chart nu).innerDomain →
      Tendsto (fun n => liftedCovectorLinear C nu (f n) x) atTop
        (𝓝 (liftedCovectorLinear C nu g x)) := by
  classical
  have hpoint (p : M) : ∃ a : TangentSpace I4 p →L[ℝ] ℝ,
      ∀ v, Tendsto (fun n => f n p v) atTop (𝓝 (a v)) := by
    obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
    let c := C.chart nu
    obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (hc nu x hx)
    refine ⟨(coefficientsToCovector a).comp (c.tangentMap x).symm.toContinuousLinearMap,fun v => ?_⟩
    have hh := (coefficientsToCovector_eval_continuous ((c.tangentMap x).symm v)).continuousAt.tendsto.comp ha
    change Tendsto (fun n => coefficientsToCovector (c.liftedCovector (f n) x)
      ((c.tangentMap x).symm v)) atTop (𝓝 (coefficientsToCovector a ((c.tangentMap x).symm v))) at hh
    change Tendsto (fun n => f n (c.lift x) v) atTop
      (𝓝 (coefficientsToCovector a ((c.tangentMap x).symm v)))
    convert hh using 1
    funext n
    exact (c.covector_recover_eval (f n) x v).symm
  choose g hg using hpoint
  refine ⟨g,fun nu x _ => ?_⟩
  apply tendsto_pi_nhds.mpr
  intro a
  exact hg _ _

theorem vector_lifts_separate (C : BoundedLocalCover M) (u : RawVector M)
    (h : ∀ nu x, x ∈ (C.chart nu).innerDomain → liftedVectorLinear C nu u x = 0) : u = 0 := by
  funext p
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  change u ((C.chart nu).lift x) = 0
  have hh := congrArg ((C.chart nu).tangentMap x) (h nu x hx)
  change (C.chart nu).tangentMap x (((C.chart nu).tangentMap x).symm (u ((C.chart nu).lift x))) =
    (C.chart nu).tangentMap x 0 at hh
  simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using hh

/-- Vectors are reconstructed by the genuine tangent equivalence; continuity
of each other inverse tangent map gives convergence in every lifted chart. -/
theorem vector_lifts_reconstruct (C : BoundedLocalCover M) (f : ℕ → RawVector M)
    (hc : ∀ nu x, x ∈ (C.chart nu).innerDomain →
      CauchySeq (fun n => liftedVectorLinear C nu (f n) x)) :
    ∃ g : RawVector M, ∀ nu x, x ∈ (C.chart nu).innerDomain →
      Tendsto (fun n => liftedVectorLinear C nu (f n) x) atTop
        (𝓝 (liftedVectorLinear C nu g x)) := by
  classical
  have hpoint (p : M) : ∃ a : TangentSpace I4 p,
      Tendsto (fun n => f n p) atTop (𝓝 a) := by
    obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
    let c := C.chart nu
    obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (hc nu x hx)
    refine ⟨c.tangentMap x a,?_⟩
    have hh := (c.tangentMap x).continuous.continuousAt.tendsto.comp ha
    change Tendsto (fun n => c.tangentMap x ((c.tangentMap x).symm (f n (c.lift x))))
      atTop (𝓝 (c.tangentMap x a)) at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  choose g hg using hpoint
  refine ⟨g,fun nu x _ => ?_⟩
  exact ((C.chart nu).tangentMap x).symm.continuous.continuousAt.tendsto.comp (hg _)

end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- The actual ambient covector Hölder sections, with their exact canonical
cover norm, form a Banach space at every finite order. -/
theorem covectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha eta}
      (C.covectorENorm k alpha) := by
  exact CoverHolder.sectionBanach (liftedCovectorLinear C)
    (fun nu => (C.chart nu).innerDomain) (fun nu => (C.chart nu).innerOpen)
    (covector_lifts_separate C) (covector_lifts_reconstruct C) k alpha

/-- The actual ambient vector Hölder sections, with their exact canonical
cover norm, form a Banach space at every finite order. -/
theorem vectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha Y}
      (C.vectorENorm k alpha) := by
  exact CoverHolder.sectionBanach (liftedVectorLinear C)
    (fun nu => (C.chart nu).innerDomain) (fun nu => (C.chart nu).innerOpen)
    (vector_lifts_separate C) (vector_lifts_reconstruct C) k alpha

/-- Ambient Banach foundations for both the natural and shifted vector pairs. -/
theorem vectorCovectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha eta}
      (C.covectorENorm k alpha) ∧
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha Y}
      (C.vectorENorm k alpha) := by
  exact ⟨covectorHolder_sectionBanach C k alpha,vectorHolder_sectionBanach C k alpha⟩

end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
namespace HolderPerp
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem cov2Pi0_smul (rho : CircleAction M) (c : ℝ) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hcu : Cov2HaarIntegrable rho (c • u)) :
    cov2Pi0 rho (c • u) = c • cov2Pi0 rho u := by
  ext p v w
  rw [HaarSectors.cov2Pi0_apply rho (c • u) hcu]
  change (∫ t, c * actionPullbackCov2 rho t u p v w ∂circleHaar) =
    c * cov2Pi0 rho u p v w
  rw [integral_const_mul,HaarSectors.cov2Pi0_apply rho u hu]

theorem covectorPi0_smul (rho : CircleAction M) (c : ℝ) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hcu : CovectorHaarIntegrable rho (c • u)) :
    covectorPi0 rho (c • u) = c • covectorPi0 rho u := by
  ext p v
  rw [HaarSectors.covectorPi0_apply rho (c • u) hcu]
  change (∫ t, c * actionPullbackCovector rho t u p v ∂circleHaar) =
    c * covectorPi0 rho u p v
  rw [integral_const_mul,HaarSectors.covectorPi0_apply rho u hu]

theorem vectorPi0_smul (rho : CircleAction M) (c : ℝ) (u : RawVector M)
    (hu : VectorHaarIntegrable rho u) (hcu : VectorHaarIntegrable rho (c • u)) :
    vectorPi0 rho (c • u) = c • vectorPi0 rho u := by
  funext p
  letI : NormedAddCommGroup (TangentSpace I4 p) :=
    inferInstanceAs (NormedAddCommGroup FourSpace)
  letI : NormedSpace ℝ (TangentSpace I4 p) :=
    inferInstanceAs (NormedSpace ℝ FourSpace)
  rw [HaarSectors.vectorPi0_eq_integral rho (c • u) hcu]
  simp only [actionPullbackVector,Pi.smul_apply,map_smul]
  change (∫ t, c • (actionPullbackVector rho t u p : FourSpace) ∂circleHaar) =
    c • (vectorPi0 rho u p : FourSpace)
  rw [integral_smul,HaarSectors.vectorPi0_eq_integral rho u hu]

/-- Fiberwise symmetry is preserved by the actual Haar integral. -/
theorem cov2Pi0_symmetric (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hsym : IsSymmetricCov2 u) :
    IsSymmetricCov2 (cov2Pi0 rho u) := by
  intro p v w
  rw [HaarSectors.cov2Pi0_apply rho u hu,HaarSectors.cov2Pi0_apply rho u hu]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => hsym _ _ _

/-- Restricted linearity follows from actual integrability, not from
linearity of a totalized integral on nonintegrable raw sections. -/
theorem linearOn_of_sub_smul {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (S : Set X) (nx : X → ℝ≥0∞)
    (hS : SectionBanachSpace S nx) (A : X → Y)
    (hsub : ∀ u ∈ S, ∀ v ∈ S, A (u-v) = A u-A v)
    (hsmul : ∀ (c : ℝ) (u : X), u ∈ S → A (c • u) = c • A u) :
    SectionLinearOn S A := by
  refine ⟨?_,?_,hsmul⟩
  · simpa only [sub_self] using hsub 0 hS.zero_mem 0 hS.zero_mem
  · intro u hu v hv
    have hh := hsub (u+v) (hS.add_mem u hu v hv) v hv
    rw [add_sub_cancel_right] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm

theorem cov2Pi0_linearOn (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M)
    (hi : ∀ u ∈ tensorHolderSpace C k alpha, Cov2HaarIntegrable rho u) :
    SectionLinearOn (tensorHolderSpace C k alpha) (cov2Pi0 rho) := by
  apply linearOn_of_sub_smul _ _ (tensorHolderSpace_sectionBanach C k alpha)
  · intro u hu v hv
    exact HaarSectors.cov2Pi0_sub rho u v (hi u hu) (hi v hv)
  · intro c u hu
    exact cov2Pi0_smul rho c u (hi u hu)
      (hi (c • u) ((tensorHolderSpace_sectionBanach C k alpha).smul_mem c u hu))

theorem covectorPi0_linearOn (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M)
    (hi : ∀ u : RawCovector M, C.CovectorHolder k alpha u → CovectorHaarIntegrable rho u) :
    SectionLinearOn {u : RawCovector M | C.CovectorHolder k alpha u} (covectorPi0 rho) := by
  apply linearOn_of_sub_smul _ _ (covectorHolder_sectionBanach C k alpha)
  · intro u hu v hv
    exact HaarSectors.covectorPi0_sub rho u v (hi u hu) (hi v hv)
  · intro c u hu
    exact covectorPi0_smul rho c u (hi u hu)
      (hi (c • u) ((covectorHolder_sectionBanach C k alpha).smul_mem c u hu))

theorem vectorPi0_linearOn (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M)
    (hi : ∀ u : RawVector M, C.VectorHolder k alpha u → VectorHaarIntegrable rho u) :
    SectionLinearOn {u : RawVector M | C.VectorHolder k alpha u} (vectorPi0 rho) := by
  apply linearOn_of_sub_smul _ _ (vectorHolder_sectionBanach C k alpha)
  · intro u hu v hv
    exact HaarSectors.vectorPi0_sub rho u v (hi u hu) (hi v hv)
  · intro c u hu
    exact vectorPi0_smul rho c u (hi u hu)
      (hi (c • u) ((vectorHolder_sectionBanach C k alpha).smul_mem c u hu))

end HolderPerp
end K24.Global



/- Inspected normed-subtype/completeness proof reused from K24INV adapter
source commit 35b6b77d6dd76b87bbf54fb49b73bc6b9fed156b. This retains the
original admissible sections and their finite canonical extended norm. -/

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal Topology

namespace K24.Global.SectionBanachSpace

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}

/-- The submodule consists of the original admissible sections. -/
def submodule (h : SectionBanachSpace S nx) : Submodule ℝ X where
  carrier := S
  zero_mem' := h.zero_mem
  add_mem' := fun hu hv => h.add_mem _ hu _ hv
  smul_mem' := fun c _ hu => h.smul_mem c _ hu

/-- The real norm is obtained from the finite, supplied section norm. -/
@[instance_reducible]
def sectionNorm (h : SectionBanachSpace S nx) : Norm h.submodule :=
  ⟨fun u => (nx u).toReal⟩

theorem normCore (h : SectionBanachSpace S nx) :
    letI := h.sectionNorm
    NormedSpace.Core ℝ h.submodule := by
  letI := h.sectionNorm
  refine
    { norm_nonneg := fun _ => ENNReal.toReal_nonneg
      norm_smul := ?_
      norm_triangle := ?_
      norm_eq_zero_iff := ?_ }
  · intro c u
    change (nx (c • (u : X))).toReal = ‖c‖ * (nx u).toReal
    rw [h.homogeneous c u u.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  · intro u v
    change (nx ((u : X) + v)).toReal ≤ (nx u).toReal + (nx v).toReal
    calc
      _ ≤ (nx u + nx v).toReal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(h.finite u u.property).ne,
          (h.finite v v.property).ne⟩) (h.triangle u u.property v v.property)
      _ = _ := ENNReal.toReal_add (h.finite u u.property).ne (h.finite v v.property).ne
  · intro u
    change (nx u).toReal = 0 ↔ u = 0
    constructor
    · intro hu
      apply Subtype.ext
      exact h.definite u u.property
        ((ENNReal.toReal_eq_zero_iff _).mp hu |>.resolve_right (h.finite u u.property).ne)
    · intro hu
      subst u
      simp [h.zero_norm]

/-- A normed group on the original section submodule, with its given norm. -/
abbrev normedAddCommGroup (h : SectionBanachSpace S nx) :
    NormedAddCommGroup h.submodule :=
  letI := h.sectionNorm
  NormedAddCommGroup.ofCore h.normCore

/-- The scalar action remains the original pointwise scalar action. -/
abbrev normedSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    NormedSpace ℝ h.submodule :=
  letI := h.normedAddCommGroup
  NormedSpace.ofCore h.normCore

theorem norm_eq_toReal (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ‖u‖ = (nx u).toReal := rfl

theorem ofReal_norm (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ENNReal.ofReal ‖u‖ = nx u :=
  ENNReal.ofReal_toReal (h.finite u u.property).ne

/-- The explicit section Cauchy-sequence axiom supplies completeness of the
actual section norm, without completing or enlarging the section space. -/
theorem completeSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    CompleteSpace h.submodule := by
  letI := h.normedAddCommGroup
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  obtain ⟨v, hv, hlim⟩ := h.complete (fun n => f n) (fun n => (f n).property) (by
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hij := hN i hi j hj
    rw [dist_eq_norm] at hij
    have hh := (ENNReal.ofReal_lt_ofReal_iff heps).mpr hij
    rwa [h.ofReal_norm (f i - f j)] at hh)
  refine ⟨⟨v, hv⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hlim eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  rw [h.ofReal_norm]
  exact hN i hi

end K24.Global.SectionBanachSpace




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology
namespace K24.Global
namespace HolderPerpAll

/-- Compact scalar orbit continuity and Banach-Steinhaus make the actual
Haar-average functional continuous. Operator-norm measurability is not assumed. -/
def averageFunctional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : Circle → E →L[ℝ] ℝ) (hc : ∀ u, Continuous (fun t => L t u)) : E →L[ℝ] ℝ := by
  have hi (u : E) : Integrable (fun t => L t u) circleHaar :=
    (hc u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUB := banach_steinhaus (g := L) (by
    intro u
    obtain ⟨B,hB⟩ := (isCompact_range (hc u).norm).bddAbove
    exact ⟨B,fun t => hB (Set.mem_range_self t)⟩)
  let C : ℝ := Classical.choose hUB
  have hC : ∀ t, ‖L t‖ ≤ C := Classical.choose_spec hUB
  let A : E →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∫ t, L t u ∂circleHaar
      map_add' := by
        intro u v
        simp only [map_add]
        exact integral_add (hi u) (hi v)
      map_smul' := by
        intro c u
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c (fun t => L t u) }
  apply A.mkContinuous C
  intro u
  have hbound : ∀ᵐ t ∂circleHaar, ‖L t u‖ ≤ C * ‖u‖ :=
    Filter.Eventually.of_forall fun t => (L t).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hC t) (norm_nonneg u))
  change ‖∫ t, L t u ∂circleHaar‖ ≤ C * ‖u‖
  simpa using norm_integral_le_of_norm_le_const hbound

@[simp] theorem averageFunctional_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : Circle → E →L[ℝ] ℝ) (hc : ∀ u, Continuous (fun t => L t u)) (u : E) :
    averageFunctional L hc u = ∫ t, L t u ∂circleHaar := rfl

/-- Closedness tested by genuine separating scalar observations suffices for
completeness of the original section kernel in its unchanged source norm. -/
theorem sectionBanach_kernel_of_evaluation_continuous
    {X Y I : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (S : Set X) (nx : X → ℝ≥0∞) (hS : SectionBanachSpace S nx)
    (A : X → Y) (hLinear : SectionLinearOn S A) (ev : I → Y → ℝ)
    (hsep : ∀ y : Y, (∀ i, ev i y = ev i 0) → y = 0)
    (hcont : letI := hS.normedAddCommGroup
      ∀ i, Continuous (fun u : hS.submodule => ev i (A u))) :
    SectionBanachSpace {u : X | u ∈ S ∧ A u = 0} nx := by
  letI := hS.normedAddCommGroup
  refine
    { zero_mem := ⟨hS.zero_mem,hLinear.1⟩
      add_mem := ?_
      smul_mem := ?_
      finite := fun u hu => hS.finite u hu.1
      zero_norm := hS.zero_norm
      definite := fun u hu => hS.definite u hu.1
      triangle := fun u hu v hv => hS.triangle u hu.1 v hv.1
      homogeneous := fun c u hu => hS.homogeneous c u hu.1
      complete := ?_ }
  · intro u hu v hv
    refine ⟨hS.add_mem u hu.1 v hv.1,?_⟩
    rw [hLinear.2.1 u hu.1 v hv.1,hu.2,hv.2,add_zero]
  · intro c u hu
    refine ⟨hS.smul_mem c u hu.1,?_⟩
    rw [hLinear.2.2 c u hu.1,hu.2,smul_zero]
  · intro f hf hc
    obtain ⟨g,hg,hconv⟩ := hS.complete f (fun n => (hf n).1) hc
    refine ⟨g,⟨hg,?_⟩,hconv⟩
    have ht : Tendsto (fun n => (⟨f n,(hf n).1⟩ : hS.submodule)) atTop
        (𝓝 (⟨g,hg⟩ : hS.submodule)) := by
      apply Metric.tendsto_atTop.mpr
      intro eps heps
      obtain ⟨N,hN⟩ := hconv eps heps
      refine ⟨N,fun n hn => ?_⟩
      rw [dist_eq_norm]
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
      rw [hS.ofReal_norm]
      exact hN n hn
    apply hsep (A g)
    intro i
    have he := (hcont i).continuousAt.tendsto.comp ht
    change Tendsto (fun n => ev i (A (f n))) atTop (𝓝 (ev i (A g))) at he
    have heq : (fun n => ev i (A (f n))) = fun _ : ℕ => ev i 0 := by
      funext n
      rw [(hf n).2]
    rw [heq] at he
    exact tendsto_nhds_unique he tendsto_const_nhds

end HolderPerpAll
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
namespace HolderPerpAll

/-- Bounded coefficient observations induce continuous linear functionals on
exactly the original section subtype with its supplied norm. -/
def boundedEvaluation {X V : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set X} {nx : X → ℝ≥0∞} (hS : SectionBanachSpace S nx)
    (L : X →ₗ[ℝ] V) (hb : ∀ u ∈ S, ‖L u‖ₑ ≤ nx u) (q : V →L[ℝ] ℝ) :
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := hS.normedSpace
    hS.submodule →L[ℝ] ℝ := by
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  let A : hS.submodule →ₗ[ℝ] ℝ := q.toLinearMap.comp (L.comp hS.submodule.subtype)
  apply A.mkContinuous ‖q‖
  intro u
  have hv : ‖L (u : X)‖ ≤ ‖u‖ := by
    change ‖L (u : X)‖ ≤ (nx u).toReal
    have hh := ENNReal.toReal_mono (hS.finite u u.property).ne (hb u u.property)
    simpa only [← ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg _)] using hh
  exact (q.le_opNorm (L u)).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg q))

def covectorCoefficientEvaluation (v : FourSpace) : (Fin 4 → ℝ) →L[ℝ] ℝ where
  toFun a := coefficientsToCovector a v
  map_add' a b := by
    simp [HaarSectors.coefficientsToCovector_apply,Finset.sum_add_distrib,add_mul,mul_add]
  map_smul' c a := by
    simp [HaarSectors.coefficientsToCovector_apply,Finset.mul_sum,mul_assoc,mul_left_comm]
  cont := coefficientsToCovector_eval_continuous v

def matrixCoefficientEvaluation (v w : FourSpace) : Mat4 →L[ℝ] ℝ where
  toFun a := matrixToBilinear a v w
  map_add' a b := by
    simp [HaarSectors.matrixToBilinear_apply,Finset.sum_add_distrib,add_mul,mul_add]
  map_smul' c a := by
    simp [HaarSectors.matrixToBilinear_apply,Finset.mul_sum,mul_assoc,mul_left_comm]
  cont := matrixToBilinear_eval_continuous v w

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- Every actual covector evaluation is bounded in every finite-order cover norm. -/
theorem exists_covectorEvaluation (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (p : M) (v : TangentSpace I4 p) :
    let hS := covectorHolder_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := hS.normedSpace
    ∃ L : hS.submodule →L[ℝ] ℝ, ∀ u, L u = (u : RawCovector M) p v := by
  let hS := covectorHolder_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  let c := C.chart nu
  let Lraw : RawCovector M →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun u => c.liftedCovector u x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb : ∀ u ∈ {u : RawCovector M | C.CovectorHolder k alpha u},
      ‖Lraw u‖ₑ ≤ C.covectorENorm k alpha u := by
    intro u _
    exact (enorm_le_coordinateHolderENorm k alpha c.innerDomain (c.liftedCovector u) x hx).trans
      (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCovector u)) nu)
  refine ⟨boundedEvaluation hS Lraw hb (covectorCoefficientEvaluation ((c.tangentMap x).symm v)),?_⟩
  intro u
  change coefficientsToCovector (c.liftedCovector (u : RawCovector M) x)
    ((c.tangentMap x).symm v) = (u : RawCovector M) (c.lift x) v
  exact c.covector_recover_eval u x v

/-- Every continuous linear fiber observation of an actual vector is bounded. -/
theorem exists_vectorEvaluation (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (p : M) (ell : TangentSpace I4 p →L[ℝ] ℝ) :
    let hS := vectorHolder_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := hS.normedSpace
    ∃ L : hS.submodule →L[ℝ] ℝ, ∀ u, L u = ell ((u : RawVector M) p) := by
  let hS := vectorHolder_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  let c := C.chart nu
  let Lraw : RawVector M →ₗ[ℝ] FourSpace :=
    { toFun := fun u => c.liftedVector u x
      map_add' := fun u v => map_add (c.tangentMap x).symm _ _
      map_smul' := fun a u => map_smul (c.tangentMap x).symm a _ }
  have hb : ∀ u ∈ {u : RawVector M | C.VectorHolder k alpha u},
      ‖Lraw u‖ₑ ≤ C.vectorENorm k alpha u := by
    intro u _
    exact (enorm_le_coordinateHolderENorm k alpha c.innerDomain (c.liftedVector u) x hx).trans
      (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedVector u)) nu)
  refine ⟨boundedEvaluation hS Lraw hb (ell.comp (c.tangentMap x).toContinuousLinearMap),?_⟩
  intro u
  change ell (c.tangentMap x ((c.tangentMap x).symm ((u : RawVector M) (c.lift x)))) =
    ell ((u : RawVector M) (c.lift x))
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Every actual symmetric tensor evaluation is bounded in the supplied norm. -/
theorem exists_cov2Evaluation (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (p : M) (v w : TangentSpace I4 p) :
    let hS := tensorHolderSpace_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := hS.normedSpace
    ∃ L : hS.submodule →L[ℝ] ℝ, ∀ u, L u = (u : RawCov2 M) p v w := by
  let hS := tensorHolderSpace_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  let c := C.chart nu
  let Lraw : RawCov2 M →ₗ[ℝ] Mat4 :=
    { toFun := fun u => c.liftedCov2 u x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb : ∀ u ∈ tensorHolderSpace C k alpha, ‖Lraw u‖ₑ ≤ C.cov2ENorm k alpha u :=
    fun u _ => liftedCov2_enorm_le_cov2ENorm_order C k alpha u nu x hx
  refine ⟨boundedEvaluation hS Lraw hb
    (matrixCoefficientEvaluation ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)),?_⟩
  intro u
  change matrixToBilinear (c.liftedCov2 (u : RawCov2 M) x)
    ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) = (u : RawCov2 M) (c.lift x) v w
  exact c.matrix_recover_eval u x v w

end HolderPerpAll
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global
namespace HolderPerpAll
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

lemma covectorHolder_integrable (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M) (u : RawCovector M) (hu : C.CovectorHolder k alpha u) :
    CovectorHaarIntegrable rho u :=
  HaarSectors.covector_haar_integrable_of_continuous rho u
    (NativeContinuity.covector_evaluation_continuous u
      (CoverContinuity.covectorHolder_native_contDiff_zero C k alpha u hu))

lemma vectorHolder_integrable (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M) (u : RawVector M) (hu : C.VectorHolder k alpha u) :
    VectorHaarIntegrable rho u :=
  HaarSectors.vector_haar_integrable_of_continuous rho u
    (NativeContinuity.vector_section_continuous u
      (CoverContinuity.vectorHolder_native_contDiff_zero C k alpha u hu))

lemma cov2Holder_integrable (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) :
    Cov2HaarIntegrable rho u :=
  HaarSectors.cov2_haar_integrable_of_continuous rho u
    (NativeContinuity.cov2_evaluation_continuous u
      (CoverContinuity.cov2Holder_native_contDiff_zero C k alpha u hu))

/-- Scalar evaluations of the actual covector Haar average are continuous in
any finite-order canonical section norm. -/
theorem covectorPi0_evaluation_continuous (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) (p : M) (v : TangentSpace I4 p) :
    let hS := covectorHolder_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (fun u : hS.submodule => covectorPi0 rho u p v) := by
  let hS := covectorHolder_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  letI := (hS.completeSpace)
  change Continuous (fun u : hS.submodule => covectorPi0 rho u p v)
  have he (t : Circle) : ∃ L : hS.submodule →L[ℝ] ℝ,
      ∀ u, L u = actionPullbackCovector rho t (u : RawCovector M) p v := by
    exact exists_covectorEvaluation C k alpha (rho.act t p) (mfderiv I4 I4 (rho.act t) p v)
  choose L hL using he
  have hc (u : hS.submodule) : Continuous (fun t => L t u) := by
    simp_rw [hL]
    exact HaarSectors.covector_orbit_continuous rho u
      (NativeContinuity.covector_evaluation_continuous (u : RawCovector M)
        (CoverContinuity.covectorHolder_native_contDiff_zero C k alpha (u : RawCovector M) u.property)) p v
  have heq : (fun u : hS.submodule => covectorPi0 rho u p v) = averageFunctional L hc := by
    funext u
    rw [averageFunctional_apply,HaarSectors.covectorPi0_apply rho u
      (covectorHolder_integrable C k alpha rho u u.property)]
    simp_rw [hL]
  rw [heq]
  exact (averageFunctional L hc).continuous

/-- Scalar evaluations of the actual tensor Haar average are continuous in
any finite-order canonical section norm. -/
theorem cov2Pi0_evaluation_continuous (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) (p : M) (v w : TangentSpace I4 p) :
    let hS := tensorHolderSpace_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (fun u : hS.submodule => cov2Pi0 rho u p v w) := by
  let hS := tensorHolderSpace_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  letI := (hS.completeSpace)
  change Continuous (fun u : hS.submodule => cov2Pi0 rho u p v w)
  have he (t : Circle) : ∃ L : hS.submodule →L[ℝ] ℝ,
      ∀ u, L u = actionPullbackCov2 rho t (u : RawCov2 M) p v w := by
    exact exists_cov2Evaluation C k alpha (rho.act t p)
      (mfderiv I4 I4 (rho.act t) p v) (mfderiv I4 I4 (rho.act t) p w)
  choose L hL using he
  have hc (u : hS.submodule) : Continuous (fun t => L t u) := by
    simp_rw [hL]
    exact HaarSectors.cov2_orbit_continuous rho u
      (NativeContinuity.cov2_evaluation_continuous (u : RawCov2 M)
        (CoverContinuity.cov2Holder_native_contDiff_zero C k alpha (u : RawCov2 M) u.property.2)) p v w
  have heq : (fun u : hS.submodule => cov2Pi0 rho u p v w) = averageFunctional L hc := by
    funext u
    rw [averageFunctional_apply,HaarSectors.cov2Pi0_apply rho u
      (cov2Holder_integrable C k alpha rho u u.property.2)]
    simp_rw [hL]
  rw [heq]
  exact (averageFunctional L hc).continuous

/-- Continuous linear fiber observations of the actual vector Haar average
are continuous in any finite-order canonical section norm. -/
theorem vectorPi0_evaluation_continuous (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) (p : M) (ell : TangentSpace I4 p →L[ℝ] ℝ) :
    let hS := vectorHolder_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (fun u : hS.submodule => ell (vectorPi0 rho u p)) := by
  let hS := vectorHolder_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  letI := (hS.completeSpace)
  change Continuous (fun u : hS.submodule => ell (vectorPi0 rho u p))
  have he (t : Circle) : ∃ L : hS.submodule →L[ℝ] ℝ,
      ∀ u, L u = ell (actionPullbackVector rho t (u : RawVector M) p) := by
    exact exists_vectorEvaluation C k alpha (rho.act t p)
      (ell.comp (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t p)))
  choose L hL using he
  have hc (u : hS.submodule) : Continuous (fun t => L t u) := by
    simp_rw [hL]
    exact ell.continuous.comp (HaarSectors.vector_orbit_continuous rho u
      (NativeContinuity.vector_section_continuous (u : RawVector M)
        (CoverContinuity.vectorHolder_native_contDiff_zero C k alpha (u : RawVector M) u.property)) p)
  have heq : (fun u : hS.submodule => ell (vectorPi0 rho u p)) = averageFunctional L hc := by
    funext u
    letI : NormedAddCommGroup (TangentSpace I4 p) := inferInstanceAs (NormedAddCommGroup FourSpace)
    letI : NormedSpace ℝ (TangentSpace I4 p) := inferInstanceAs (NormedSpace ℝ FourSpace)
    letI : CompleteSpace (TangentSpace I4 p) := inferInstanceAs (CompleteSpace FourSpace)
    have hi := vectorHolder_integrable C k alpha rho u u.property
    rw [averageFunctional_apply,HaarSectors.vectorPi0_eq_integral rho u hi p]
    rw [← ell.integral_comp_comm (HaarSectors.vector_orbit_integrable rho u hi p)]
    simp_rw [hL]
  rw [heq]
  exact (averageFunctional L hc).continuous

end HolderPerpAll
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global
namespace HolderPerpAll
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual zero-average covector sections form a Banach space at all finite
orders, without a quantitative action bound. -/
theorem covectorHolderPerp_sectionBanach (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) :
    SectionBanachSpace (covectorHolderPerp C k alpha rho) (C.covectorENorm k alpha) := by
  apply sectionBanach_kernel_of_evaluation_continuous
    {u : RawCovector M | C.CovectorHolder k alpha u} (C.covectorENorm k alpha)
    (covectorHolder_sectionBanach C k alpha) (covectorPi0 rho)
    (HolderPerp.covectorPi0_linearOn C k alpha rho (covectorHolder_integrable C k alpha rho))
    (fun (q : Σ p : M, TangentSpace I4 p) u => u q.1 q.2)
  · intro u hu
    ext p v
    exact hu ⟨p,v⟩
  · intro q
    exact covectorPi0_evaluation_continuous C k alpha rho q.1 q.2

/-- The actual zero-average vector sections form a Banach space at all finite
orders, using the genuine inverse-action pullback. -/
theorem vectorHolderPerp_sectionBanach (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) :
    SectionBanachSpace (vectorHolderPerp C k alpha rho) (C.vectorENorm k alpha) := by
  apply sectionBanach_kernel_of_evaluation_continuous
    {u : RawVector M | C.VectorHolder k alpha u} (C.vectorENorm k alpha)
    (vectorHolder_sectionBanach C k alpha) (vectorPi0 rho)
    (HolderPerp.vectorPi0_linearOn C k alpha rho (vectorHolder_integrable C k alpha rho))
    (fun (q : Σ p : M, TangentSpace I4 p →L[ℝ] ℝ) u => q.2 (u q.1))
  · intro u hu
    funext p
    letI : NormedAddCommGroup (TangentSpace I4 p) := inferInstanceAs (NormedAddCommGroup FourSpace)
    letI : NormedSpace ℝ (TangentSpace I4 p) := inferInstanceAs (NormedSpace ℝ FourSpace)
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
    intro ell
    simpa using hu ⟨p,ell⟩
  · intro q
    exact vectorPi0_evaluation_continuous C k alpha rho q.1 q.2

/-- The actual symmetric zero-average tensor sections form a Banach space at
all finite orders, in the literal canonical tensor norm. -/
theorem tensorHolderPerp_sectionBanach (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) :
    SectionBanachSpace (tensorHolderPerp C k alpha rho) (C.cov2ENorm k alpha) := by
  apply sectionBanach_kernel_of_evaluation_continuous
    (tensorHolderSpace C k alpha) (C.cov2ENorm k alpha)
    (tensorHolderSpace_sectionBanach C k alpha) (cov2Pi0 rho)
    (HolderPerp.cov2Pi0_linearOn C k alpha rho
      (fun u hu => cov2Holder_integrable C k alpha rho u hu.2))
    (fun (q : Σ p : M, TangentSpace I4 p × TangentSpace I4 p) u => u q.1 q.2.1 q.2.2)
  · intro u hu
    ext p v w
    exact hu ⟨p,v,w⟩
  · intro q
    exact cov2Pi0_evaluation_continuous C k alpha rho q.1 q.2.1 q.2.2

/-- All three literal zero-average Hölder section spaces are Banach at every
finite order. Kernel closedness does not require a higher-order projection estimate. -/
theorem holderPerp_all_orders_sectionBanach (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (rho : CircleAction M) :
    SectionBanachSpace (tensorHolderPerp C k alpha rho) (C.cov2ENorm k alpha) ∧
    SectionBanachSpace (vectorHolderPerp C k alpha rho) (C.vectorENorm k alpha) ∧
    SectionBanachSpace (covectorHolderPerp C k alpha rho) (C.covectorENorm k alpha) := by
  exact ⟨tensorHolderPerp_sectionBanach C k alpha rho,
    vectorHolderPerp_sectionBanach C k alpha rho,covectorHolderPerp_sectionBanach C k alpha rho⟩

end HolderPerpAll
end K24.Global

open scoped NNReal ENNReal Manifold ContDiff
universe u

theorem inclusionsPerpFoundation_solution :
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    [IsManifold K24.Global.I4 ∞ M] (C : K24.Global.BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) (rho : K24.Global.CircleAction M),
    K24.Global.SectionBanachSpace (K24.Global.tensorHolderPerp C k alpha rho)
      (C.cov2ENorm k alpha) ∧
    K24.Global.SectionBanachSpace (K24.Global.vectorHolderPerp C k alpha rho)
      (C.vectorENorm k alpha) ∧
    K24.Global.SectionBanachSpace (K24.Global.covectorHolderPerp C k alpha rho)
      (C.covectorENorm k alpha) := by
  intro M _ _ _ C k alpha rho
  exact K24.Global.HolderPerpAll.holderPerp_all_orders_sectionBanach C k alpha rho




-- BEGIN FiniteIndex

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Lower

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- Each internal atlas has finitely many charts: every chart meets the compact
closure of the lift of its inner base, and the chart sources are locally finite. -/
theorem finite_chartIndex (C : BoundedLocalCover M) (a : C.CoverIndex) :
    Finite (C.ChartIndex a) := by
  have hfin := (C.internalLocallyFinite a).finite_nonempty_inter_compact
    (C.cover a).innerCompactClosure
  apply Finite.of_finite_univ
  apply hfin.subset
  intro j _
  obtain ⟨x, hx⟩ := (C.localChart a j).innerNonempty
  refine ⟨(C.localChart a j).coordinate.symm x, ?_, ?_⟩
  · exact (C.localChart a j).coordinate.map_target
      ((C.localChart a j).outerSubsetTarget
        ((C.localChart a j).closureInnerSubset (subset_closure hx)))
  · exact subset_closure ((C.localChart a j).innerMapsToBase x hx)

/-- A cover which contributes an actual chart has nonempty base. Empty covers
may be indexed arbitrarily, so finiteness is asserted only for active indices. -/
theorem baseDomain_nonempty_of_chart (C : BoundedLocalCover M)
    (a : C.CoverIndex) (j : C.ChartIndex a) : (C.cover a).baseDomain.Nonempty := by
  obtain ⟨x, hx⟩ := (C.localChart a j).innerNonempty
  exact ⟨(C.localChart a j).lift x,
    (C.cover a).innerBaseSubset ((C.localChart a j).innerMapsToBase x hx)⟩

/-- On a compact manifold the flattened index of genuine inner coordinate
charts is finite. No finiteness assumption on the (possibly padded) cover
index type is needed. -/
theorem finite_coverIndex [CompactSpace M] (C : BoundedLocalCover M) :
    Finite C.Index := by
  let A := {a : C.CoverIndex // (C.cover a).baseDomain.Nonempty}
  have hA : {a : C.CoverIndex | (C.cover a).baseDomain.Nonempty}.Finite :=
    C.locallyFinite.finite_nonempty_of_compact
  let : Finite A := hA.to_subtype
  let : ∀ a : A, Finite (C.ChartIndex a.val) := fun a => finite_chartIndex C a.val
  let f : C.Index → Sigma (fun a : A => C.ChartIndex a.val) := fun ν =>
    ⟨⟨ν.1, baseDomain_nonempty_of_chart C ν.1 ν.2⟩, ν.2⟩
  let g : Sigma (fun a : A => C.ChartIndex a.val) → C.Index := fun ν => ⟨ν.1.val, ν.2⟩
  exact Finite.of_injective f (Function.LeftInverse.injective (show Function.LeftInverse g f by
    intro ν
    rfl))

/-- Finitely many finite vector coordinate norms give the literal cover norm. -/
theorem vectorENorm_lt_top_iff [CompactSpace M] (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) (Y : RawVector M) :
    C.vectorENorm k alpha Y < ⊤ ↔
      ∀ ν : C.Index, coordinateHolderENorm k alpha (C.chart ν).innerDomain
        ((C.chart ν).liftedVector Y) < ⊤ := by
  let : Finite C.Index := finite_coverIndex C
  constructor
  · intro h ν
    exact (le_iSup (fun μ : C.Index => coordinateHolderENorm k alpha
      (C.chart μ).innerDomain ((C.chart μ).liftedVector Y)) ν).trans_lt h
  · intro h
    exact lt_top_iff_ne_top.mpr (iSup_ne_top fun ν => ne_of_lt (h ν))

/-- Finitely many finite covector coordinate norms give the literal cover norm. -/
theorem covectorENorm_lt_top_iff [CompactSpace M] (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) (u : RawCovector M) :
    C.covectorENorm k alpha u < ⊤ ↔
      ∀ ν : C.Index, coordinateHolderENorm k alpha (C.chart ν).innerDomain
        ((C.chart ν).liftedCovector u) < ⊤ := by
  let : Finite C.Index := finite_coverIndex C
  constructor
  · intro h ν
    exact (le_iSup (fun μ : C.Index => coordinateHolderENorm k alpha
      (C.chart μ).innerDomain ((C.chart μ).liftedCovector u)) ν).trans_lt h
  · intro h
    exact lt_top_iff_ne_top.mpr (iSup_ne_top fun ν => ne_of_lt (h ν))

/-- Finitely many finite tensor coordinate norms give the literal cover norm. -/
theorem cov2ENorm_lt_top_iff [CompactSpace M] (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) (u : RawCov2 M) :
    C.cov2ENorm k alpha u < ⊤ ↔
      ∀ ν : C.Index, coordinateHolderENorm k alpha (C.chart ν).innerDomain
        ((C.chart ν).liftedCov2 u) < ⊤ := by
  let : Finite C.Index := finite_coverIndex C
  constructor
  · intro h ν
    exact (le_iSup (fun μ : C.Index => coordinateHolderENorm k alpha
      (C.chart μ).innerDomain ((C.chart μ).liftedCov2 u)) ν).trans_lt h
  · intro h
    exact lt_top_iff_ne_top.mpr (iSup_ne_top fun ν => ne_of_lt (h ν))


end K24.Global.Holder20261026Lower

-- END FiniteIndex

-- BEGIN NativeFoundation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter IsManifold
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal

namespace K24.Global.NativeRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

omit [IsManifold I4 ∞ M] in
lemma lift_smoothAt (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  have hc : c.coordinate ∈ maximalAtlas I4 ∞ F.TotalSpace :=
    subset_maximalAtlas c.coordinate_mem_atlas
  exact F.projectionSmooth.contMDiffAt.comp x
    (contMDiffAt_symm_of_mem_maximalAtlas hc (c.outerSubsetTarget hx))

lemma coord_smoothAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace d) ∘ c.lift) x := by
  exact ((contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I4) (n := ∞) d) hd).comp x
    (lift_smoothAt c x hx)).contDiffAt

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

omit [IsManifold I4 ∞ M] in
lemma liftedCovector_apply (c : LocalCoverChart F) (eta : RawCovector M)
    (x a : FourSpace) :
    coefficientsToCovector (c.liftedCovector eta x) a = eta (c.lift x) (c.tangentMap x a) := by
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L a)
    (coefficientsToCovector_recover ((eta (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap))

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

lemma inverse_frame_contDiffAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (k : ℕ) :
    ContDiffAt ℝ k (fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse) x := by
  have hi := contDiffAt_map_inverse (𝕜 := ℝ) (n := (k : ℕ∞ω)) (frame c d x hd)
  rw [frame_eq_fderiv c d x hx hd] at hi
  exact hi.comp x ((coord_smoothAt c d x hx hd).fderiv_right (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))

lemma covector_eval_contDiff (k : ℕ) :
    ContDiff ℝ k (fun q : (Fin 4 → ℝ) × FourSpace => coefficientsToCovector q.1 q.2) := by
  simp only [coefficientsToCovector, sum_apply,
    smul_apply, smul_eq_mul, coordProj]
  fun_prop

lemma contDiffAt_of_coord_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (k : ℕ) (f : FourSpace → E)
    (hf : ContDiffAt ℝ k (f ∘ (chartAt FourSpace d) ∘ c.lift) x) :
    ContDiffAt ℝ k f (chartAt FourSpace d (c.lift x)) := by
  let g := (chartAt FourSpace d) ∘ c.lift
  have hg : ContDiffAt ℝ ∞ g x := coord_smoothAt c d x hx hd
  have hgd : HasFDerivAt g (frame c d x hd).toContinuousLinearMap x := by
    rw [frame_eq_fderiv c d x hx hd]
    exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let gi := hg.localInverse hgd hn
  have hgi : ContDiffAt ℝ k gi (g x) := (hg.to_localInverse hgd hn).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hleft : gi (g x) = x := hg.localInverse_apply_image hgd hn
  have hright : ∀ᶠ y in 𝓝 (g x), g (gi y) = y :=
    (hg.hasStrictFDerivAt' hgd hn).eventually_right_inverse
  have hcomp : ContDiffAt ℝ k ((f ∘ g) ∘ gi) (g x) := by
    apply ContDiffAt.comp (g x) _ hgi
    simpa only [hleft] using hf
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hright] with y hy
  simp only [Function.comp_apply, hy]

lemma vector_coord_lift_contDiffAt (c : LocalCoverChart F) (Y : RawVector M) (d : M)
    (k : ℕ) (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hY : ContDiffOn ℝ k (c.liftedVector Y) c.innerDomain) :
    ContDiffAt ℝ k (vectorInChart Y d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hY.contDiffAt (c.innerOpen.mem_nhds hx)
  have hderiv := (coord_smoothAt c d x hxo hd).fderiv_right (m := (k : ℕ∞ω)) (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤))
  have hlocal := hderiv.clm_apply hcoeff
  apply contDiffAt_of_coord_lift c d x hxo hd k
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact vector_coord_lift c Y d y hy hyd

lemma covector_coord_lift_contDiffAt (c : LocalCoverChart F) (eta : RawCovector M) (d : M)
    (k : ℕ) (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (heta : ContDiffOn ℝ k (c.liftedCovector eta) c.innerDomain) :
    ContDiffAt ℝ k (covectorInChart eta d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := heta.contDiffAt (c.innerOpen.mem_nhds hx)
  have hinv := inverse_frame_contDiffAt c d x hxo hd k
  apply contDiffAt_of_coord_lift c d x hxo hd k
  apply contDiffAt_pi.mpr
  intro i
  have hlocal := (covector_eval_contDiff k).contDiffAt.comp x
    (hcoeff.prodMk (hinv.clm_apply (contDiffAt_const (c := basisVector i))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact covector_coord_lift c eta d y hy hyd i


theorem vectorContDiff_of_lifted_contDiff (C : BoundedLocalCover M) (k : ℕ) (Y : RawVector M)
    (hY : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector Y) (C.chart ν).innerDomain) :
    VectorContDiff k Y := by
  intro d z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := vector_coord_lift_contDiffAt (C.chart ν) Y d k x hx hd (hY ν)
  rw [hchart] at h
  exact h.contDiffWithinAt

theorem covectorContDiff_of_lifted_contDiff (C : BoundedLocalCover M) (k : ℕ) (eta : RawCovector M)
    (heta : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector eta) (C.chart ν).innerDomain) :
    CovectorContDiff k eta := by
  intro d z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := covector_coord_lift_contDiffAt (C.chart ν) eta d k x hx hd (heta ν)
  rw [hchart] at h
  exact h.contDiffWithinAt

end K24.Global.NativeRegularity

open K24.Global

theorem NativeFoundation_solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0),
      (∀ eta : RawCovector M, C.CovectorHolder k α eta → CovectorContDiff k eta) ∧
      (∀ Y : RawVector M, C.VectorHolder k α Y → VectorContDiff k Y) := by
  intro M _ _ _ C k α
  constructor
  · intro eta heta
    exact NativeRegularity.covectorContDiff_of_lifted_contDiff C k eta heta.1
  · intro Y hY
    exact NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1

theorem K24NATIVE_exact_type_wrapper :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0),
      (∀ eta : RawCovector M, C.CovectorHolder k α eta → CovectorContDiff k eta) ∧
      (∀ Y : RawVector M, C.VectorHolder k α Y → VectorContDiff k Y) := NativeFoundation_solution


-- END NativeFoundation



-- BEGIN OuterRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter IsManifold
open scoped Manifold ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

/-- Native differentiability propagates to the entire actual covering chart.
No bound for the section on that larger chart is assumed. -/
theorem liftedVector_contDiffOn_outer (c : LocalCoverChart F) (k : ℕ)
    (Y : RawVector M) (hY : VectorContDiff k Y) :
    ContDiffOn ℝ k (c.liftedVector Y) c.outerDomain := by
  intro x hx
  let d := c.lift x
  have hd : c.lift x ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hs := NativeRegularity.coord_smoothAt c d x hx hd
  have hn := (hY d).contDiffAt
    ((chartAt FourSpace d).open_target.mem_nhds ((chartAt FourSpace d).map_source hd))
  have hinv := NativeRegularity.inverse_frame_contDiffAt c d x hx hd k
  have hh := hinv.clm_apply (hn.comp x (hs.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))))
  apply ContDiffAt.contDiffWithinAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hx,
    (NativeRegularity.lift_smoothAt c x hx).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  change c.liftedVector Y y =
    (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse
      (vectorInChart Y d (chartAt FourSpace d (c.lift y)))
  rw [NativeRegularity.vector_coord_lift c Y d y hy hyd,
    ← NativeRegularity.frame_eq_fderiv c d y hy hyd,
    ContinuousLinearMap.inverse_equiv]
  exact ((NativeRegularity.frame c d y hyd).symm_apply_apply _).symm

/-- An original finite-order vector Hölder section has native regularity on
every outer chart. This conclusion does not assert an outer Hölder norm bound. -/
theorem vectorHolder_outer_contDiff (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (Y : RawVector M) (hY : C.VectorHolder k alpha Y) (nu : C.Index) :
    ContDiffOn ℝ k ((C.chart nu).liftedVector Y) (C.chart nu).outerDomain :=
  liftedVector_contDiffOn_outer (C.chart nu) k Y
    (NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1)

theorem liftedCovector_eq_native (c : LocalCoverChart F) (eta : RawCovector M)
    (d : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    c.liftedCovector eta x i =
      coefficientsToCovector (covectorInChart eta d (chartAt FourSpace d (c.lift x)))
        (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (basisVector i)) := by
  rw [← NativeRegularity.frame_eq_fderiv c d x hx hd,
    ContinuousLinearEquiv.coe_coe, NativeRegularity.frame_apply]
  exact (congrArg (fun L => L (c.tangentMap x (basisVector i)))
    (covector_chart_recovery eta d (c.lift x) hd)).symm

/-- Native covector regularity on every actual outer chart. -/
theorem liftedCovector_contDiffOn_outer (c : LocalCoverChart F) (k : ℕ)
    (eta : RawCovector M) (heta : CovectorContDiff k eta) :
    ContDiffOn ℝ k (c.liftedCovector eta) c.outerDomain := by
  intro x hx
  let d := c.lift x
  have hd : c.lift x ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hs := NativeRegularity.coord_smoothAt c d x hx hd
  have hn := (heta d).contDiffAt
    ((chartAt FourSpace d).open_target.mem_nhds ((chartAt FourSpace d).map_source hd))
  have hc := hn.comp x (hs.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  have hderiv := hs.fderiv_right (m := (k : ℕ∞ω))
    (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤))
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  have hh := (NativeRegularity.covector_eval_contDiff k).contDiffAt.comp x
    (hc.prodMk (hderiv.clm_apply (contDiffAt_const (c := basisVector i))))
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hx,
    (NativeRegularity.lift_smoothAt c x hx).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact liftedCovector_eq_native c eta d y hy hyd i

theorem covectorHolder_outer_contDiff (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (eta : RawCovector M) (heta : C.CovectorHolder k alpha eta) (nu : C.Index) :
    ContDiffOn ℝ k ((C.chart nu).liftedCovector eta) (C.chart nu).outerDomain :=
  liftedCovector_contDiffOn_outer (C.chart nu) k eta
    (NativeRegularity.covectorContDiff_of_lifted_contDiff C k eta heta.1)

theorem liftedCov2_eq_native (c : LocalCoverChart F) (u : RawCov2 M)
    (d : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    c.liftedCov2 u x i j =
      matrixToBilinear (cov2InChart u d (chartAt FourSpace d (c.lift x)))
        (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (basisVector i))
        (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (basisVector j)) := by
  rw [← NativeRegularity.frame_eq_fderiv c d x hx hd,
    ContinuousLinearEquiv.coe_coe, NativeRegularity.frame_apply,
    NativeRegularity.frame_apply]
  exact (congrArg (fun L => L (c.tangentMap x (basisVector i))
    (c.tangentMap x (basisVector j)))
    (cov2_chart_recovery u d (c.lift x) hd)).symm

theorem matrix_eval_contDiff (k : ℕ) :
    ContDiff ℝ k (fun q : Mat4 × (FourSpace × FourSpace) =>
      matrixToBilinear q.1 q.2.1 q.2.2) := by
  simp only [matrixToBilinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, coordProj]
  fun_prop

/-- Native covariant tensor regularity on every actual outer chart. -/
theorem liftedCov2_contDiffOn_outer (c : LocalCoverChart F) (k : ℕ)
    (u : RawCov2 M) (hu : Cov2ContDiff k u) :
    ContDiffOn ℝ k (c.liftedCov2 u) c.outerDomain := by
  intro x hx
  let d := c.lift x
  have hd : c.lift x ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hs := NativeRegularity.coord_smoothAt c d x hx hd
  have hn := (hu d).contDiffAt
    ((chartAt FourSpace d).open_target.mem_nhds ((chartAt FourSpace d).map_source hd))
  have hc := hn.comp x (hs.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  have hderiv := hs.fderiv_right (m := (k : ℕ∞ω))
    (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤))
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hh := (matrix_eval_contDiff k).contDiffAt.comp x
    (hc.prodMk ((hderiv.clm_apply (contDiffAt_const (c := basisVector i))).prodMk
      (hderiv.clm_apply (contDiffAt_const (c := basisVector j)))))
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hx,
    (NativeRegularity.lift_smoothAt c x hx).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact liftedCov2_eq_native c u d y hy hyd i j

end K24.Global.Holder20261026Operators


-- END OuterRegularity

-- BEGIN TensorDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter IsManifold
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal

namespace K24.Global.Holder20261026Operators.TensorDescent
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

private theorem cov2_eval_contDiff (k : ℕ) :
    ContDiff ℝ k (fun q : Mat4 × FourSpace × FourSpace =>
      matrixToBilinear q.1 q.2.1 q.2.2) := by
  simp only [matrixToBilinear, sum_apply, smul_apply, smul_eq_mul, coordProj]
  fun_prop

/-- Tensor coefficient regularity descends through the genuine local-cover frame. -/
theorem cov2_coord_lift_contDiffAt (c : LocalCoverChart F) (u : RawCov2 M) (d : M)
    (k : ℕ) (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hu : ContDiffOn ℝ k (c.liftedCov2 u) c.innerDomain) :
    ContDiffAt ℝ k (cov2InChart u d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hu.contDiffAt (c.innerOpen.mem_nhds hx)
  have hinv := NativeRegularity.inverse_frame_contDiffAt c d x hxo hd k
  apply NativeRegularity.contDiffAt_of_coord_lift c d x hxo hd k
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hlocal := (cov2_eval_contDiff k).contDiffAt.comp x
    (hcoeff.prodMk ((hinv.clm_apply (contDiffAt_const (c := basisVector i))).prodMk
      (hinv.clm_apply (contDiffAt_const (c := basisVector j)))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (NativeRegularity.lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact CoverContinuity.cov2_coord_lift c u d y hy hyd i j

/-- All finite tensor regularity orders on the covering charts descend to native sections. -/
theorem cov2ContDiff_of_lifted_contDiff (C : BoundedLocalCover M) (k : ℕ) (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain) :
    Cov2ContDiff k u := by
  intro d z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := cov2_coord_lift_contDiffAt (C.chart ν) u d k x hx hd (hu ν)
  rw [hchart] at h
  exact h.contDiffWithinAt

theorem cov2Holder_native (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) : Cov2ContDiff k u :=
  cov2ContDiff_of_lifted_contDiff C k u hu.1

/-- Admissibility supplies native regularity at every order allowed by its fixed numerics. -/
theorem metricAdmissible_native (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g : RawCov2 M) (hg : MetricAdmissible C b g) (k : ℕ) (hk : k ≤ b.order) :
    Cov2ContDiff k g := by
  apply cov2ContDiff_of_lifted_contDiff C k g
  intro ν
  apply ((hg.regularity ν).1.of_le (by exact_mod_cast hk)).mono
  intro x hx
  exact (C.chart ν).closureInnerSubset (subset_closure hx)

theorem metricAdmissible_native_two (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g : RawCov2 M) (hg : MetricAdmissible C b g) : Cov2ContDiff 2 g :=
  metricAdmissible_native C b g hg 2 b.order_ge_two

end K24.Global.Holder20261026Operators.TensorDescent

-- END TensorDescent

-- BEGIN LowerFiniteness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Lower

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Derivatives below the available order are Lipschitz on a compact subset
of the open regularity domain; the compact subset need not be convex. -/
theorem lower_jet_lipschitz_compact (m j : ℕ) (hjm : j < m)
    {s t : Set E} (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t)
    (f : E → V) (hf : ContDiffOn ℝ m f t) :
    ∃ L : ℝ≥0, LipschitzOnWith L (iteratedFDeriv ℝ j f) s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs
  intro x hx
  have hc : ContDiffAt ℝ 1 (iteratedFDeriv ℝ j f) x :=
    (hf.contDiffAt (ht.mem_nhds (hst hx))).iteratedFDeriv_right (by exact_mod_cast (show 1+j ≤ m by omega))
  obtain ⟨L,u,hu,hL⟩ := hc.exists_lipschitzOnWith
  exact ⟨L,u,mem_nhdsWithin_of_mem_nhds hu,hL⟩

/-- The literal coordinate norm of a lower derivative order is finite on an
open precompact inner set. No convexity or section outer norm is assumed. -/
theorem coordinate_lower_finite (m j : ℕ) (hjm : j < m) (alpha : ℝ≥0)
    (ha : alpha ≤ 1) {s t : Set E} (hs : IsOpen s) (ht : IsOpen t)
    (hc : IsCompact (closure s)) (hst : closure s ⊆ t)
    (f : E → V) (hf : ContDiffOn ℝ m f t) :
    coordinateHolderENorm j alpha s f < ⊤ := by
  have hcont (i : ℕ) (hi : i ≤ m) : ContinuousOn (iteratedFDeriv ℝ i f) (closure s) := by
    intro x hx
    exact ((hf.contDiffAt (ht.mem_nhds (hst hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast hi)).continuousWithinAt
  have hjet (i : ℕ) (hi : i ≤ m) : derivativeENorm i s f < ⊤ := by
    obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (hcont i hi)
    apply lt_of_le_of_lt (b := ENNReal.ofReal B) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro x
    change ‖iteratedFDerivWithin ℝ i f s x‖ₑ ≤ _
    rw [iteratedFDerivWithin_of_isOpen i hs x.property, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB x (subset_closure x.property))
  obtain ⟨L,hL⟩ := lower_jet_lipschitz_compact m j hjm hc ht hst f hf
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (hcont j hjm.le)
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hb (x : s) : ‖iteratedFDeriv ℝ j f x‖ ≤ Bn :=
    (hB x (subset_closure x.property)).trans (le_max_left _ _)
  have hz : HolderWith (2*Bn) 0 (fun x : s => iteratedFDeriv ℝ j f x) := by
    intro x y
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [hb x,hb y])
  have hl : LipschitzWith L (fun x : s => iteratedFDeriv ℝ j f x) := by
    intro x y
    exact hL (subset_closure x.property) (subset_closure y.property)
  have hh := hz.of_le_of_le hl.holderWith (bot_le : 0 ≤ alpha) ha
  have hh' : eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ j f s x) < ⊤ := by
    have heq : (fun x : s => iteratedFDerivWithin ℝ j f s x) =
        (fun x : s => iteratedFDeriv ℝ j f x) := by
      funext x
      exact iteratedFDerivWithin_of_isOpen j hs x.property
    rw [heq]
    exact hh.memHolder.eHolderNorm_lt_top
  apply ENNReal.add_lt_top.mpr
  refine ⟨?_,hh'⟩
  exact ENNReal.sum_lt_top.mpr fun i hi => hjet i (by have := Finset.mem_range.mp hi; omega)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M]

/-- Natural and shifted lower-vector Hölder membership on the ORIGINAL cover
and the ORIGINAL coordinate norm. The constant obtained by compactness is not
asserted uniform over covers. -/
theorem vectorHolder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (Y : RawVector M)
    (hY : C.VectorHolder m alpha Y) : C.VectorHolder j alpha Y := by
  rcases eq_or_lt_of_le hjm with rfl | hjm
  · exact hY
  refine ⟨fun nu => (hY.1 nu).of_le (by exact_mod_cast hjm.le), ?_⟩
  apply (vectorENorm_lt_top_iff C j alpha Y).mpr
  intro nu
  exact coordinate_lower_finite m j hjm alpha ha (C.chart nu).innerOpen
    (C.chart nu).outerOpen (C.chart nu).innerCompactClosure
    (C.chart nu).closureInnerSubset _
    (Holder20261026Operators.vectorHolder_outer_contDiff C m alpha Y hY nu)

/-- The same exact-norm lower-order membership for actual covectors. -/
theorem covectorHolder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCovector M)
    (hu : C.CovectorHolder m alpha u) : C.CovectorHolder j alpha u := by
  rcases eq_or_lt_of_le hjm with rfl | hjm
  · exact hu
  refine ⟨fun nu => (hu.1 nu).of_le (by exact_mod_cast hjm.le), ?_⟩
  apply (covectorENorm_lt_top_iff C j alpha u).mpr
  intro nu
  exact coordinate_lower_finite m j hjm alpha ha (C.chart nu).innerOpen
    (C.chart nu).outerOpen (C.chart nu).innerCompactClosure
    (C.chart nu).closureInnerSubset _
    (Holder20261026Operators.covectorHolder_outer_contDiff C m alpha u hu nu)

/-- Generic tensor membership from native regularity; the public original
Holder premise will be connected once native tensor descent is available. -/
theorem cov2Holder_lower_of_native (C : BoundedLocalCover M) (m j : ℕ) (hjm : j < m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCov2 M)
    (hu : Cov2ContDiff m u) : C.Cov2Holder j alpha u := by
  have hreg (nu : C.Index) :=
    Holder20261026Operators.liftedCov2_contDiffOn_outer (C.chart nu) m u hu
  refine ⟨fun nu => ((hreg nu).mono (fun _ hx =>
    (C.chart nu).closureInnerSubset (subset_closure hx))).of_le
      (by exact_mod_cast hjm.le), ?_⟩
  apply (cov2ENorm_lt_top_iff C j alpha u).mpr
  intro nu
  exact coordinate_lower_finite m j hjm alpha ha (C.chart nu).innerOpen
    (C.chart nu).outerOpen (C.chart nu).innerCompactClosure
    (C.chart nu).closureInnerSubset _ (hreg nu)

/-- Original two-tensor Hölder membership descends in order on the same cover. -/
theorem cov2Holder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCov2 M)
    (hu : C.Cov2Holder m alpha u) : C.Cov2Holder j alpha u := by
  rcases eq_or_lt_of_le hjm with rfl | hjm
  · exact hu
  exact cov2Holder_lower_of_native C m j hjm alpha ha u
    (Holder20261026Operators.TensorDescent.cov2Holder_native C m alpha u hu)



end K24.Global.Holder20261026Lower

-- END LowerFiniteness



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology

namespace K24.Global.Holder20261026Operators

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

theorem exists_scalarBoundedLinearMap {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    {U : Set Z} {nz : Z → ℝ≥0∞} (hU : SectionBanachSpace U nz)
    (L : hU.submodule →ₗ[ℝ] ℝ) (D : ℝ≥0)
    (hb : ∀ u : hU.submodule, ‖L u‖ₑ ≤ (D : ℝ≥0∞) * nz u) :
    letI := hU.normedAddCommGroup
    letI := hU.normedSpace
    ∃ LC : hU.submodule →L[ℝ] ℝ, ∀ u, LC u = L u := by
  letI := hU.normedAddCommGroup
  letI := hU.normedSpace
  refine ⟨L.mkContinuous D (fun u => ?_), fun _ => rfl⟩
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hU.finite u u.property).ne) (hb u)
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_mul, ENNReal.coe_toReal, hU.norm_eq_toReal] using h

/-- A point-separating family of scalar observations suffices for the closed
graph theorem. The source and target are the original section submodules. -/
theorem sectionBoundedOn_of_scalar_observations
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    (A : X → Y) (hAT : Set.MapsTo A S T) (hAL : SectionLinearOn S A)
    {I : Type*} (eval : I → Y →ₗ[ℝ] ℝ)
    (hsep : ∀ v w : Y, (∀ i, eval i v = eval i w) → v = w)
    (hsource : ∀ i, SectionBoundedOn S nx (fun r : ℝ => ‖r‖ₑ) (fun u => eval i (A u)))
    (htarget : ∀ i, SectionBoundedOn T ny (fun r : ℝ => ‖r‖ₑ) (eval i)) :
    SectionBoundedOn S nx ny A := by
  letI := hS.normedAddCommGroup
  letI := hS.normedSpace
  letI := hS.completeSpace
  letI := hT.normedAddCommGroup
  letI := hT.normedSpace
  letI := hT.completeSpace
  let a : hS.submodule →ₗ[ℝ] hT.submodule :=
    { toFun := fun u => ⟨A u, hAT u.property⟩
      map_add' := fun u v => Subtype.ext (hAL.2.1 u u.property v v.property)
      map_smul' := fun c u => Subtype.ext (hAL.2.2 c u u.property) }
  have hs (i : I) : ∃ L : hS.submodule →L[ℝ] ℝ,
      ∀ u, L u = eval i (A u) := by
    obtain ⟨D, hD⟩ := hsource i
    let L := (eval i).comp (hT.submodule.subtype.comp a)
    exact exists_scalarBoundedLinearMap (nz := nx) hS L D (fun u => by
      change ‖eval i (A (u : X))‖ₑ ≤ (D : ℝ≥0∞) * nx u
      exact hD u u.property)
  have ht (i : I) : ∃ L : hT.submodule →L[ℝ] ℝ,
      ∀ u, L u = eval i u := by
    obtain ⟨D, hD⟩ := htarget i
    exact exists_scalarBoundedLinearMap (nz := ny) hT ((eval i).comp hT.submodule.subtype) D
      (fun u => by
        change ‖eval i (u : Y)‖ₑ ≤ (D : ℝ≥0∞) * ny u
        exact hD u u.property)
  have hc : Continuous a := by
    apply a.continuous_of_seq_closed_graph
    intro f u v hf hfa
    apply Subtype.ext
    apply hsep
    intro i
    obtain ⟨LS, hLS⟩ := hs i
    obtain ⟨LT, hLT⟩ := ht i
    have hsconv := LS.continuous.continuousAt.tendsto.comp hf
    have htconv := LT.continuous.continuousAt.tendsto.comp hfa
    have heq : (LT ∘ (a ∘ f)) = (LS ∘ f) := by
      funext n
      simp only [Function.comp_apply, hLS, hLT]
      rfl
    rw [heq] at htconv
    have he := tendsto_nhds_unique htconv hsconv
    change eval i (v : Y) = eval i (A u)
    simpa only [hLS, hLT] using he
  let ac : hS.submodule →L[ℝ] hT.submodule := ⟨a, hc⟩
  refine ⟨‖ac‖₊, fun u hu => ?_⟩
  have hb := ac.le_opNorm (⟨u, hu⟩ : hS.submodule)
  have hb' := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (norm_nonneg _), hT.ofReal_norm, hS.ofReal_norm] at hb'
  change ny (A u) ≤ ENNReal.ofReal ‖ac‖ * nx u at hb'
  simpa only [ofReal_norm, enorm_eq_nnnorm] using hb'

end K24.Global.Holder20261026Operators



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators

theorem scalarBoundedOn_of_continuousLinearMap
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {S : Set X} {nx : X → ℝ≥0∞} (hS : SectionBanachSpace S nx)
    (A : X → ℝ)
    (he : letI := hS.normedAddCommGroup
      letI := hS.normedSpace
      ∃ L : hS.submodule →L[ℝ] ℝ, ∀ u, L u = A u) :
    SectionBoundedOn S nx (fun r : ℝ => ‖r‖ₑ) A := by
  letI := hS.normedAddCommGroup
  letI := hS.normedSpace
  obtain ⟨L, hL⟩ := he
  refine ⟨‖L‖₊, fun u hu => ?_⟩
  have hb := ENNReal.ofReal_le_ofReal (L.le_opNorm (⟨u, hu⟩ : hS.submodule))
  rw [ENNReal.ofReal_mul (norm_nonneg _), hS.ofReal_norm] at hb
  simpa only [hL, ofReal_norm, enorm_eq_nnnorm] using hb

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def covectorEvaluation (q : Σ p : M, TangentSpace I4 p) : RawCovector M →ₗ[ℝ] ℝ where
  toFun u := u q.1 q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorEvaluation (q : Σ p : M, TangentSpace I4 p →L[ℝ] ℝ) : RawVector M →ₗ[ℝ] ℝ where
  toFun u := q.2 (u q.1)
  map_add' u v := map_add q.2 _ _
  map_smul' a u := map_smul q.2 a _

def tensorEvaluation (q : Σ p : M, TangentSpace I4 p × TangentSpace I4 p) :
    RawCov2 M →ₗ[ℝ] ℝ where
  toFun u := u q.1 q.2.1 q.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem covectorEvaluation_bounded (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (q : Σ p : M, TangentSpace I4 p) :
    SectionBoundedOn {u : RawCovector M | C.CovectorHolder k alpha u}
      (C.covectorENorm k alpha) (fun r : ℝ => ‖r‖ₑ) (covectorEvaluation q) := by
  apply scalarBoundedOn_of_continuousLinearMap (covectorHolder_sectionBanach C k alpha)
  exact HolderPerpAll.exists_covectorEvaluation C k alpha q.1 q.2

theorem vectorEvaluation_bounded (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (q : Σ p : M, TangentSpace I4 p →L[ℝ] ℝ) :
    SectionBoundedOn {u : RawVector M | C.VectorHolder k alpha u}
      (C.vectorENorm k alpha) (fun r : ℝ => ‖r‖ₑ) (vectorEvaluation q) := by
  apply scalarBoundedOn_of_continuousLinearMap (vectorHolder_sectionBanach C k alpha)
  exact HolderPerpAll.exists_vectorEvaluation C k alpha q.1 q.2

theorem tensorEvaluation_bounded (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (q : Σ p : M, TangentSpace I4 p × TangentSpace I4 p) :
    SectionBoundedOn (tensorHolderSpace C k alpha)
      (C.cov2ENorm k alpha) (fun r : ℝ => ‖r‖ₑ) (tensorEvaluation q) := by
  apply scalarBoundedOn_of_continuousLinearMap (tensorHolderSpace_sectionBanach C k alpha)
  exact HolderPerpAll.exists_cov2Evaluation C k alpha q.1 q.2.1 q.2.2

variable [IsManifold I4 ∞ M] [CompactSpace M]

/-- The actual vector Hölder inclusion has a finite norm bound for fixed data.
The constant is not claimed to depend only on the numerical cover parameters. -/
theorem vectorHolder_lower_bounded (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    SectionBoundedOn {Y : RawVector M | C.VectorHolder m alpha Y}
      (C.vectorENorm m alpha) (C.vectorENorm j alpha) id := by
  apply sectionBoundedOn_of_scalar_observations
    (vectorHolder_sectionBanach C m alpha) (vectorHolder_sectionBanach C j alpha)
    id (fun Y hY => Holder20261026Lower.vectorHolder_lower C m j hjm alpha ha Y hY)
    ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩ vectorEvaluation
  · intro v w h
    funext p
    letI : NormedAddCommGroup (TangentSpace I4 p) := inferInstanceAs (NormedAddCommGroup FourSpace)
    letI : NormedSpace ℝ (TangentSpace I4 p) := inferInstanceAs (NormedSpace ℝ FourSpace)
    apply sub_eq_zero.mp
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
    intro ell
    rw [map_sub]
    exact sub_eq_zero.mpr (h ⟨p, ell⟩)
  · exact vectorEvaluation_bounded C m alpha
  · exact vectorEvaluation_bounded C j alpha

theorem covectorHolder_lower_bounded (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    SectionBoundedOn {u : RawCovector M | C.CovectorHolder m alpha u}
      (C.covectorENorm m alpha) (C.covectorENorm j alpha) id := by
  apply sectionBoundedOn_of_scalar_observations
    (covectorHolder_sectionBanach C m alpha) (covectorHolder_sectionBanach C j alpha)
    id (fun u hu => Holder20261026Lower.covectorHolder_lower C m j hjm alpha ha u hu)
    ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩ covectorEvaluation
  · intro v w h
    ext p a
    exact h ⟨p, a⟩
  · exact covectorEvaluation_bounded C m alpha
  · exact covectorEvaluation_bounded C j alpha

theorem tensorHolder_lower_bounded (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    SectionBoundedOn (tensorHolderSpace C m alpha)
      (C.cov2ENorm m alpha) (C.cov2ENorm j alpha) id := by
  apply sectionBoundedOn_of_scalar_observations
    (tensorHolderSpace_sectionBanach C m alpha) (tensorHolderSpace_sectionBanach C j alpha)
    id (fun u hu => ⟨hu.1, Holder20261026Lower.cov2Holder_lower C m j hjm alpha ha u hu.2⟩)
    ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩ tensorEvaluation
  · intro v w h
    ext p a b
    exact h ⟨p, a, b⟩
  · exact tensorEvaluation_bounded C m alpha
  · exact tensorEvaluation_bounded C j alpha

end K24.Global.Holder20261026Operators



set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff
namespace K24.Global.Holder20261026Operators

def FixedCoverHolderInclusions : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M]
    (C : BoundedLocalCover M) (m j : ℕ), j ≤ m →
    ∀ alpha : ℝ≥0, alpha ≤ 1 →
      (∀ Y : RawVector M, C.VectorHolder m alpha Y → C.VectorHolder j alpha Y) ∧
      (∀ eta : RawCovector M, C.CovectorHolder m alpha eta → C.CovectorHolder j alpha eta) ∧
      (∀ U : RawCov2 M, C.Cov2Holder m alpha U → C.Cov2Holder j alpha U) ∧
      SectionBoundedOn {Y : RawVector M | C.VectorHolder m alpha Y}
        (C.vectorENorm m alpha) (C.vectorENorm j alpha) id ∧
      SectionBoundedOn {eta : RawCovector M | C.CovectorHolder m alpha eta}
        (C.covectorENorm m alpha) (C.covectorENorm j alpha) id ∧
      SectionBoundedOn (tensorHolderSpace C m alpha)
        (C.cov2ENorm m alpha) (C.cov2ENorm j alpha) id

end K24.Global.Holder20261026Operators


namespace K24.Global.Holder20261026Operators

theorem fixedCoverHolderInclusions_solution : FixedCoverHolderInclusions.{u} := by
  intro M _ _ _ _ C m j hjm alpha ha
  exact ⟨fun Y hY => Holder20261026Lower.vectorHolder_lower C m j hjm alpha ha Y hY,
    fun eta heta => Holder20261026Lower.covectorHolder_lower C m j hjm alpha ha eta heta,
    fun U hU => Holder20261026Lower.cov2Holder_lower C m j hjm alpha ha U hU,
    vectorHolder_lower_bounded C m j hjm alpha ha,
    covectorHolder_lower_bounded C m j hjm alpha ha,
    tensorHolder_lower_bounded C m j hjm alpha ha⟩

end K24.Global.Holder20261026Operators


set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology Set
open scoped NNReal ENNReal ContDiff Manifold Matrix.Norms.Elementwise
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



end K24.Global.HolderProjectionZero


namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem pos_derivativeENorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (alpha : ℝ≥0) (s : Set E) (f : E → V) :
    derivativeENorm j s f ≤ coordinateHolderENorm k alpha s f := by
  have hsum : derivativeENorm j s f ≤ ∑ l ∈ Finset.range (k+1), derivativeENorm l s f :=
    Finset.single_le_sum (f := fun l => derivativeENorm l s f) (fun _ _ => bot_le)
      (show j ∈ Finset.range (k+1) from Finset.mem_range.mpr (by omega))
  exact hsum.trans le_self_add

theorem pos_jet_pos_enorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (alpha : ℝ≥0) (s : Set E) (f : E → V) (x : E) (hx : x ∈ s) :
    ‖iteratedFDerivWithin ℝ j f s x‖ₑ ≤ coordinateHolderENorm k alpha s f := by
  exact (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)) ⟨x,hx⟩).trans
    (pos_derivativeENorm_le_coordinateHolderENorm k j hj alpha s f)

theorem pos_enorm_le_coordinateHolderENorm (k : ℕ) (alpha : ℝ≥0)
    (s : Set E) (f : E → V) (x : E) (hx : x ∈ s) :
    ‖f x‖ₑ ≤ coordinateHolderENorm k alpha s f := by
  have heq : ‖iteratedFDerivWithin ℝ 0 f s x‖ₑ = ‖f x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDerivWithin_zero]
  rw [← heq]
  exact pos_jet_pos_enorm_le_coordinateHolderENorm k 0 (Nat.zero_le k) alpha s f x hx


theorem pos_coordinate_bound (k : ℕ) (alpha B D : ℝ≥0) (s : Set E) (f : E → V)
    (hjet : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDerivWithin ℝ j f s x‖ ≤ B)
    (hh : HolderWith D alpha (fun x : s => iteratedFDerivWithin ℝ k f s x)) :
    coordinateHolderENorm k alpha s f ≤ (k+1 : ℕ) * (B : ℝ≥0∞) + D := by
  unfold coordinateHolderENorm
  apply add_le_add _ hh.eHolderNorm_le
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (B : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro j hj
      apply iSup_le
      intro x
      apply ENNReal.coe_le_coe.mpr
      exact hjet j (by simpa using Finset.mem_range.mp hj) x x.property
    _ = _ := by simp

theorem pos_lipschitz_of_shrink {s t : Set E} (g : E → V) (r B : ℝ≥0)
    (hr : 0 < r) (hball : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hdiff : ∀ x ∈ t, DifferentiableAt ℝ g x)
    (hderiv : ∀ x ∈ t, ‖fderiv ℝ g x‖ ≤ B)
    (hbound : ∀ x ∈ s, ‖g x‖ ≤ B) :
    LipschitzWith (B + 2*B/r) (fun x : s => g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hr' : 0 < (r : ℝ) := hr
  have hL : (B : ℝ) ≤ (B + 2*B/r : ℝ≥0) := by
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
    exact le_add_of_nonneg_right (by positivity)
  by_cases hxy : dist (x : E) (y : E) ≤ r
  · have hs := hball (x : E) x.property
    have hx : (x : E) ∈ Metric.closedBall (x : E) r := Metric.mem_closedBall_self r.coe_nonneg
    have hy : (y : E) ∈ Metric.closedBall (x : E) r := by
      simpa only [Metric.mem_closedBall, dist_comm] using hxy
    have hb := (convex_closedBall (x : E) (r : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hdiff z (hs hz)) (fun z hz => hderiv z (hs hz)) hx hy
    rw [← dist_eq_norm] at hb
    calc
      dist (g x) (g y) = dist (g y) (g x) := dist_comm _ _
      _ ≤ (B : ℝ) * dist (y : E) (x : E) := by simpa only [← dist_eq_norm] using hb
      _ ≤ (B + 2*B/r : ℝ≥0) * dist x y := by
        simpa only [Subtype.dist_eq, dist_comm] using mul_le_mul_of_nonneg_right hL dist_nonneg
  · have hxy' : (r : ℝ) < dist (x : E) (y : E) := lt_of_not_ge hxy
    have hb : dist (g x) (g y) ≤ 2 * (B : ℝ) := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hbound x x.property,hbound y y.property])
    have hscale : 2 * (B : ℝ) ≤ (2 * (B : ℝ) / r) * dist (x : E) (y : E) := by
      have hdiv : 1 ≤ dist (x : E) (y : E) / (r : ℝ) :=
        (le_div_iff₀ hr').mpr (by simpa using hxy'.le)
      calc
        _ ≤ (2 * (B : ℝ)) * (dist (x : E) (y : E) / (r : ℝ)) :=
          le_mul_of_one_le_right (by positivity) hdiv
        _ = _ := by ring
    apply hb.trans
    calc
      _ ≤ (2 * (B : ℝ) / r) * dist (x : E) (y : E) := hscale
      _ ≤ (B + 2*B/r : ℝ≥0) * dist x y := by
        simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, Subtype.dist_eq]
        nlinarith [mul_nonneg B.coe_nonneg (dist_nonneg : 0 ≤ dist (x : E) (y : E))]

theorem pos_lower_order_bound (k m : ℕ) (hkm : k < m) (alpha : ℝ≥0)
    (ha : alpha ≤ 1) {s t : Set E} (hs : IsOpen s) (ht : IsOpen t) (hst : s ⊆ t)
    (r B : ℝ≥0) (hr : 0 < r) (hball : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (f : E → V) (hf : ContDiffOn ℝ m f t)
    (hB : coordinateHolderENorm m alpha t f ≤ (B : ℝ≥0∞)) :
    coordinateHolderENorm k alpha s f ≤
      (k+1 : ℕ) * (B : ℝ≥0∞) + (max (2*B) (B+2*B/r) : ℝ≥0) := by
  have hjt (j : ℕ) (hj : j ≤ m) (x : E) (hx : x ∈ t) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
    have h := (pos_jet_pos_enorm_le_coordinateHolderENorm m j hj alpha t f x hx).trans hB
    rw [iteratedFDerivWithin_of_isOpen j ht hx] at h
    exact ENNReal.coe_le_coe.mp h
  have hj (j : ℕ) (hj : j ≤ k) (x : E) (hx : x ∈ s) :
      ‖iteratedFDerivWithin ℝ j f s x‖ ≤ B := by
    rw [iteratedFDerivWithin_of_isOpen j hs hx]
    exact hjt j (hj.trans hkm.le) x (hst hx)
  let g := iteratedFDeriv ℝ k f
  have hd : ∀ x ∈ t, DifferentiableAt ℝ g x := by
    intro x hx
    exact (hf.contDiffAt (ht.mem_nhds hx)).differentiableAt_iteratedFDeriv (by exact_mod_cast hkm)
  have hderiv : ∀ x ∈ t, ‖fderiv ℝ g x‖ ≤ B := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    exact hjt (k+1) (by omega) x hx
  have hg : ∀ x ∈ s, ‖g x‖ ≤ B := fun x hx => hjt k hkm.le x (hst hx)
  have hl := pos_lipschitz_of_shrink g r B hr hball hd hderiv hg
  have hzero : HolderWith (2*B) 0 (fun x : s => g x) := by
    intro x y
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      simp only [NNReal.coe_mul,NNReal.coe_ofNat]
      linarith [hg x x.property,hg y y.property])
  have hh := hzero.of_le_of_le hl.holderWith (bot_le : 0 ≤ alpha) ha
  apply pos_coordinate_bound k alpha B (max (2*B) (B+2*B/r)) s f hj
  intro x y
  simpa only [iteratedFDerivWithin_of_isOpen k hs x.property,
    iteratedFDerivWithin_of_isOpen k hs y.property, g] using hh x y


end K24.Global




set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ContDiff Matrix.Norms.Elementwise

namespace K24.Global.HolderFrechet
open HolderProjectionZero

variable {D V W Z : Type*} [MetricSpace D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The product estimate uses the full, original zero-order Hölder norm. -/
theorem zeroENorm_bilinear_le (α : ℝ≥0) (B : V →ₗ[ℝ] W →ₗ[ℝ] Z)
    (K : ℝ≥0∞) (hB : ∀ v w, ‖B v w‖ₑ ≤ K * ‖v‖ₑ * ‖w‖ₑ)
    (f : D → V) (g : D → W) :
    zeroENorm α (fun x => B (f x) (g x)) ≤ K * zeroENorm α f * zeroENorm α g := by
  let sf := ⨆ x, ‖f x‖ₑ
  let sg := ⨆ x, ‖g x‖ₑ
  let hf := eHolderNorm α f
  let hg := eHolderNorm α g
  have hsup : (⨆ x, ‖B (f x) (g x)‖ₑ) ≤ K * sf * sg := by
    refine iSup_le fun x => (hB _ _).trans ?_
    exact mul_le_mul' (mul_le_mul' le_rfl (le_iSup (fun x => ‖f x‖ₑ) x))
      (le_iSup (fun x => ‖g x‖ₑ) x)
  have hhold : eHolderNorm α (fun x => B (f x) (g x)) ≤ K * sf * hg + K * hf * sg := by
    rw [eHolderNorm_eq_iSup_ratio]
    refine iSup_le fun x => iSup_le fun y => ?_
    have hd : B (f x) (g x) - B (f y) (g y) =
        B (f x) (g x - g y) + B (f x - f y) (g y) := by
      simp only [map_sub, LinearMap.sub_apply]
      abel
    have hfg := (enorm_add_le (B (f x) (g x - g y))
      (B (f x - f y) (g y))).trans (add_le_add (hB _ _) (hB _ _))
    have hfr : ‖f x - f y‖ₑ / edist x y ^ (α : ℝ) ≤ hf := by
      rw [← edist_eq_enorm_sub]
      exact (le_iSup_of_le x (le_iSup (fun y =>
        edist (f x) (f y) / edist x y ^ (α : ℝ)) y)).trans_eq
        (eHolderNorm_eq_iSup_ratio α f).symm
    have hgr : ‖g x - g y‖ₑ / edist x y ^ (α : ℝ) ≤ hg := by
      rw [← edist_eq_enorm_sub]
      exact (le_iSup_of_le x (le_iSup (fun y =>
        edist (g x) (g y) / edist x y ^ (α : ℝ)) y)).trans_eq
        (eHolderNorm_eq_iSup_ratio α g).symm
    calc
      edist (B (f x) (g x)) (B (f y) (g y)) / edist x y ^ (α : ℝ)
          ≤ (K * ‖f x‖ₑ * ‖g x - g y‖ₑ + K * ‖f x - f y‖ₑ * ‖g y‖ₑ) /
            edist x y ^ (α : ℝ) := by
              rw [edist_eq_enorm_sub, hd]
              exact ENNReal.div_le_div_right hfg _
      _ = K * ‖f x‖ₑ * (‖g x - g y‖ₑ / edist x y ^ (α : ℝ)) +
          K * (‖f x - f y‖ₑ / edist x y ^ (α : ℝ)) * ‖g y‖ₑ := by
            simp only [div_eq_mul_inv, add_mul]
            ac_rfl
      _ ≤ K * sf * hg + K * hf * sg := by
        exact add_le_add
          (mul_le_mul' (mul_le_mul' le_rfl (le_iSup (fun x => ‖f x‖ₑ) x)) hgr)
          (mul_le_mul' (mul_le_mul' le_rfl hfr) (le_iSup (fun y => ‖g y‖ₑ) y))
  calc
    zeroENorm α (fun x => B (f x) (g x)) ≤ K * sf * sg + (K * sf * hg + K * hf * sg) :=
      add_le_add hsup hhold
    _ ≤ K * sf * sg + (K * sf * hg + K * hf * sg) + K * hf * hg := le_self_add
    _ = K * zeroENorm α f * zeroENorm α g := by
      change _ = K * (sf + hf) * (sg + hg)
      ring

theorem coordinateHolderENorm_zero_bilinear_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (s : Set E) (B : V →ₗ[ℝ] W →ₗ[ℝ] Z)
    (K : ℝ≥0∞) (hB : ∀ v w, ‖B v w‖ₑ ≤ K * ‖v‖ₑ * ‖w‖ₑ)
    (f : E → V) (g : E → W) :
    coordinateHolderENorm 0 α s (fun x => B (f x) (g x)) ≤
      K * coordinateHolderENorm 0 α s f * coordinateHolderENorm 0 α s g := by
  simp only [coordinateHolderENorm_zero_eq]
  exact zeroENorm_bilinear_le α B K hB _ _

end K24.Global.HolderFrechet





set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.HolderFrechet

/-- Multiplication in the frozen elementwise matrix norm costs the dimension. -/
theorem matrix_norm_mul_le (A B : Mat4) : ‖A * B‖ ≤ 4 * ‖A‖ * ‖B‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  calc
    ‖(A * B) i j‖ = ‖∑ k : Fin 4, A i k * B k j‖ := rfl
    _ ≤ ∑ k : Fin 4, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 4, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = 4 * ‖A‖ * ‖B‖ := by simp; ring

/-- Exact second order inverse remainder; no asymptotic or commutativity assumption. -/
theorem matrix_inverse_quadratic_remainder (G H : Mat4)
    (hG : IsUnit G) (hGH : IsUnit (G + H)) :
    (G + H)⁻¹ - G⁻¹ + G⁻¹ * H * G⁻¹ =
      G⁻¹ * H * G⁻¹ * H * (G + H)⁻¹ := by
  have hdiff : G⁻¹ - (G + H)⁻¹ = G⁻¹ * H * (G + H)⁻¹ := by
    simpa only [add_sub_cancel_left] using
      (Matrix.inv_sub_inv (A := G) (B := G + H) ⟨fun _ => hGH, fun _ => hG⟩)
  calc
    (G + H)⁻¹ - G⁻¹ + G⁻¹ * H * G⁻¹ =
        G⁻¹ * H * G⁻¹ - G⁻¹ * H * (G + H)⁻¹ := by rw [← hdiff]; abel
    _ = G⁻¹ * H * (G⁻¹ - (G + H)⁻¹) := by rw [mul_sub]
    _ = G⁻¹ * H * (G⁻¹ * H * (G + H)⁻¹) := by rw [hdiff]
    _ = G⁻¹ * H * G⁻¹ * H * (G + H)⁻¹ := by simp only [mul_assoc]

/-- The exact remainder estimate uses the original elementwise norm. -/
theorem matrix_inverse_quadratic_remainder_norm_le (G H : Mat4)
    (hG : IsUnit G) (hGH : IsUnit (G + H)) :
    ‖(G + H)⁻¹ - G⁻¹ + G⁻¹ * H * G⁻¹‖ ≤
      256 * ‖G⁻¹‖ ^ 2 * ‖(G + H)⁻¹‖ * ‖H‖ ^ 2 := by
  rw [matrix_inverse_quadratic_remainder G H hG hGH]
  calc
    ‖G⁻¹ * H * G⁻¹ * H * (G + H)⁻¹‖ ≤
        4 * (4 * (4 * (4 * ‖G⁻¹‖ * ‖H‖) * ‖G⁻¹‖) * ‖H‖) * ‖(G + H)⁻¹‖ := by
      apply (matrix_norm_mul_le _ _).trans
      gcongr
      apply (matrix_norm_mul_le _ _).trans
      gcongr
      apply (matrix_norm_mul_le _ _).trans
      gcongr
      exact matrix_norm_mul_le _ _
    _ = 256 * ‖G⁻¹‖ ^ 2 * ‖(G + H)⁻¹‖ * ‖H‖ ^ 2 := by ring

/-- Resolvent estimate in the frozen elementwise norm. -/
theorem matrix_inverse_difference_norm_le (G K : Mat4)
    (hG : IsUnit G) (hK : IsUnit K) :
    ‖G⁻¹ - K⁻¹‖ ≤ 16 * ‖G⁻¹‖ * ‖K⁻¹‖ * ‖K - G‖ := by
  rw [Matrix.inv_sub_inv ⟨fun _ => hK, fun _ => hG⟩]
  calc
    ‖G⁻¹ * (K - G) * K⁻¹‖ ≤ 4 * (4 * ‖G⁻¹‖ * ‖K - G‖) * ‖K⁻¹‖ := by
      apply (matrix_norm_mul_le _ _).trans
      gcongr
      exact matrix_norm_mul_le _ _
    _ = 16 * ‖G⁻¹‖ * ‖K⁻¹‖ * ‖K - G‖ := by ring

/-- Positivity supplies invertibility of the perturbed metric; smallness alone
then gives its inverse bound without changing matrix norms. -/
theorem matrix_perturbed_inverse_norm_le (G H : Mat4)
    (hG : IsUnit G) (hGH : IsUnit (G + H))
    (hsmall : 32 * ‖G⁻¹‖ * ‖H‖ ≤ 1) :
    ‖(G + H)⁻¹‖ ≤ 2 * ‖G⁻¹‖ := by
  have hd := matrix_inverse_difference_norm_le G (G + H) hG hGH
  simp only [add_sub_cancel_left] at hd
  have hq : ‖(G + H)⁻¹‖ ≤ ‖G⁻¹‖ + 16 * ‖G⁻¹‖ * ‖H‖ * ‖(G + H)⁻¹‖ := by
    calc
      ‖(G + H)⁻¹‖ = ‖G⁻¹ - (G⁻¹ - (G + H)⁻¹)‖ := by congr 1; abel
      _ ≤ ‖G⁻¹‖ + ‖G⁻¹ - (G + H)⁻¹‖ := norm_sub_le _ _
      _ ≤ ‖G⁻¹‖ + 16 * ‖G⁻¹‖ * ‖(G + H)⁻¹‖ * ‖H‖ := by gcongr
      _ = ‖G⁻¹‖ + 16 * ‖G⁻¹‖ * ‖H‖ * ‖(G + H)⁻¹‖ := by ring
  have hs : 16 * ‖G⁻¹‖ * ‖H‖ ≤ (1 / 2 : ℝ) := by nlinarith [hsmall]
  have hmul := mul_le_mul_of_nonneg_right hs (norm_nonneg ((G + H)⁻¹))
  nlinarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  {F : LocalFiniteCover M}

theorem liftedCov2_add (c : LocalCoverChart F) (u v : RawCov2 M) (x : FourSpace) :
    c.liftedCov2 (u + v) x = c.liftedCov2 u x + c.liftedCov2 v x := rfl

/-- Positivity on the actual tangent fibers gives nonsingularity of every lifted matrix. -/
theorem lifted_metric_isUnit (c : LocalCoverChart F) (g : RawCov2 M)
    (hg : IsMetric g) (x : FourSpace) : IsUnit (c.liftedCov2 g x) := by
  apply Matrix.PosDef.isUnit
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · ext i j
    change c.liftedCov2 g x j i = c.liftedCov2 g x i j
    exact hg.1 _ _ _
  · intro v hv
    let V : FourSpace := ∑ i : Fin 4, v i • basisVector i
    have hV : V ≠ 0 := by
      intro h
      apply hv
      funext j
      have hj := congrArg (fun w : FourSpace => w j) h
      simpa [V, basisVector, Pi.single_apply] using hj
    have heV : c.tangentMap x V ≠ 0 := by
      simpa only [map_zero] using (c.tangentMap x).injective.ne hV
    have hp := hg.2 (c.lift x) (c.tangentMap x V) heV
    convert hp using 1 <;> try rfl
    simp [dotProduct, Matrix.mulVec, LocalCoverChart.liftedCov2, V,
      map_sum, Finset.mul_sum, mul_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg (fun t : ℝ => v a * (v b * t)) (hg.1 _ _ _)

/-- The quadratic expansion is for the actual local-cover inverse metric coefficients. -/
theorem lifted_inverse_quadratic_remainder (c : LocalCoverChart F)
    (z h : RawCov2 M) (hz : IsMetric z) (hzh : IsMetric (z + h)) (x : FourSpace) :
    c.inverseMetricCoefficients (z + h) x - c.inverseMetricCoefficients z x +
        c.inverseMetricCoefficients z x * c.liftedCov2 h x * c.inverseMetricCoefficients z x =
      c.inverseMetricCoefficients z x * c.liftedCov2 h x * c.inverseMetricCoefficients z x *
        c.liftedCov2 h x * c.inverseMetricCoefficients (z + h) x := by
  have hu : IsUnit (c.liftedCov2 z x + c.liftedCov2 h x) := by
    rw [← liftedCov2_add]
    exact lifted_metric_isUnit c (z + h) hzh x
  simpa only [LocalCoverChart.inverseMetricCoefficients, liftedCov2_add] using
    matrix_inverse_quadratic_remainder (c.liftedCov2 z x) (c.liftedCov2 h x)
      (lifted_metric_isUnit c z hz x) hu

end K24.Global.HolderFrechet





set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ContDiff Manifold Matrix.Norms.Elementwise

namespace K24.Global.HolderFrechet
open HolderProjectionZero

theorem matrix_enorm_mul_le (A B : Mat4) : ‖A * B‖ₑ ≤ 4 * ‖A‖ₑ * ‖B‖ₑ := by
  have h := ENNReal.ofReal_le_ofReal (matrix_norm_mul_le A B)
  rw [ENNReal.ofReal_mul (show 0 ≤ (4 : ℝ) * ‖A‖ by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num)] at h
  simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using h

variable {D : Type*} [MetricSpace D]

theorem zeroENorm_matrix_mul_le (α : ℝ≥0) (f g : D → Mat4) :
    zeroENorm α (fun x => f x * g x) ≤ 4 * zeroENorm α f * zeroENorm α g := by
  exact zeroENorm_bilinear_le α (LinearMap.mul ℝ Mat4) 4 matrix_enorm_mul_le f g

theorem matrix_inverse_difference_enorm_le (G K : Mat4)
    (hG : IsUnit G) (hK : IsUnit K) :
    ‖G⁻¹ - K⁻¹‖ₑ ≤ 16 * ‖G⁻¹‖ₑ * ‖K⁻¹‖ₑ * ‖K - G‖ₑ := by
  rw [Matrix.inv_sub_inv ⟨fun _ => hK, fun _ => hG⟩]
  calc
    _ ≤ 4 * (4 * ‖G⁻¹‖ₑ * ‖K - G‖ₑ) * ‖K⁻¹‖ₑ := by
      apply (matrix_enorm_mul_le _ _).trans
      gcongr
      exact matrix_enorm_mul_le _ _
    _ = _ := by ring

/-- Inverse Hölder finiteness is derived from the inverse pointwise bound;
it is not assumed as a separate regularity property of the perturbed metric. -/
theorem zeroENorm_inverse_le (α : ℝ≥0) (G : D → Mat4) (P : ℝ≥0∞)
    (hG : ∀ x, IsUnit (G x)) (hP : ∀ x, ‖(G x)⁻¹‖ₑ ≤ P) :
    zeroENorm α (fun x => (G x)⁻¹) ≤ P + 16 * P ^ 2 * eHolderNorm α G := by
  apply add_le_add (iSup_le hP)
  rw [eHolderNorm_eq_iSup_ratio]
  refine iSup_le fun x => iSup_le fun y => ?_
  have hn : ‖(G x)⁻¹ - (G y)⁻¹‖ₑ ≤ 16 * P ^ 2 * ‖G x - G y‖ₑ := by
    calc
      _ ≤ 16 * ‖(G x)⁻¹‖ₑ * ‖(G y)⁻¹‖ₑ * ‖G y - G x‖ₑ :=
        matrix_inverse_difference_enorm_le _ _ (hG x) (hG y)
      _ ≤ 16 * P * P * ‖G y - G x‖ₑ := by gcongr; exact hP x; exact hP y
      _ = _ := by rw [enorm_sub_rev]; ring
  calc
    edist ((G x)⁻¹) ((G y)⁻¹) / edist x y ^ (α : ℝ) ≤
        (16 * P ^ 2 * ‖G x - G y‖ₑ) / edist x y ^ (α : ℝ) := by
      rw [edist_eq_enorm_sub]
      exact ENNReal.div_le_div_right hn _
    _ = 16 * P ^ 2 * (edist (G x) (G y) / edist x y ^ (α : ℝ)) := by
      rw [edist_eq_enorm_sub, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    _ ≤ 16 * P ^ 2 * eHolderNorm α G := by
      gcongr
      rw [eHolderNorm_eq_iSup_ratio]
      exact le_iSup_of_le x (le_iSup (fun y =>
        edist (G x) (G y) / edist x y ^ (α : ℝ)) y)

theorem zeroENorm_inverse_add_le (α : ℝ≥0) (G H : D → Mat4) (P : ℝ≥0)
    (hG : ∀ x, IsUnit (G x)) (hGH : ∀ x, IsUnit (G x + H x))
    (hP : ∀ x, ‖(G x)⁻¹‖ ≤ (P : ℝ))
    (hsmall : ∀ x, 32 * (P : ℝ) * ‖H x‖ ≤ 1) :
    zeroENorm α (fun x => (G x + H x)⁻¹) ≤
      2 * (P : ℝ≥0∞) + 64 * (P : ℝ≥0∞) ^ 2 * (zeroENorm α G + zeroENorm α H) := by
  have hQ (x : D) : ‖(G x + H x)⁻¹‖ₑ ≤ 2 * (P : ℝ≥0∞) := by
    have hs : 32 * ‖(G x)⁻¹‖ * ‖H x‖ ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hP x) (by norm_num)) (norm_nonneg _)).trans (hsmall x)
    have hb := (matrix_perturbed_inverse_norm_le _ _ (hG x) (hGH x) hs).trans
      (mul_le_mul_of_nonneg_left (hP x) (by norm_num))
    have hb' := ENNReal.ofReal_le_ofReal hb
    simpa only [ofReal_norm, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal] using hb'
  have hh : eHolderNorm α (fun x => G x + H x) ≤ zeroENorm α G + zeroENorm α H := by
    exact eHolderNorm_add_le.trans (add_le_add le_add_self le_add_self)
  calc
    _ ≤ 2 * (P : ℝ≥0∞) + 16 * (2 * (P : ℝ≥0∞)) ^ 2 *
        eHolderNorm α (fun x => G x + H x) :=
      zeroENorm_inverse_le α (fun x => G x + H x) _ hGH hQ
    _ ≤ 2 * (P : ℝ≥0∞) + 16 * (2 * (P : ℝ≥0∞)) ^ 2 *
        (zeroENorm α G + zeroENorm α H) := by gcongr
    _ = _ := by ring

theorem zeroENorm_inverse_remainder_le (α : ℝ≥0) (G H : D → Mat4)
    (hG : ∀ x, IsUnit (G x)) (hGH : ∀ x, IsUnit (G x + H x)) :
    zeroENorm α (fun x => (G x + H x)⁻¹ - (G x)⁻¹ + (G x)⁻¹ * H x * (G x)⁻¹) ≤
      256 * (zeroENorm α (fun x => (G x)⁻¹)) ^ 2 *
        zeroENorm α (fun x => (G x + H x)⁻¹) * (zeroENorm α H) ^ 2 := by
  simp_rw [matrix_inverse_quadratic_remainder _ _ (hG _) (hGH _)]
  calc
    _ ≤ 4 * (4 * (4 * (4 * zeroENorm α (fun x => (G x)⁻¹) * zeroENorm α H) *
        zeroENorm α (fun x => (G x)⁻¹)) * zeroENorm α H) *
        zeroENorm α (fun x => (G x + H x)⁻¹) := by
      apply (zeroENorm_matrix_mul_le α _ _).trans
      gcongr
      apply (zeroENorm_matrix_mul_le α _ _).trans
      gcongr
      apply (zeroENorm_matrix_mul_le α _ _).trans
      gcongr
      exact zeroENorm_matrix_mul_le α _ _
    _ = _ := by ring

theorem coordinateHolderENorm_inverse_remainder_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (s : Set E) (G H : E → Mat4)
    (hG : ∀ x ∈ s, IsUnit (G x)) (hGH : ∀ x ∈ s, IsUnit (G x + H x)) :
    coordinateHolderENorm 0 α s
        (fun x => (G x + H x)⁻¹ - (G x)⁻¹ + (G x)⁻¹ * H x * (G x)⁻¹) ≤
      256 * (coordinateHolderENorm 0 α s (fun x => (G x)⁻¹)) ^ 2 *
        coordinateHolderENorm 0 α s (fun x => (G x + H x)⁻¹) *
          (coordinateHolderENorm 0 α s H) ^ 2 := by
  simp only [coordinateHolderENorm_zero_eq]
  exact zeroENorm_inverse_remainder_le α _ _
    (fun x => hG x x.property) (fun x => hGH x x.property)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  {F : LocalFiniteCover M}

/-- A genuine quadratic estimate for the actual local-cover inverse coefficients. -/
theorem lifted_inverse_holder_remainder_le (c : LocalCoverChart F) (s : Set FourSpace)
    (α : ℝ≥0) (z h : RawCov2 M) (hz : IsMetric z) (hzh : IsMetric (z + h)) :
    coordinateHolderENorm 0 α s (fun x =>
      c.inverseMetricCoefficients (z + h) x - c.inverseMetricCoefficients z x +
        c.inverseMetricCoefficients z x * c.liftedCov2 h x * c.inverseMetricCoefficients z x) ≤
      256 * (coordinateHolderENorm 0 α s (c.inverseMetricCoefficients z)) ^ 2 *
        coordinateHolderENorm 0 α s (c.inverseMetricCoefficients (z + h)) *
          (coordinateHolderENorm 0 α s (c.liftedCov2 h)) ^ 2 := by
  unfold LocalCoverChart.inverseMetricCoefficients
  simpa only [liftedCov2_add] using
    coordinateHolderENorm_inverse_remainder_le α s (c.liftedCov2 z) (c.liftedCov2 h)
      (fun x _ => lifted_metric_isUnit c z hz x)
      (fun x _ => by simpa only [← liftedCov2_add] using lifted_metric_isUnit c (z + h) hzh x)

end K24.Global.HolderFrechet





set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ContDiff Manifold Matrix.Norms.Elementwise

namespace K24.Global.HolderFrechet
open HolderProjectionZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- A finite uniform bound extracted from the original outer coefficient hypotheses. -/
theorem admissible_coefficient_inverse_zero_bounds (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (z : RawCov2 M) (hz : MetricAdmissible C b z) :
    ∃ B : ℝ≥0, 0 < B ∧ ∀ ν : C.Index,
      coordinateHolderENorm 0 b.exponent.value (C.chart ν).innerDomain
          ((C.chart ν).liftedCov2 z) ≤ (B : ℝ≥0∞) ∧
      coordinateHolderENorm 0 b.exponent.value (C.chart ν).innerDomain
          ((C.chart ν).inverseMetricCoefficients z) ≤ (B : ℝ≥0∞) := by
  let r : ℝ≥0 := ⟨C.numerics.shrinkRadius, C.numerics.shrinkRadius_pos.le⟩
  let D : ℝ≥0 := max (2 * b.coefficientBound)
    (b.coefficientBound + 2 * b.coefficientBound / r)
  refine ⟨b.coefficientBound + D + 1, by positivity, ?_⟩
  intro ν
  have hsub : (C.chart ν).innerDomain ⊆ (C.chart ν).outerDomain :=
    fun _ hx => (C.chart ν).closureInnerSubset (subset_closure hx)
  have helper (f : FourSpace → Mat4)
      (hf : ContDiffOn ℝ b.order f (C.chart ν).outerDomain)
      (hB : coordinateHolderENorm b.order b.exponent.value (C.chart ν).outerDomain f ≤
        (b.coefficientBound : ℝ≥0∞)) :
      coordinateHolderENorm 0 b.exponent.value (C.chart ν).innerDomain f ≤
        ((b.coefficientBound + D + 1 : ℝ≥0) : ℝ≥0∞) := by
    have hh := pos_lower_order_bound 0 b.order (by have := b.order_ge_two; omega)
      b.exponent.value b.exponent.lessThanOne.le
      (C.chart ν).innerOpen (C.chart ν).outerOpen hsub r b.coefficientBound
      C.numerics.shrinkRadius_pos
      (fun x hx => C.uniformShrink ν.1 ν.2 x (subset_closure hx)) f hf hB
    apply hh.trans
    simp only [Nat.zero_add, Nat.cast_one, one_mul, ← ENNReal.coe_add, D]
    exact ENNReal.coe_le_coe.mpr le_self_add
  exact ⟨helper _ (hz.regularity ν).1 (le_self_add.trans (hz.coefficientBound ν)),
    helper _ (hz.inverseRegularity ν).1 (le_add_self.trans (hz.coefficientBound ν))⟩

theorem lifted_inverse_add_holder_bound (C : BoundedLocalCover M) (α : ℝ≥0)
    (z h : RawCov2 M) (hz : IsMetric z) (hzh : IsMetric (z + h)) (B : ℝ≥0)
    (hB : ∀ ν : C.Index,
      coordinateHolderENorm 0 α (C.chart ν).innerDomain ((C.chart ν).liftedCov2 z) ≤
          (B : ℝ≥0∞) ∧
      coordinateHolderENorm 0 α (C.chart ν).innerDomain
          ((C.chart ν).inverseMetricCoefficients z) ≤ (B : ℝ≥0∞))
    (hsmall : 32 * (B : ℝ≥0∞) * C.cov2ENorm 2 α h ≤ 1) (ν : C.Index) :
    coordinateHolderENorm 0 α (C.chart ν).innerDomain
        ((C.chart ν).inverseMetricCoefficients (z + h)) ≤
      2 * (B : ℝ≥0∞) + 64 * (B : ℝ≥0∞) ^ 2 * ((B : ℝ≥0∞) + C.cov2ENorm 0 α h) := by
  let s := (C.chart ν).innerDomain
  let G : s → Mat4 := fun x => (C.chart ν).liftedCov2 z x
  let H : s → Mat4 := fun x => (C.chart ν).liftedCov2 h x
  have hP (x : s) : ‖(G x)⁻¹‖ ≤ (B : ℝ) := by
    have hh := (pos_enorm_le_coordinateHolderENorm 0 α s
      ((C.chart ν).inverseMetricCoefficients z) x x.property).trans (hB ν).2
    exact ENNReal.coe_le_coe.mp hh
  have hH (x : s) : ‖H x‖ₑ ≤ C.cov2ENorm 2 α h :=
    (pos_enorm_le_coordinateHolderENorm 2 α s ((C.chart ν).liftedCov2 h) x x.property).trans
      (le_iSup (fun ν : C.Index => coordinateHolderENorm 2 α (C.chart ν).innerDomain
        ((C.chart ν).liftedCov2 h)) ν)
  have hs (x : s) : 32 * (B : ℝ) * ‖H x‖ ≤ 1 := by
    have hh : (32 : ℝ≥0∞) * (B : ℝ≥0∞) * ‖H x‖ₑ ≤ 1 :=
      (mul_le_mul' le_rfl (hH x)).trans hsmall
    have heq : ENNReal.ofReal (32 * (B : ℝ) * ‖H x‖) =
        (32 : ℝ≥0∞) * (B : ℝ≥0∞) * ‖H x‖ₑ := by
      rw [ENNReal.ofReal_mul (show 0 ≤ (32 : ℝ) * B by positivity),
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ 32 by norm_num)]
      simp only [ofReal_norm, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    rw [← heq, ← ENNReal.ofReal_one] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hh
  have hi := zeroENorm_inverse_add_le α G H B
    (fun x => lifted_metric_isUnit (C.chart ν) z hz x)
    (fun x => by simpa only [G, H, ← liftedCov2_add] using
      lifted_metric_isUnit (C.chart ν) (z + h) hzh x) hP hs
  have hG : zeroENorm α G ≤ (B : ℝ≥0∞) := by
    simpa only [coordinateHolderENorm_zero_eq, G] using (hB ν).1
  have hH0 : zeroENorm α H ≤ C.cov2ENorm 0 α h := by
    simpa only [coordinateHolderENorm_zero_eq, H, BoundedLocalCover.cov2ENorm] using
      (le_iSup (fun ν : C.Index => coordinateHolderENorm 0 α (C.chart ν).innerDomain
        ((C.chart ν).liftedCov2 h)) ν)
  have hid : (fun x : s => (G x + H x)⁻¹) =
      (fun x : s => (C.chart ν).inverseMetricCoefficients (z + h) x) := rfl
  rw [hid] at hi
  rw [coordinateHolderENorm_zero_eq]
  exact hi.trans (by gcongr)

/-- The remainder is measured on exactly the original cover inner domains. -/
theorem actual_inverse_holder_remainder_bound (C : BoundedLocalCover M) (α : ℝ≥0)
    (z h : RawCov2 M) (hz : IsMetric z) (hzh : IsMetric (z + h)) (B : ℝ≥0)
    (hB : ∀ ν : C.Index,
      coordinateHolderENorm 0 α (C.chart ν).innerDomain ((C.chart ν).liftedCov2 z) ≤
          (B : ℝ≥0∞) ∧
      coordinateHolderENorm 0 α (C.chart ν).innerDomain
          ((C.chart ν).inverseMetricCoefficients z) ≤ (B : ℝ≥0∞))
    (hsmall : 32 * (B : ℝ≥0∞) * C.cov2ENorm 2 α h ≤ 1) :
    (⨆ ν : C.Index, coordinateHolderENorm 0 α (C.chart ν).innerDomain (fun x =>
      (C.chart ν).inverseMetricCoefficients (z + h) x -
        (C.chart ν).inverseMetricCoefficients z x +
        (C.chart ν).inverseMetricCoefficients z x * (C.chart ν).liftedCov2 h x *
          (C.chart ν).inverseMetricCoefficients z x)) ≤
      256 * (B : ℝ≥0∞) ^ 2 *
        (2 * (B : ℝ≥0∞) + 64 * (B : ℝ≥0∞) ^ 2 * ((B : ℝ≥0∞) + C.cov2ENorm 0 α h)) *
          (C.cov2ENorm 0 α h) ^ 2 := by
  refine iSup_le fun ν => ?_
  apply (lifted_inverse_holder_remainder_le (C.chart ν) (C.chart ν).innerDomain α z h hz hzh).trans
  have hH : coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCov2 h) ≤ C.cov2ENorm 0 α h :=
    le_iSup (fun ν : C.Index => coordinateHolderENorm 0 α (C.chart ν).innerDomain
      ((C.chart ν).liftedCov2 h)) ν
  have hQ := lifted_inverse_add_holder_bound C α z h hz hzh B hB hsmall ν
  gcongr
  exact (hB ν).2

variable [IsManifold I4 ∞ M] [CompactSpace M]

/-- The actual inverse coefficients have a quadratic remainder in the original
source `C.cov2ENorm 2 α`. The constants are permitted to depend on the fixed
cover and center, exactly as in the requested Fréchet fields. -/
theorem actual_inverse_quadratic_remainder (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (z : RawCov2 M) (hz : MetricAdmissible C b z) :
    ∃ K : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ h ∈ tensorHolderSpace C 2 b.exponent.value, IsMetric (z + h) →
        C.cov2ENorm 2 b.exponent.value h < ENNReal.ofReal δ →
        (⨆ ν : C.Index, coordinateHolderENorm 0 b.exponent.value (C.chart ν).innerDomain
          (fun x => (C.chart ν).inverseMetricCoefficients (z + h) x -
            (C.chart ν).inverseMetricCoefficients z x +
            (C.chart ν).inverseMetricCoefficients z x * (C.chart ν).liftedCov2 h x *
              (C.chart ν).inverseMetricCoefficients z x)) ≤
          (K : ℝ≥0∞) * (C.cov2ENorm 2 b.exponent.value h) ^ 2 := by
  obtain ⟨B, hBpos, hB⟩ := admissible_coefficient_inverse_zero_bounds C b z hz
  obtain ⟨D, hD⟩ := Holder20261026Operators.tensorHolder_lower_bounded C 2 0 (by omega)
    b.exponent.value b.exponent.lessThanOne.le
  let δ : ℝ≥0 := min 1 (32 * B + 1)⁻¹
  let K : ℝ≥0 := 256 * B ^ 2 * (2 * B + 64 * B ^ 2 * (B + D)) * D ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨K, δ, hδ, ?_⟩
  intro h hh hzh hnorm
  have hN : C.cov2ENorm 2 b.exponent.value h ≤ (δ : ℝ≥0∞) := by
    exact (hnorm.trans_eq (ENNReal.ofReal_coe_nnreal)).le
  have hN1 : C.cov2ENorm 2 b.exponent.value h ≤ 1 :=
    hN.trans (by exact_mod_cast (min_le_left (1 : ℝ≥0) (32 * B + 1)⁻¹))
  have h0 : C.cov2ENorm 0 b.exponent.value h ≤ (D : ℝ≥0∞) * C.cov2ENorm 2 b.exponent.value h :=
    hD h hh
  have h0D : C.cov2ENorm 0 b.exponent.value h ≤ (D : ℝ≥0∞) := by
    exact h0.trans (by simpa using mul_le_mul' (le_refl (D : ℝ≥0∞)) hN1)
  have hδsmall : 32 * B * δ ≤ 1 := by
    calc
      32 * B * δ ≤ (32 * B + 1) * (32 * B + 1)⁻¹ := by
        apply mul_le_mul
        · exact le_self_add
        · exact min_le_right _ _
        · positivity
        · positivity
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hsmall : 32 * (B : ℝ≥0∞) * C.cov2ENorm 2 b.exponent.value h ≤ 1 := by
    apply (mul_le_mul' le_rfl hN).trans
    exact_mod_cast hδsmall
  apply (actual_inverse_holder_remainder_bound C b.exponent.value z h hz.metric hzh B hB hsmall).trans
  calc
    _ ≤ 256 * (B : ℝ≥0∞) ^ 2 *
        (2 * (B : ℝ≥0∞) + 64 * (B : ℝ≥0∞) ^ 2 * ((B : ℝ≥0∞) + D)) *
          ((D : ℝ≥0∞) * C.cov2ENorm 2 b.exponent.value h) ^ 2 := by gcongr
    _ = (K : ℝ≥0∞) * (C.cov2ENorm 2 b.exponent.value h) ^ 2 := by
      simp only [K, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_pow, ENNReal.coe_ofNat]
      ring

end K24.Global.HolderFrechet





set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ContDiff Manifold Matrix.Norms.Elementwise

namespace K24.Global.HolderFrechet
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M]

/-- The inverse-metric component satisfies a true uniform epsilon remainder,
with the original C2 Hölder directions and actual positive-metric domain.
This is an ingredient for, not a replacement for, the nonlinear gauge field. -/
theorem actual_inverse_uniform_remainder (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (z : RawCov2 M) (hz : MetricAdmissible C b z) :
    ∀ eps : ℝ, 0 < eps → ∃ δ : ℝ, 0 < δ ∧
      ∀ h ∈ tensorHolderSpace C 2 b.exponent.value,
        z + h ∈ positiveHolderMetrics C 2 b.exponent.value →
        C.cov2ENorm 2 b.exponent.value h < ENNReal.ofReal δ →
        (⨆ ν : C.Index, coordinateHolderENorm 0 b.exponent.value (C.chart ν).innerDomain
          (fun x => (C.chart ν).inverseMetricCoefficients (z + h) x -
            (C.chart ν).inverseMetricCoefficients z x +
            (C.chart ν).inverseMetricCoefficients z x * (C.chart ν).liftedCov2 h x *
              (C.chart ν).inverseMetricCoefficients z x)) ≤
          ENNReal.ofReal eps * C.cov2ENorm 2 b.exponent.value h := by
  obtain ⟨K, δ₀, hδ₀, hR⟩ := actual_inverse_quadratic_remainder C b z hz
  intro eps heps
  let δ := min δ₀ (eps / ((K : ℝ) + 1))
  have hK1 : 0 < (K : ℝ) + 1 := by positivity
  refine ⟨δ, lt_min hδ₀ (div_pos heps hK1), ?_⟩
  intro h hh hzh hnorm
  have hnorm₀ : C.cov2ENorm 2 b.exponent.value h < ENNReal.ofReal δ₀ :=
    hnorm.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hnorm₁ : C.cov2ENorm 2 b.exponent.value h ≤ ENNReal.ofReal (eps / ((K : ℝ) + 1)) :=
    hnorm.le.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hscalar : (K : ℝ) * (eps / ((K : ℝ) + 1)) ≤ eps := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hK1).mpr
    nlinarith
  have hKN : (K : ℝ≥0∞) * C.cov2ENorm 2 b.exponent.value h ≤ ENNReal.ofReal eps := by
    apply (mul_le_mul' le_rfl hnorm₁).trans
    have hs := ENNReal.ofReal_le_ofReal hscalar
    simpa only [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hs
  calc
    _ ≤ (K : ℝ≥0∞) * (C.cov2ENorm 2 b.exponent.value h) ^ 2 :=
      hR h hh hzh.1 hnorm₀
    _ = ((K : ℝ≥0∞) * C.cov2ENorm 2 b.exponent.value h) *
        C.cov2ENorm 2 b.exponent.value h := by ring
    _ ≤ ENNReal.ofReal eps * C.cov2ENorm 2 b.exponent.value h := mul_le_mul' hKN le_rfl

end K24.Global.HolderFrechet





set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.HolderFrechet

def ActualInverseMetricUniformRemainder : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M],
    ∀ (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
      (z : RawCov2 M), MetricAdmissible C b z →
      ∀ eps : ℝ, 0 < eps → ∃ δ : ℝ, 0 < δ ∧
        ∀ h ∈ tensorHolderSpace C 2 b.exponent.value,
          z + h ∈ positiveHolderMetrics C 2 b.exponent.value →
          C.cov2ENorm 2 b.exponent.value h < ENNReal.ofReal δ →
          (⨆ ν : C.Index, coordinateHolderENorm 0 b.exponent.value (C.chart ν).innerDomain
            (fun x => (C.chart ν).inverseMetricCoefficients (z + h) x -
              (C.chart ν).inverseMetricCoefficients z x +
              (C.chart ν).inverseMetricCoefficients z x * (C.chart ν).liftedCov2 h x *
                (C.chart ν).inverseMetricCoefficients z x)) ≤
            ENNReal.ofReal eps * C.cov2ENorm 2 b.exponent.value h

end K24.Global.HolderFrechet



theorem solution : K24.Global.HolderFrechet.ActualInverseMetricUniformRemainder.{u} := by
  intro M _ _ _ _ C b z hz
  exact K24.Global.HolderFrechet.actual_inverse_uniform_remainder C b z hz

#print axioms solution
