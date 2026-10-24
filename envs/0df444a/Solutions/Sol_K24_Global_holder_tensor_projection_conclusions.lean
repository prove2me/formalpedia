-- Prove2me | solution 1 for K24.Global.holder_tensor_projection_conclusions
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:17:11.925299+00:00
-- url     : https://prove2.me/submissions/8236fc91-8bad-4057-ad6b-cae007f9a8e7

import Definitions.Def_K24GlobalStatement

/- Inlined checked local module GeometricSupport; exact source hash recorded in PROVENANCE.json. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.CoverRegularityProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}

omit [IsManifold I4 ∞ M] in
theorem contMDiffAt_lift (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  apply F.projectionSmooth.contMDiffAt.comp
  exact contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas c.coordinate_mem_atlas) (c.outerSubsetTarget hx)

theorem transition_smooth (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace q) ∘ c.lift) x := by
  apply ContMDiffAt.contDiffAt
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hq).comp x
    (contMDiffAt_lift c x hx)

theorem transition_derivative (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ∃ d : FourSpace ≃L[ℝ] FourSpace,
      HasFDerivAt ((chartAt FourSpace q) ∘ c.lift) (d : FourSpace →L[ℝ] FourSpace) x := by
  let e := chartAt FourSpace q
  let de := (mdifferentiable_chart (I := I4) q).mfderiv hq
  let d : FourSpace ≃L[ℝ] FourSpace := (c.tangentMap x).trans de
  have heq : (d : FourSpace →L[ℝ] FourSpace) =
      mfderiv I4 I4 (e ∘ c.lift) x := by
    rw [mfderiv_comp x ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
      ((contMDiffAt_lift c x hx).mdifferentiableAt (by simp))]
    have hc : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
      c.tangentMap_eq x hx
    rw [← hc]
    rfl
  refine ⟨d, ?_⟩
  rw [heq, mfderiv_eq_fderiv]
  exact ((transition_smooth c q x hx hq).differentiableAt (by simp)).hasFDerivAt

theorem local_inverse (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.innerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ∃ S : FourSpace → FourSpace,
      S (chartAt FourSpace q (c.lift x)) = x ∧
      ContDiffAt ℝ ∞ S (chartAt FourSpace q (c.lift x)) ∧
      (∀ᶠ y in 𝓝 (chartAt FourSpace q (c.lift x)), S y ∈ c.innerDomain) ∧
      (c.lift ∘ S =ᶠ[𝓝 (chartAt FourSpace q (c.lift x))] (chartAt FourSpace q).symm) := by
  have hxo : x ∈ c.outerDomain := c.closureInnerSubset (subset_closure hx)
  let f : FourSpace → FourSpace := (chartAt FourSpace q) ∘ c.lift
  have hf : ContDiffAt ℝ ∞ f x := transition_smooth c q x hxo hq
  obtain ⟨d, hd⟩ := transition_derivative c q x hxo hq
  have hd' : HasFDerivAt f (d : FourSpace →L[ℝ] FourSpace) x := hd
  let S := hf.localInverse hd' (by simp)
  have hSx : S (f x) = x := hf.localInverse_apply_image hd' (by simp)
  have hS : ContDiffAt ℝ ∞ S (f x) := hf.to_localInverse hd' (by simp)
  have hSt : Tendsto S (𝓝 (f x)) (𝓝 x) := by
    simpa only [hSx] using hS.continuousAt.tendsto
  have hinner : ∀ᶠ y in 𝓝 (f x), S y ∈ c.innerDomain :=
    hSt (c.innerOpen.mem_nhds hx)
  have hsource : ∀ᶠ y in 𝓝 (f x), c.lift (S y) ∈ (chartAt FourSpace q).source :=
    ((contMDiffAt_lift c x hxo).continuousAt.tendsto.comp hSt)
      ((chartAt FourSpace q).open_source.mem_nhds hq)
  have hright : ∀ᶠ y in 𝓝 (f x), f (S y) = y :=
    (hf.hasStrictFDerivAt' hd' (by simp)).eventually_right_inverse
  refine ⟨S, hSx, hS, hinner, ?_⟩
  filter_upwards [hsource, hright] with y hy hy'
  change c.lift (S y) = (chartAt FourSpace q).symm y
  calc
    c.lift (S y) = (chartAt FourSpace q).symm (f (S y)) :=
      ((chartAt FourSpace q).left_inv hy).symm
    _ = (chartAt FourSpace q).symm y := congrArg (chartAt FourSpace q).symm hy'


theorem matrixToBilinear_apply (A : Mat4) (v w : FourSpace) :
    matrixToBilinear A v w = ∑ a, ∑ b, v a * A a b * w b := by
  simp [matrixToBilinear, coordProj, mul_assoc]

def pullbackCoefficients (A : FourSpace → Mat4) (S : FourSpace → FourSpace)
    (y : FourSpace) : Mat4 :=
  fun i j => matrixToBilinear (A (S y))
    (fderiv ℝ S y (basisVector i)) (fderiv ℝ S y (basisVector j))

theorem contDiffAt_pullbackCoefficients (A : FourSpace → Mat4)
    (S : FourSpace → FourSpace) (y : FourSpace) (k : ℕ)
    (hA : ContDiffAt ℝ k A (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (pullbackCoefficients A S) y := by
  have hT : ContDiffAt ℝ k (fderiv ℝ S) y := hS.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hAS : ContDiffAt ℝ k (A ∘ S) y := hA.comp y (hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  have hV (i a : Fin 4) :
      ContDiffAt ℝ k (fun z => (fderiv ℝ S z (basisVector i)) a) y :=
    (coordProj a).contDiff.contDiffAt.comp y (hT.clm_apply contDiffAt_const)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [pullbackCoefficients, matrixToBilinear_apply]
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact ((hV i a).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hAS a) b)).mul (hV j b)

omit [IsManifold I4 ∞ M] in
theorem pullbackCoefficients_eventually (c : LocalCoverChart F) (u : RawCov2 M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hS : ContDiffAt ℝ ∞ S y)
    (hinner : ∀ᶠ z in 𝓝 y, S z ∈ c.innerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    pullbackCoefficients (c.liftedCov2 u) S =ᶠ[𝓝 y] cov2InChart u q := by
  have hS1 : ContDiffAt ℝ 1 S y := hS.of_le (by simp)
  have hSnear := hS1.eventually (by simp)
  filter_upwards [hinner, heq.eventuallyEq_nhds, hSnear] with z hz heqz hSz
  have hzo : S z ∈ c.outerDomain := c.closureInnerSubset (subset_closure hz)
  have hDL := (contMDiffAt_lift c (S z) hzo).mdifferentiableAt (by simp)
  have hDS := (hSz.differentiableAt (by simp)).mdifferentiableAt
  have hder := heqz.mfderiv_eq (I := I4) (I' := I4)
  rw [mfderiv_comp z hDL hDS, mfderiv_eq_fderiv] at hder
  have hc : (c.tangentMap (S z)).toContinuousLinearMap =
      mfderiv I4 I4 c.lift (S z) := c.tangentMap_eq (S z) hzo
  rw [← hc] at hder
  have hvec (i : Fin 4) : c.tangentMap (S z) (fderiv ℝ S z (basisVector i)) =
      mfderiv I4 I4 (chartAt FourSpace q).symm z (basisVector i) :=
    congrArg (fun D : FourSpace →L[ℝ] FourSpace => D (basisVector i)) hder
  have hmat := matrixToBilinear_recover
    (bilinearPullback (u (c.lift (S z))) (c.tangentMap (S z)).toContinuousLinearMap)
  change matrixToBilinear (c.liftedCov2 u (S z)) = _ at hmat
  ext i j
  change matrixToBilinear (c.liftedCov2 u (S z))
    (fderiv ℝ S z (basisVector i)) (fderiv ℝ S z (basisVector j)) = _
  rw [hmat]
  simp only [bilinearPullback_apply]
  change u (c.lift (S z)) (c.tangentMap (S z) (fderiv ℝ S z (basisVector i)))
    (c.tangentMap (S z) (fderiv ℝ S z (basisVector j))) = _
  rw [hvec i, hvec j]
  change u (c.lift (S z)) _ _ = u ((chartAt FourSpace q).symm z) _ _
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz.self_of_nhds]

end K24.Global.CoverRegularityProof

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem cov2ContDiff_of_cover_coefficients (C : BoundedLocalCover M) (k : ℕ)
    (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u)
      (C.chart ν).innerDomain) : Cov2ContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy⟩ := C.exists_inner_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]
    exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, hinner, heq⟩ := CoverRegularityProof.local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]
    exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS hinner heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCov2 u) (S y) := by
    rw [hSx]
    exact (hu ν x hx).contDiffAt ((C.chart ν).innerOpen.mem_nhds hx)
  have hpull := CoverRegularityProof.contDiffAt_pullbackCoefficients _ S y k hA hS
  have hequal := CoverRegularityProof.pullbackCoefficients_eventually (C.chart ν) u q S y
    hS hinner heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

theorem cov2ContDiff_of_cov2Holder (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) :
    Cov2ContDiff k u := cov2ContDiff_of_cover_coefficients C k u hu.1

theorem cov2ContDiff_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff b.order g := by
  apply cov2ContDiff_of_cover_coefficients C b.order g
  intro ν
  exact (hg.regularity ν).1.mono (fun x hx =>
    (C.chart ν).closureInnerSubset (subset_closure hx))

theorem cov2ContDiff_one_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff 1 g := by
  intro q
  exact (cov2ContDiff_of_metricAdmissible C b g hg q).of_le
    (by exact_mod_cast (show 1 ≤ b.order from le_trans (by omega) b.order_ge_two))

theorem cov2ContDiff_one_of_tensorHolderSpace (C : BoundedLocalCover M)
    (alpha : ℝ≥0) (u : RawCov2 M) (hu : u ∈ tensorHolderSpace C 2 alpha) :
    Cov2ContDiff 1 u := by
  intro q
  exact (cov2ContDiff_of_cov2Holder C 2 alpha u hu.2 q).of_le (by norm_num)

end K24.Global


namespace K24.Global.HolderHaarProof
open MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuousAt_action_differential_coordinates
    (rho : CircleAction M) (p : M) (t₀ : Circle) :
    ContinuousAt
      (inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
        (fun t => mfderiv I4 I4 (rho.act t) p) t₀) t₀ := by
  have h := rho.smooth.contMDiffAt.mfderiv rho.act (fun _ : Circle => p)
    (contMDiffAt_const : ContMDiffAt (𝓡 1) I4 0 (fun _ : Circle => p) t₀)
    (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)
  exact h.continuousAt

theorem action_differential_coordinates_eq
    (rho : CircleAction M) (p : M) (t₀ t : Circle)
    (ht : rho.act t p ∈ (chartAt FourSpace (rho.act t₀ p)).source) :
    inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
      (fun t => mfderiv I4 I4 (rho.act t) p) t₀ t =
      (mfderiv I4 I4 (chartAt FourSpace (rho.act t₀ p)) (rho.act t p)).comp
        (mfderiv I4 I4 (rho.act t) p) := by
  rw [inTangentCoordinates_eq_mfderiv_comp (mem_chart_source FourSpace p) ht]
  rw [mfderivWithin_range_extChartAt_symm, ContinuousLinearMap.comp_id]
  rfl

theorem continuous_actionPullbackCov2_eval
    (rho : CircleAction M) (u : RawCov2 M)
    (hu : ∀ q : M, ContinuousOn (cov2InChart u q) (chartAt FourSpace q).target)
    (p : M) (v w : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCov2 rho t u p v w) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let q := rho.act t₀ p
  let D := inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
    (fun t => mfderiv I4 I4 (rho.act t) p) t₀
  have hD : ContinuousAt D t₀ := continuousAt_action_differential_coordinates rho p t₀
  have hact : Continuous (fun t : Circle => rho.act t p) :=
    rho.smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hq : q ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hnear : ∀ᶠ t in 𝓝 t₀, rho.act t p ∈ (chartAt FourSpace q).source :=
    hact.continuousAt.preimage_mem_nhds ((chartAt FourSpace q).open_source.mem_nhds hq)
  have hchart : ContinuousAt (fun t : Circle => chartAt FourSpace q (rho.act t p)) t₀ :=
    ((chartAt FourSpace q).continuousAt hq).comp_of_eq hact.continuousAt rfl
  have hcoeff : ContinuousAt
      (fun t : Circle => cov2InChart u q (chartAt FourSpace q (rho.act t p))) t₀ := by
    apply ((hu q).continuousAt ((chartAt FourSpace q).open_target.mem_nhds
      ((chartAt FourSpace q).map_source hq))).comp_of_eq hchart rfl
  have hformula : ContinuousAt (fun t : Circle =>
      matrixToBilinear (cov2InChart u q (chartAt FourSpace q (rho.act t p)))
        (D t v) (D t w)) t₀ := by
    simp only [matrixToBilinear, sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    apply tendsto_finsetSum
    intro a _ha
    apply tendsto_finsetSum
    intro b _hb
    exact ((coordProj a).continuous.continuousAt.comp (hD.clm_apply continuousAt_const)).mul
      (((continuous_apply b).continuousAt.comp
        ((continuous_apply a).continuousAt.comp hcoeff)).mul
        ((coordProj b).continuous.continuousAt.comp (hD.clm_apply continuousAt_const)))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  have hrec := cov2_chart_recovery u q (rho.act t p) ht
  have hd := action_differential_coordinates_eq rho p t₀ t ht
  change D t = _ at hd
  rw [hd]
  dsimp only [actionPullbackCov2, pullbackCov2]
  change u (rho.act t p) (mfderiv I4 I4 (rho.act t) p v)
    (mfderiv I4 I4 (rho.act t) p w) = _
  rw [← hrec]
  rfl

theorem cov2HaarIntegrable_of_canonical_continuity
    (rho : CircleAction M) (u : RawCov2 M)
    (hu : ∀ q : M, ContinuousOn (cov2InChart u q) (chartAt FourSpace q).target) :
    Cov2HaarIntegrable rho u := by
  intro c x _hx i j
  exact Continuous.integrable_of_hasCompactSupport
    (continuous_actionPullbackCov2_eval rho u hu ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j)))
    (HasCompactSupport.of_compactSpace _)

theorem cov2Holder_haarIntegrable_proof
    (C : BoundedLocalCover M) (rho : CircleAction M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) : Cov2HaarIntegrable rho u := by
  apply cov2HaarIntegrable_of_canonical_continuity rho u
  intro q
  exact (cov2ContDiff_of_cov2Holder C k alpha u hu q).continuousOn

theorem tensorHolderSpace_haarIntegrable
    (C : BoundedLocalCover M) (rho : CircleAction M) (k : ℕ) (alpha : ℝ≥0) :
    ∀ u ∈ tensorHolderSpace C k alpha, Cov2HaarIntegrable rho u := by
  intro u hu
  exact cov2Holder_haarIntegrable_proof C rho k alpha u hu.2

end K24.Global.HolderHaarProof


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


/- Inlined checked local module NormAlgebra; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 32
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal ContDiff Matrix.Norms.Elementwise BigOperators
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
@[simp] theorem LocalCoverChart.liftedCov2_sub {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCov2 M) :
    c.liftedCov2 (u - v) = c.liftedCov2 u - c.liftedCov2 v := rfl

@[simp] theorem LocalCoverChart.liftedCov2_add {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCov2 M) :
    c.liftedCov2 (u + v) = c.liftedCov2 u + c.liftedCov2 v := rfl

@[simp] theorem LocalCoverChart.liftedCov2_smul {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (r : ℝ) (u : RawCov2 M) :
    c.liftedCov2 (r • u) = r • c.liftedCov2 u := rfl

@[simp] theorem LocalCoverChart.liftedCov2_zero {F : LocalFiniteCover M}
    (c : LocalCoverChart F) : c.liftedCov2 (0 : RawCov2 M) = 0 := rfl

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem coordinateHolderENorm_zero (k : ℕ) (α : ℝ≥0) (s : Set E) :
    coordinateHolderENorm k α s (0 : E → V) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm, iteratedFDerivWithin_zero]
  exact eHolderNorm_zero s α

theorem coordinateHolderENorm_add_le {k : ℕ} (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) {f g : E → V} (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k α s (f + g) ≤
      coordinateHolderENorm k α s f + coordinateHolderENorm k α s g := by
  have hd : ∀ j ≤ k, derivativeENorm j s (f + g) ≤ derivativeENorm j s f + derivativeENorm j s g := by
    intro j hj
    apply iSup_le
    intro x
    have hfi := hf.of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
    have hgi := hg.of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
    rw [iteratedFDerivWithin_add_apply (hfi x x.property) (hgi x x.property) hs.uniqueDiffOn x.property]
    have hnorm : (‖iteratedFDerivWithin ℝ j f s x + iteratedFDerivWithin ℝ j g s x‖₊ : ℝ≥0∞) ≤
        (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞) + (‖iteratedFDerivWithin ℝ j g s x‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_add_le (iteratedFDerivWithin ℝ j f s x) (iteratedFDerivWithin ℝ j g s x)
    exact hnorm.trans (add_le_add
      (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) x)
      (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j g s y‖₊ : ℝ≥0∞)) x))
  have hh : (fun x : s => iteratedFDerivWithin ℝ k (f + g) s x) =
      (fun x : s => iteratedFDerivWithin ℝ k f s x) + (fun x : s => iteratedFDerivWithin ℝ k g s x) := by
    funext x
    exact iteratedFDerivWithin_add_apply (hf x x.property) (hg x x.property) hs.uniqueDiffOn x.property
  unfold coordinateHolderENorm
  rw [hh]
  have hsum := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun j hj => hd j (by simpa using (Finset.mem_range.mp hj)))
  rw [Finset.sum_add_distrib] at hsum
  exact (add_le_add hsum eHolderNorm_add_le).trans_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem coordinateHolderENorm_smul {k : ℕ} (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) {f : E → V} (hf : ContDiffOn ℝ k f s) (c : ℝ) :
    coordinateHolderENorm k α s (c • f) = ENNReal.ofReal |c| * coordinateHolderENorm k α s f := by
  have hn : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal |c| := by
    simpa only [enorm, Real.norm_eq_abs] using (ofReal_norm c).symm
  have hd : ∀ j ≤ k, derivativeENorm j s (c • f) = ENNReal.ofReal |c| * derivativeENorm j s f := by
    intro j hj
    unfold derivativeENorm
    rw [ENNReal.mul_iSup]
    apply iSup_congr
    intro x
    rw [iteratedFDerivWithin_const_smul_apply ((hf.of_le (by exact_mod_cast hj)) x x.property) hs.uniqueDiffOn x.property,
      nnnorm_smul, ENNReal.coe_mul, hn]
  have hh : (fun x : s => iteratedFDerivWithin ℝ k (c • f) s x) =
      c • (fun x : s => iteratedFDerivWithin ℝ k f s x) := by
    funext x
    exact iteratedFDerivWithin_const_smul_apply (hf x x.property) hs.uniqueDiffOn x.property
  unfold coordinateHolderENorm
  have hh' : eHolderNorm α (c • (fun x : s => iteratedFDerivWithin ℝ k f s x)) =
      (‖c‖₊ : ℝ≥0∞) * eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k f s x) := eHolderNorm_smul c
  rw [hh, hh', hn]
  have hsum : (∑ j ∈ Finset.range (k + 1), derivativeENorm j s (c • f)) =
      ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal |c| * derivativeENorm j s f := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hd j (by simpa using (Finset.mem_range.mp hj))
  rw [hsum, ← Finset.mul_sum, ← mul_add]

theorem BoundedLocalCover.cov2ENorm_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    C.cov2ENorm k α 0 = 0 := by
  simp only [BoundedLocalCover.cov2ENorm, LocalCoverChart.liftedCov2_zero,
    coordinateHolderENorm_zero]
  simp

theorem BoundedLocalCover.cov2ENorm_add_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u v : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain)
    (hv : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 v) (C.chart ν).innerDomain) :
    C.cov2ENorm k α (u + v) ≤ C.cov2ENorm k α u + C.cov2ENorm k α v := by
  apply iSup_le
  intro ν
  rw [LocalCoverChart.liftedCov2_add]
  exact (coordinateHolderENorm_add_le α (C.chart ν).innerOpen (hu ν) (hv ν)).trans
    (add_le_add (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 u)) ν)
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 v)) ν))

theorem BoundedLocalCover.cov2ENorm_smul (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (r : ℝ) (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain) :
    C.cov2ENorm k α (r • u) = ENNReal.ofReal |r| * C.cov2ENorm k α u := by
  unfold BoundedLocalCover.cov2ENorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro ν
  rw [LocalCoverChart.liftedCov2_smul]
  exact coordinateHolderENorm_smul α (C.chart ν).innerOpen (hu ν) r


end K24.Global

/- Inlined checked local module ParameterJets; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology
open Filter
namespace K24.Global.HolderProjectionProof
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contMDiffAt_parameter_fderiv
    (F : Circle → FourSpace → V) (t : Circle) (x : FourSpace) (m n : ℕ∞ω)
    (hF : ContMDiffAt ((𝓡 1).prod I4) 𝓘(ℝ, V) n
      (Function.uncurry F) (t, x)) (hmn : m + 1 ≤ n) :
    ContMDiffAt ((𝓡 1).prod I4) 𝓘(ℝ, FourSpace →L[ℝ] V) m
      (fun z : Circle × FourSpace => fderiv ℝ (F z.1) z.2) (t, x) := by
  have hG : ContMDiffAt (((𝓡 1).prod I4).prod I4) 𝓘(ℝ, V) n
      (Function.uncurry (fun z : Circle × FourSpace => F z.1)) ((t,x),x) := by
    exact hF.comp_of_eq (contMDiffAt_fst.fst.prodMk contMDiffAt_snd) rfl
  have h := hG.mfderiv (fun z : Circle × FourSpace => F z.1) (fun z => z.2)
    (contMDiffAt_snd : ContMDiffAt ((𝓡 1).prod I4) I4 m
      (fun z : Circle × FourSpace => z.2) (t,x)) hmn
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] using h

theorem contMDiffAt_parameter_iteratedFDeriv
    (F : Circle → FourSpace → V) (t : Circle) (x : FourSpace) (k j : ℕ)
    (hF : ContMDiffAt ((𝓡 1).prod I4) 𝓘(ℝ, V) k (Function.uncurry F) (t,x))
    (hj : j ≤ k) :
    ContMDiffAt ((𝓡 1).prod I4)
      𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin j => FourSpace) V) (k-j : ℕ)
      (fun z : Circle × FourSpace => iteratedFDeriv ℝ j (F z.1) z.2) (t,x) := by
  induction j with
  | zero =>
    simpa! only [Nat.sub_zero, iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry] using
      (continuousMultilinearCurryFin0 ℝ FourSpace V).symm.contDiff.contMDiff.contMDiffAt.comp (t,x) hF
  | succ j ih =>
    have hprev := ih (by omega)
    have hd := contMDiffAt_parameter_fderiv
      (fun t x => iteratedFDeriv ℝ j (F t) x) t x (k-(j+1) : ℕ) (k-j : ℕ) hprev (by
        exact_mod_cast (show k - (j + 1) + 1 ≤ k-j by omega))
    simpa! only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => FourSpace) V).symm.contDiff.contMDiff.contMDiffAt.comp (t,x) hd

end K24.Global.HolderProjectionProof

/- Inlined checked local module IntegralNorm; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal BigOperators
namespace K24.Global.HolderProjectionProof
variable {X V : Type*} [MetricSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V]

theorem eHolderNorm_integral_le (alpha : ℝ≥0) (F : Circle → X → V) (g : X → V)
    (hInt : ∀ x, Integrable (fun t => F t x) circleHaar)
    (hg : ∀ x, g x = ∫ t, F t x ∂circleHaar)
    (hfin : ∀ t, eHolderNorm alpha (F t) < ⊤) :
    eHolderNorm alpha g ≤ ∫⁻ t, eHolderNorm alpha (F t) ∂circleHaar := by
  let R := ∫⁻ t, eHolderNorm alpha (F t) ∂circleHaar
  by_cases hR : R = ⊤
  · change _ ≤ R
    rw [hR]
    exact le_top
  have hh : HolderWith R.toNNReal alpha g := by
    intro x y
    rw [ENNReal.coe_toNNReal hR, hg x, hg y]
    refine (edist_integral_le_lintegral_edist (hInt x) (hInt y)).trans ?_
    calc
      _ ≤ ∫⁻ t, eHolderNorm alpha (F t) * edist x y ^ (alpha : ℝ) ∂circleHaar := by
        apply lintegral_mono
        intro t
        have hm := eHolderNorm_lt_top.mp (hfin t)
        simpa only [hm.coe_nnHolderNorm_eq_eHolderNorm] using hm.holderWith x y
      _ = R * edist x y ^ (alpha : ℝ) :=
        lintegral_mul_const' _ _ (by simp [(edist_ne_top x y)])
  exact hh.eHolderNorm_le.trans_eq (ENNReal.coe_toNNReal hR)

theorem sum_lintegral_le {ι : Type*} (s : Finset ι) (f : ι → Circle → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ t, f i t ∂circleHaar) ≤
      ∫⁻ t, ∑ i ∈ s, f i t ∂circleHaar := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    simp only [Finset.sum_cons]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinateHolderENorm_integral_le
    (k : ℕ) (alpha : ℝ≥0) (s : Set E) (F : Circle → E → V) (g : E → V)
    (hInt : ∀ j ≤ k, ∀ x : s,
      Integrable (fun t => iteratedFDerivWithin ℝ j (F t) s x) circleHaar)
    (hderiv : ∀ j ≤ k, ∀ x : s,
      iteratedFDerivWithin ℝ j g s x =
        ∫ t, iteratedFDerivWithin ℝ j (F t) s x ∂circleHaar)
    (hfin : ∀ t, coordinateHolderENorm k alpha s (F t) < ⊤) :
    coordinateHolderENorm k alpha s g ≤
      ∫⁻ t, coordinateHolderENorm k alpha s (F t) ∂circleHaar := by
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s g ≤
      ∫⁻ t, derivativeENorm j s (F t) ∂circleHaar := by
    apply iSup_le
    intro x
    rw [hderiv j hj x]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    apply lintegral_mono
    intro t
    exact le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j (F t) s y‖₊ : ℝ≥0∞)) x
  have hh := eHolderNorm_integral_le alpha
    (fun t (x : s) => iteratedFDerivWithin ℝ k (F t) s x)
    (fun x : s => iteratedFDerivWithin ℝ k g s x)
    (hInt k le_rfl) (hderiv k le_rfl) (fun t =>
      lt_of_le_of_lt (le_add_left le_rfl) (hfin t))
  have hs : (∑ j ∈ Finset.range (k+1), derivativeENorm j s g) ≤
      ∫⁻ t, ∑ j ∈ Finset.range (k+1), derivativeENorm j s (F t) ∂circleHaar :=
    (Finset.sum_le_sum (fun j hj => hd j (by simpa using Finset.mem_range.mp hj))).trans
      (sum_lintegral_le _ _)
  exact (add_le_add hs hh).trans (le_lintegral_add _ _)

end K24.Global.HolderProjectionProof

/- Inlined checked local module IntegralJets; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal BigOperators
namespace K24.Global.HolderProjectionProof
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem derivative_norm_bound (k j : ℕ) (hj : j ≤ k) (alpha : ℝ≥0)
    (s : Set E) (f : E → V) (B : ℝ≥0) (hB : coordinateHolderENorm k alpha s f ≤ B)
    (x : E) (hx : x ∈ s) : ‖iteratedFDerivWithin ℝ j f s x‖ ≤ B := by
  have hd : derivativeENorm j s f ≤ ∑ l ∈ Finset.range (k+1), derivativeENorm l s f :=
    Finset.single_le_sum (a := j) (s := Finset.range (k+1)) (f := fun l => derivativeENorm l s f) (fun _ _ => bot_le) (Finset.mem_range.mpr (by omega))
  have hn : (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞) ≤ B :=
    (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) ⟨x,hx⟩).trans
      (hd.trans ((le_add_right le_rfl).trans hB))
  exact_mod_cast hn

theorem integral_contDiff_and_derivatives
    (k : ℕ) (alpha B : ℝ≥0) {s : Set E} (hs : IsOpen s) (F : Circle → E → V)
    (hF : ∀ t, ContDiffOn ℝ k (F t) s)
    (hcont : ∀ j ≤ k, ∀ x ∈ s,
      Continuous (fun t : Circle => iteratedFDerivWithin ℝ j (F t) s x))
    (hB : ∀ t, coordinateHolderENorm k alpha s (F t) ≤ B) :
    ContDiffOn ℝ k (fun x => ∫ t, F t x ∂circleHaar) s ∧
    ∀ j ≤ k, ∀ x ∈ s,
      iteratedFDerivWithin ℝ j (fun y => ∫ t, F t y ∂circleHaar) s x =
        ∫ t, iteratedFDerivWithin ℝ j (F t) s x ∂circleHaar := by
  let D (j : ℕ) (x : E) := ∫ t, iteratedFDerivWithin ℝ j (F t) s x ∂circleHaar
  have hInt (j : ℕ) (hj : j ≤ k) (x : E) (hx : x ∈ s) :
      Integrable (fun t => iteratedFDerivWithin ℝ j (F t) s x) circleHaar :=
    (hcont j hj x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hD (j : ℕ) (hj : j ≤ k) : ContinuousOn (D j) s := by
    apply continuousOn_of_dominated
      (fun x hx => (hInt j hj x hx).aestronglyMeasurable)
      (fun x hx => Filter.Eventually.of_forall fun t =>
        derivative_norm_bound k j hj alpha s (F t) B (hB t) x hx)
      (integrable_const (B : ℝ))
    exact Filter.Eventually.of_forall fun t =>
      (hF t).continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hs.uniqueDiffOn
  have hstep (j : ℕ) (hj : j < k) (x : E) (hx : x ∈ s) :
      HasFDerivAt (D j)
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) V) (D (j+1) x)) x := by
    let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) V
    have ht := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (F := fun x t => iteratedFDerivWithin ℝ j (F t) s x)
      (F' := fun x t => e (iteratedFDerivWithin ℝ (j+1) (F t) s x))
      (bound := fun _ : Circle => (B : ℝ)) (hs.mem_nhds hx)
      ((show ∀ᶠ y in 𝓝 x, y ∈ s from hs.mem_nhds hx).mono fun y hy => (hInt j hj.le y hy).aestronglyMeasurable)
      (hInt j hj.le x hx)
      ((e.continuous.comp (hcont (j+1) (by omega) x hx)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t y hy => by
        rw [e.norm_map]
        exact derivative_norm_bound k (j+1) (by omega) alpha s (F t) B (hB t) y hy)
      (integrable_const (B : ℝ))
      (Filter.Eventually.of_forall fun t y hy => by
        have hd := (((hF t).differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast hj) hs.uniqueDiffOn y hy).hasFDerivWithinAt).hasFDerivAt
            (hs.mem_nhds hy)
        simpa only [fderivWithin_iteratedFDerivWithin, Function.comp_apply] using hd)
    have hcomm : (∫ t, e (iteratedFDerivWithin ℝ (j+1) (F t) s x) ∂circleHaar) = e (D (j+1) x) := by
      let G : Circle → (E →L[ℝ] E [×j]→L[ℝ] V) :=
        fun t => e (iteratedFDerivWithin ℝ (j+1) (F t) s x)
      have hGc : Continuous G := by
        convert! (e.continuous.comp (hcont (j+1) (by omega) x hx)) using 1
      have heInt : Integrable G circleHaar :=
        hGc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      ext v w
      rw [ContinuousLinearMap.integral_apply heInt v,
        ContinuousMultilinearMap.integral_apply (heInt.apply_continuousLinearMap v) w]
      change (∫ t, (iteratedFDerivWithin ℝ (j+1) (F t) s x) (Fin.cons v w) ∂circleHaar) =
        (∫ t, iteratedFDerivWithin ℝ (j+1) (F t) s x ∂circleHaar) (Fin.cons v w)
      exact (ContinuousMultilinearMap.integral_apply (hInt (j+1) (by omega) x hx) _).symm
    rw [hcomm] at ht
    exact ht
  have heq : ∀ j ≤ k, Set.EqOn (D j)
      (iteratedFDerivWithin ℝ j (fun x => ∫ t, F t x ∂circleHaar) s) s := by
    intro j
    induction j with
    | zero =>
      intro _hj x hx
      ext w
      rw [show D 0 x = ∫ t, iteratedFDerivWithin ℝ 0 (F t) s x ∂circleHaar from rfl,
        ContinuousMultilinearMap.integral_apply (hInt 0 (by omega) x hx) w]
      simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
        continuousMultilinearCurryFin0_symm_apply, ContinuousMultilinearMap.uncurry0_apply]
    | succ j ih =>
      intro hj x hx
      have hj' : j < k := by omega
      have hd := (hstep j hj' x hx).hasFDerivWithinAt.fderivWithin (hs.uniqueDiffOn x hx)
      rw [fderivWithin_congr (ih hj'.le) (ih hj'.le hx)] at hd
      apply (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) V).injective
      exact hd.symm
  refine ⟨?_, fun j hj x hx => (heq j hj hx).symm⟩
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn hs.uniqueDiffOn).mpr
  constructor
  · intro j hj
    exact (hD j hj).congr (fun x hx => (heq j hj hx).symm)
  · intro j hj
    exact (show DifferentiableOn ℝ (D j) s from
      fun x hx => (hstep j hj x hx).differentiableAt.differentiableWithinAt).congr
        (fun x hx => (heq j hj.le hx).symm)

end K24.Global.HolderProjectionProof

/- Inlined checked local module ActionJets; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 32
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology NNReal Matrix.Norms.Elementwise BigOperators
namespace K24.Global.HolderProjectionProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {L : LocalFiniteCover M}

theorem lifted_action_coefficients
    (c : LocalCoverChart L) (rho : CircleAction M) (u : RawCov2 M)
    (q : M) (t : Circle) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hq : rho.act t (c.lift x) ∈ (chartAt FourSpace q).source) (i j : Fin 4) :
    c.liftedCov2 (actionPullbackCov2 rho t u) x i j =
      matrixToBilinear (cov2InChart u q (chartAt FourSpace q (rho.act t (c.lift x))))
        (fderiv ℝ (fun y => chartAt FourSpace q (rho.act t (c.lift y))) x (basisVector i))
        (fderiv ℝ (fun y => chartAt FourSpace q (rho.act t (c.lift y))) x (basisVector j)) := by
  have hL : MDifferentiableAt I4 I4 c.lift x :=
    (CoverRegularityProof.contMDiffAt_lift c x hx).mdifferentiableAt (by simp)
  have hR : MDifferentiableAt I4 I4 (rho.act t) (c.lift x) :=
    (circleAction_smooth_slice rho t).mdifferentiableAt (by simp)
  have hE := (mdifferentiable_chart (I := I4) q).mdifferentiableAt hq
  have hd : fderiv ℝ (fun y => chartAt FourSpace q (rho.act t (c.lift y))) x =
      (mfderiv I4 I4 (chartAt FourSpace q) (rho.act t (c.lift x))).comp
        ((mfderiv I4 I4 (rho.act t) (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap) := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv I4 I4 ((chartAt FourSpace q) ∘ ((rho.act t) ∘ c.lift)) x = _
    rw [mfderiv_comp x hE (hR.comp x hL), mfderiv_comp x hR hL]
    have hc : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
      c.tangentMap_eq x hx
    rw [hc]
    rfl
  rw [hd]
  have hrec := cov2_chart_recovery u q (rho.act t (c.lift x)) hq
  dsimp only [LocalCoverChart.liftedCov2, actionPullbackCov2, pullbackCov2]
  rw [← hrec]
  rfl

theorem contMDiffAt_lifted_action
    (c : LocalCoverChart L) (rho : CircleAction M) (u : RawCov2 M) (k : ℕ)
    (hu : Cov2ContDiff k u) (t : Circle) (x : FourSpace) (hx : x ∈ c.outerDomain) :
    ContMDiffAt ((𝓡 1).prod I4) 𝓘(ℝ, Mat4) k
      (fun z : Circle × FourSpace => c.liftedCov2 (actionPullbackCov2 rho z.1 u) z.2) (t,x) := by
  let q := rho.act t (c.lift x)
  let A : Circle → FourSpace → FourSpace := fun t y => chartAt FourSpace q (rho.act t (c.lift y))
  have hq : q ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hact : ContMDiffAt ((𝓡 1).prod I4) I4 ∞
      (fun z : Circle × FourSpace => rho.act z.1 (c.lift z.2)) (t,x) :=
    rho.smooth.contMDiffAt.comp (t,x)
      (contMDiffAt_fst.prodMk ((CoverRegularityProof.contMDiffAt_lift c x hx).comp (t,x) contMDiffAt_snd))
  have hA : ContMDiffAt ((𝓡 1).prod I4) I4 ∞ (Function.uncurry A) (t,x) :=
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hq).comp_of_eq hact rfl
  have hkinf : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl k
  have hkplusinf : (k : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_le_of_coe_top_le_withTop le_rfl (k+1)
  have hcoeff : ContMDiffAt ((𝓡 1).prod I4) 𝓘(ℝ, Mat4) k
      (fun z : Circle × FourSpace => cov2InChart u q (A z.1 z.2)) (t,x) :=
    ((hu q _ ((chartAt FourSpace q).map_source hq)).contDiffAt
      ((chartAt FourSpace q).open_target.mem_nhds ((chartAt FourSpace q).map_source hq))).contMDiffAt.comp
        (t,x) (hA.of_le hkinf)
  have hD := contMDiffAt_parameter_fderiv A t x k ∞ hA hkplusinf
  have hformula : ContMDiffAt ((𝓡 1).prod I4) 𝓘(ℝ, Mat4) k
      (fun z : Circle × FourSpace => Matrix.of (fun i j : Fin 4 =>
        matrixToBilinear (cov2InChart u q (A z.1 z.2))
          (fderiv ℝ (A z.1) z.2 (basisVector i))
          (fderiv ℝ (A z.1) z.2 (basisVector j)))) (t,x) := by
    apply contMDiffAt_pi_space.mpr
    intro i
    apply contMDiffAt_pi_space.mpr
    intro j
    simp only [CoverRegularityProof.matrixToBilinear_apply, Matrix.of_apply]
    apply contMDiffAt_finsetSum
    intro a _ha
    apply contMDiffAt_finsetSum
    intro b _hb
    have hva := ((coordProj a).contDiff.contMDiff.contMDiffAt.comp (t,x)
      (hD.clm_apply (contMDiffAt_const (c := basisVector i))))
    have hvb := ((coordProj b).contDiff.contMDiff.contMDiffAt.comp (t,x)
      (hD.clm_apply (contMDiffAt_const (c := basisVector j))))
    have hab := (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hcoeff a) b)
    exact (hva.mul hab).mul hvb
  apply hformula.congr_of_eventuallyEq
  have houter : ∀ᶠ z : Circle × FourSpace in 𝓝 (t,x), z.2 ∈ c.outerDomain :=
    continuousAt_snd.preimage_mem_nhds (c.outerOpen.mem_nhds hx)
  have hsource : ∀ᶠ z : Circle × FourSpace in 𝓝 (t,x),
      rho.act z.1 (c.lift z.2) ∈ (chartAt FourSpace q).source :=
    hact.continuousAt.preimage_mem_nhds ((chartAt FourSpace q).open_source.mem_nhds hq)
  filter_upwards [houter,hsource] with z hz hqz
  funext i j
  exact lifted_action_coefficients c rho u q z.1 z.2 hz hqz i j

theorem continuous_lifted_action_derivative
    (C : BoundedLocalCover M) (rho : CircleAction M) (u : RawCov2 M) (k : ℕ)
    (hu : Cov2ContDiff k u) (nu : C.Index) (j : ℕ) (hj : j ≤ k)
    (x : FourSpace) (hx : x ∈ (C.chart nu).innerDomain) :
    Continuous (fun t : Circle => iteratedFDerivWithin ℝ j
      ((C.chart nu).liftedCov2 (actionPullbackCov2 rho t u)) (C.chart nu).innerDomain x) := by
  have hxo : x ∈ (C.chart nu).outerDomain := (C.chart nu).closureInnerSubset (subset_closure hx)
  have hcont : Continuous (fun t : Circle => iteratedFDeriv ℝ j
      ((C.chart nu).liftedCov2 (actionPullbackCov2 rho t u)) x) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hf := contMDiffAt_lifted_action (C.chart nu) rho u k hu t x hxo
    have h := contMDiffAt_parameter_iteratedFDeriv (V := Mat4)
      (fun t => (C.chart nu).liftedCov2 (actionPullbackCov2 rho t u)) t x k j hf hj
    have hc := h.continuousAt
    have hmap : ContinuousAt (fun s : Circle => (s,x)) t :=
      continuousAt_id.prodMk continuousAt_const
    convert! hc.comp_of_eq hmap rfl using 1
  apply hcont.congr
  intro t
  exact (iteratedFDerivWithin_of_isOpen j (C.chart nu).innerOpen hx).symm

end K24.Global.HolderProjectionProof

/- Inlined checked local module MeanCoefficients; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global.HolderProjectionProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
local instance tangentNormedAddCommGroup (p : M) : NormedAddCommGroup (TangentSpace I4 p) :=
  inferInstanceAs (NormedAddCommGroup FourSpace)
local instance tangentNormedSpace (p : M) : NormedSpace ℝ (TangentSpace I4 p) :=
  inferInstanceAs (NormedSpace ℝ FourSpace)
local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) :=
  inferInstanceAs (FiniteDimensional ℝ FourSpace)
local instance tangentCompleteSpace (p : M) : CompleteSpace (TangentSpace I4 p) :=
  inferInstanceAs (CompleteSpace FourSpace)

def liftedCov2AtCLM {L : LocalFiniteCover M} (c : LocalCoverChart L) (x : FourSpace) :
    (TangentSpace I4 (c.lift x) →L[ℝ] (TangentSpace I4 (c.lift x) →L[ℝ] ℝ)) →L[ℝ] Mat4 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a i j => a (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable [IsManifold I4 ∞ M]
theorem liftedCov2_pi0 {L : LocalFiniteCover M} (c : LocalCoverChart L)
    (rho : CircleAction M) (u : RawCov2 M) (hu : Cov2HaarIntegrable rho u) :
    c.liftedCov2 (cov2Pi0 rho u) =
      fun x => ∫ t, c.liftedCov2 (actionPullbackCov2 rho t u) x ∂circleHaar := by
  funext x
  change liftedCov2AtCLM c x (cov2Pi0 rho u (c.lift x)) = _
  rw [cov2Pi0_eq_fiberIntegral rho u hu]
  exact ((liftedCov2AtCLM c x).integral_comp_comm (hu.fiber (c.lift x))).symm
end K24.Global.HolderProjectionProof

/- Inlined checked local module TensorProjection; exact source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 32
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise BigOperators
namespace K24.Global.HolderProjectionProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem cov2_average_holder_bound (C : BoundedLocalCover M) (alpha H : ℝ≥0)
    (order : ℕ) (rho : CircleAction M) (ha : HolderActionControl C alpha H order rho)
    (k : ℕ) (hk : k ≤ order) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) :
    C.Cov2Holder k alpha (cov2Pi0 rho u) ∧
    C.cov2ENorm k alpha (cov2Pi0 rho u) ≤ (H : ℝ≥0∞) * C.cov2ENorm k alpha u := by
  have hi := HolderHaarProof.cov2Holder_haarIntegrable_proof C rho k alpha u hu
  have hc := cov2ContDiff_of_cov2Holder C k alpha u hu
  let B : ℝ≥0 := H * (C.cov2ENorm k alpha u).toNNReal
  have hB : (B : ℝ≥0∞) = (H : ℝ≥0∞) * C.cov2ENorm k alpha u := by
    simp [B, ENNReal.coe_toNNReal hu.2.ne]
  have hregbound (nu : C.Index) :
      ContDiffOn ℝ k ((C.chart nu).liftedCov2 (cov2Pi0 rho u)) (C.chart nu).innerDomain ∧
      coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCov2 (cov2Pi0 rho u)) ≤ (B : ℝ≥0∞) := by
    let s := (C.chart nu).innerDomain
    let F : Circle → FourSpace → Mat4 := fun t => (C.chart nu).liftedCov2 (actionPullbackCov2 rho t u)
    have hF (t : Circle) : ContDiffOn ℝ k (F t) s := (ha.tensor k hk t u hu).1.1 nu
    have hb (t : Circle) : coordinateHolderENorm k alpha s (F t) ≤ (B : ℝ≥0∞) := by
      rw [hB]
      exact (le_iSup (fun mu => coordinateHolderENorm k alpha (C.chart mu).innerDomain
        ((C.chart mu).liftedCov2 (actionPullbackCov2 rho t u))) nu).trans
        (ha.tensor k hk t u hu).2
    have hcont (j : ℕ) (hj : j ≤ k) (x : FourSpace) (hx : x ∈ s) :
        Continuous (fun t => iteratedFDerivWithin ℝ j (F t) s x) :=
      continuous_lifted_action_derivative C rho u k hc nu j hj x hx
    have hh := integral_contDiff_and_derivatives k alpha B (C.chart nu).innerOpen F hF hcont hb
    rw [liftedCov2_pi0 (C.chart nu) rho u hi]
    refine ⟨hh.1, ?_⟩
    calc
      _ ≤ ∫⁻ t, coordinateHolderENorm k alpha s (F t) ∂circleHaar :=
        coordinateHolderENorm_integral_le k alpha s F _
          (fun j hj x => (hcont j hj x x.property).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          (fun j hj x => hh.2 j hj x x.property)
          (fun t => (hb t).trans_lt ENNReal.coe_lt_top)
      _ ≤ ∫⁻ _t : Circle, (B : ℝ≥0∞) ∂circleHaar := lintegral_mono hb
      _ = B := by simp
  have hn : C.cov2ENorm k alpha (cov2Pi0 rho u) ≤ (B : ℝ≥0∞) :=
    iSup_le fun nu => (hregbound nu).2
  exact ⟨⟨fun nu => (hregbound nu).1, hn.trans_lt ENNReal.coe_lt_top⟩, hn.trans_eq hB⟩

theorem cov2_projection_conclusions_proof (C : BoundedLocalCover M) (alpha H : ℝ≥0)
    (order : ℕ) (rho : CircleAction M) (ha : HolderActionControl C alpha H order rho)
    (k : ℕ) (hk : k ≤ order) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) :
    Cov2HaarIntegrable rho u ∧
    C.Cov2Holder k alpha (cov2Pi0 rho u) ∧
    C.Cov2Holder k alpha (cov2PiPerp rho u) ∧
    IsInvariantCov2 rho (cov2Pi0 rho u) ∧
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
    IsNonzeroCov2 rho (cov2PiPerp rho u) ∧
    C.cov2ENorm k alpha (cov2Pi0 rho u) ≤ (H : ℝ≥0∞) * C.cov2ENorm k alpha u ∧
    C.cov2ENorm k alpha (cov2PiPerp rho u) ≤
      ((1+H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm k alpha u := by
  have hi := HolderHaarProof.cov2Holder_haarIntegrable_proof C rho k alpha u hu
  obtain ⟨hm, hmn⟩ := cov2_average_holder_bound C alpha H order rho ha k hk u hu
  have hneg : C.cov2ENorm k alpha ((-1 : ℝ) • cov2Pi0 rho u) = C.cov2ENorm k alpha (cov2Pi0 rho u) := by
    rw [C.cov2ENorm_smul k alpha (-1) (cov2Pi0 rho u) hm.1]
    norm_num
  have hpreg : ∀ nu : C.Index,
      ContDiffOn ℝ k ((C.chart nu).liftedCov2 (cov2PiPerp rho u)) (C.chart nu).innerDomain := by
    intro nu
    rw [cov2PiPerp, LocalCoverChart.liftedCov2_sub]
    convert! (hu.1 nu).sub (hm.1 nu) using 1
  have hpbound : C.cov2ENorm k alpha (cov2PiPerp rho u) ≤
      ((1+H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm k alpha u := by
    change C.cov2ENorm k alpha (u - cov2Pi0 rho u) ≤ _
    rw [sub_eq_add_neg, ← neg_one_smul ℝ (cov2Pi0 rho u)]
    have hb := C.cov2ENorm_add_le k alpha u ((-1 : ℝ) • cov2Pi0 rho u) hu.1
      (fun nu => by
        rw [LocalCoverChart.liftedCov2_smul]
        convert! (hm.1 nu).const_smul (-1 : ℝ) using 1)
    rw [hneg] at hb
    calc
      _ ≤ C.cov2ENorm k alpha u + C.cov2ENorm k alpha (cov2Pi0 rho u) := hb
      _ ≤ C.cov2ENorm k alpha u + (H : ℝ≥0∞) * C.cov2ENorm k alpha u := by gcongr
      _ = ((1+H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm k alpha u := by
        rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]
  have hp : C.Cov2Holder k alpha (cov2PiPerp rho u) :=
    ⟨hpreg, hpbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.2)⟩
  exact ⟨hi, hm, hp, cov2Pi0_invariant rho u hi, cov2Pi0_idempotent rho u hi,
    cov2PiPerp_zeroMean rho u hi, hmn, hpbound⟩
end K24.Global.HolderProjectionProof

set_option maxSynthPendingDepth 32
namespace K24.Global
universe u
theorem _root_.solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M]
      (C : BoundedLocalCover M) (alpha : HolderExponent) (H : ℝ≥0)
      (order : ℕ) (rho : CircleAction M),
      HolderActionControl C alpha.value H order rho →
      ∀ k ≤ order, ∀ v : RawCov2 M, C.Cov2Holder k alpha.value v →
        Cov2HaarIntegrable rho v ∧
        C.Cov2Holder k alpha.value (cov2Pi0 rho v) ∧
        C.Cov2Holder k alpha.value (cov2PiPerp rho v) ∧
        IsInvariantCov2 rho (cov2Pi0 rho v) ∧
        cov2Pi0 rho (cov2Pi0 rho v) = cov2Pi0 rho v ∧
        IsNonzeroCov2 rho (cov2PiPerp rho v) ∧
        C.cov2ENorm k alpha.value (cov2Pi0 rho v) ≤
          (H : ℝ≥0∞) * C.cov2ENorm k alpha.value v ∧
        C.cov2ENorm k alpha.value (cov2PiPerp rho v) ≤
          ((1 + H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm k alpha.value v := by
  intro M _ _ _ _ _ C alpha H order rho ha k hk u hu
  exact HolderProjectionProof.cov2_projection_conclusions_proof C alpha.value H order rho ha k hk u hu
end K24.Global
