-- Prove2me | solution 1 for K24.Global.cov2Holder_haarIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:42:48.846603+00:00
-- url     : https://prove2.me/submissions/237128c5-d59f-4d6b-b447-bb82569b7c81

import Definitions.Def_K24GlobalStatement

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

namespace K24.Global
universe u
 theorem _root_.solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (rho : CircleAction M)
      (k : ℕ) (alpha : ℝ≥0) (v : RawCov2 M),
      C.Cov2Holder k alpha v → Cov2HaarIntegrable rho v := by
  intro M _ _ _ C rho k alpha v hv
  exact HolderHaarProof.cov2Holder_haarIntegrable_proof C rho k alpha v hv
end K24.Global
