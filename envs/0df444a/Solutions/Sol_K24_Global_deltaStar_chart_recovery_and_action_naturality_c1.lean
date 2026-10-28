-- Prove2me | solution 1 for K24.Global.deltaStar_chart_recovery_and_action_naturality_c1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:12:12.441039+00:00
-- url     : https://prove2.me/submissions/598556b4-0852-42e2-8611-ec71bf0c9ca6

import Definitions.Def_K24GlobalStatement

/- Inlined checked module: CoverRegularity.lean -/

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

end K24.Global

/- Inlined checked module: Infrastructure.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem cov2InChart_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart g c x i j = cov2InChart g c x j i := by
  exact hg _ _ _

theorem cov2InChart_isUnit_det [IsManifold I4 ∞ M] (g : RawCov2 M)
    (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    IsUnit (cov2InChart g c x).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.PosDef.isUnit
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      cov2InChart_symmetric g hg.1 c x j i
  · intro v hv
    let w : FourSpace := ∑ i, v i • basisVector i
    have hw : w ≠ 0 := by
      intro hw
      apply hv
      funext i
      have h := congrArg (fun q : FourSpace => q i) hw
      simpa [w, basisVector, Pi.single_apply] using h
    let e := chartAt FourSpace c
    let di := mfderiv I4 I4 e.symm x
    have hinj : Function.Injective di := by
      apply Function.LeftInverse.injective (g := mfderiv I4 I4 e (e.symm x))
      intro v
      exact congrArg (fun A => A v) ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
    have hdi : di w ≠ 0 := by
      intro h
      exact hw (hinj (h.trans (map_zero di).symm))
    have hpos := hg.2 (e.symm x) (di w) hdi
    have heq : star v ⬝ᵥ (cov2InChart g c x *ᵥ v) =
        g (e.symm x) (di w) (di w) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        cov2InChart, w, map_sum, map_smul, _root_.sum_apply,
        _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hg.1 (e.symm x) (di (basisVector j)) (di (basisVector i))]
      ring
    rw [heq]
    exact hpos

theorem differentiableAt_inverseMetric [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) :
    DifferentiableAt ℝ (inverseMetricInChart g c) x := by
  have hentry (a b : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hDg a) b
  have hdet : DifferentiableAt ℝ (fun y => (cov2InChart g c y).det) x := by
    simp only [Matrix.det_apply']
    apply DifferentiableAt.fun_sum
    intro σ _
    apply DifferentiableAt.const_mul
    exact (HasFDerivAt.finsetProd (u := Finset.univ)
      (fun i _ => (hentry (σ i) i).hasFDerivAt)).differentiableAt
  have hne : (cov2InChart g c x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (cov2InChart_isUnit_det g hg c x hx)
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  simp only [inverseMetricInChart, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  apply (hdet.inv hne).mul
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  have hrow (i : Fin 4) : DifferentiableAt ℝ
      (fun y => Matrix.updateRow (cov2InChart g c y) b (Pi.single a 1) (σ i) i) x := by
    simp only [Matrix.updateRow_apply]
    split_ifs <;> first | exact differentiableAt_const _ | exact hentry _ _
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun i _ => (hrow i).hasFDerivAt)).differentiableAt

theorem christoffel_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (d a b : Fin 4) :
    christoffelInChart g c x d a b = christoffelInChart g c x d b a := by
  have hs : (fun y => cov2InChart g c y a b) =
      (fun y => cov2InChart g c y b a) := by
    funext y
    exact hg _ _ _
  unfold christoffelInChart
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem christoffel_lower [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    2 * (∑ p : Fin 4, christoffelInChart g c x p a b * cov2InChart g c x p d) =
      coordDeriv (fun y => cov2InChart g c y b d) a x +
      coordDeriv (fun y => cov2InChart g c y a d) b x -
      coordDeriv (fun y => cov2InChart g c y a b) d x := by
  let A := cov2InChart g c x
  let K := fun r => coordDeriv (fun y => cov2InChart g c y b r) a x +
    coordDeriv (fun y => cov2InChart g c y a r) b x -
    coordDeriv (fun y => cov2InChart g c y a b) r x
  have hsum : (∑ p, christoffelInChart g c x p a b * cov2InChart g c x p d) =
      (1 / 2 : ℝ) * (A *ᵥ (A⁻¹ *ᵥ K)) d := by
    change (∑ p, christoffelInChart g c x p a b * cov2InChart g c x p d) =
      (1 / 2 : ℝ) * ∑ p, cov2InChart g c x d p * ∑ r, inverseMetricInChart g c x p r * K r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [cov2InChart_symmetric g hg.1 c x p d]
    unfold christoffelInChart K
    ring
  rw [hsum, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
    (cov2InChart_isUnit_det g hg c x hx), Matrix.one_mulVec]
  dsimp [K]
  ring


end K24.Global.IdentityProof

namespace K24.Global.LieNaturality
abbrev Form := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

abbrev matrixToForm : Mat4 → Form := matrixToBilinear

@[simp] theorem matrixToForm_apply (A : Mat4) : matrixToForm A = matrixToBilinear A := rfl

theorem fderiv_form_apply (A : FourSpace → Form) (U V : FourSpace → FourSpace)
    (x t : FourSpace) (hA : DifferentiableAt ℝ A x)
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => A y (U y) (V y)) x t =
      fderiv ℝ A x t (U x) (V x) + A x (fderiv ℝ U x t) (V x) +
        A x (U x) (fderiv ℝ V x t) := by
  rw [fderiv_clm_apply (hA.clm_apply hU) hV, fderiv_clm_apply hA hU]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem fderiv_form_const (A : FourSpace → Form) (x t u v : FourSpace)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => A y u v) x t = fderiv ℝ A x t u v := by
  rw [fderiv_form_apply A (fun _ => u) (fun _ => v) x t hA
    (differentiableAt_const _) (differentiableAt_const _)]
  simp

theorem fderiv_derivative_apply (F : FourSpace → FourSpace) (x t u : FourSpace)
    (hF : DifferentiableAt ℝ (fderiv ℝ F) x) :
    fderiv ℝ (fun y => fderiv ℝ F y u) x t = fderiv ℝ (fderiv ℝ F) x t u := by
  rw [fderiv_clm_apply hF (differentiableAt_const _)]
  simp

@[simp] theorem matrixToForm_basis (A : Mat4) (i j : Fin 4) :
    matrixToForm A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToForm_apply, matrixToBilinear, coordProj, basisVector]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def formInChart (g : RawCov2 M) (c : M) : FourSpace → Form :=
  matrixToForm ∘ cov2InChart g c

theorem formInChart_eq (g : RawCov2 M) (c : M) (x : FourSpace) :
    formInChart g c x = bilinearPullback (g ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (chartAt FourSpace c).symm x) := by
  exact matrixToBilinear_recover
    (bilinearPullback (g ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (chartAt FourSpace c).symm x))

theorem formInChart_differentiableAt (g : RawCov2 M) (c : M) (x : FourSpace)
    (hg : DifferentiableAt ℝ (cov2InChart g c) x) :
    DifferentiableAt ℝ (formInChart g c) x := by
  have heq : formInChart g c = fun y => ∑ i : Fin 4, ∑ j : Fin 4,
      cov2InChart g c y i j • (coordProj i).smulRight (coordProj j) := by
    ext y u v
    simp only [formInChart, Function.comp_apply, matrixToForm_apply, matrixToBilinear,
      _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun i y => ∑ j : Fin 4, cov2InChart g c y i j • (coordProj i).smulRight (coordProj j))
  intro i _
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun j y => cov2InChart g c y i j • (coordProj i).smulRight (coordProj j))
  intro j _
  let T : ℝ →L[ℝ] Form := ContinuousLinearMap.toSpanSingleton ℝ
    ((coordProj i).smulRight (coordProj j))
  exact DifferentiableAt.comp (g := T) (f := fun y => cov2InChart g c y i j) x
    (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := ℝ) (F := Form) T) (differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j)


end K24.Global.LieNaturality

namespace K24.Global.LieNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

def chartTransition (c d : M) : FourSpace → FourSpace :=
  (chartAt FourSpace d) ∘ (chartAt FourSpace c).symm

theorem chartTransition_smooth (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (chartTransition c d) x := by
  apply ContMDiffAt.contDiffAt
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hd).comp x
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hx)

theorem chartTransition_derivative (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (chartTransition c d) x =
      (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm x)).comp
        (mfderiv I4 I4 (chartAt FourSpace c).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x ((mdifferentiable_chart (I := I4) d).mdifferentiableAt hd)
    ((mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hx)

theorem chartTransition_inverse_differential (c d : M) (x v : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) =
      mfderiv I4 I4 (chartAt FourSpace c).symm x v := by
  rw [chartTransition_derivative c d x hx hd]
  exact congrArg (fun D => D (mfderiv I4 I4 (chartAt FourSpace c).symm x v))
    ((mdifferentiable_chart (I := I4) d).symm_comp_deriv hd)

theorem chartTransition_form (g : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    formInChart g c x = bilinearPullback (formInChart g d (chartTransition c d x))
      (fderiv ℝ (chartTransition c d) x) := by
  rw [formInChart_eq, formInChart_eq]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change g ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x u)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x v) =
    g ((chartAt FourSpace d).symm (chartTransition c d x))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x u))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v))
  rw [chartTransition_inverse_differential c d x u hx hd,
    chartTransition_inverse_differential c d x v hx hd]
  change g ((chartAt FourSpace c).symm x) _ _ =
    g ((chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x))) _ _
  rw [(chartAt FourSpace d).left_inv hd]

theorem chartTransition_overlap_eventually (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source := by
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx,
    ((chartAt FourSpace c).continuousAt_symm hx).tendsto
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hdy
  exact ⟨hy, hdy⟩

theorem chartTransition_comp_chart_differential (c d p : M)
    (hc : p ∈ (chartAt FourSpace c).source) (hd : p ∈ (chartAt FourSpace d).source)
    (v : TangentSpace I4 p) :
    fderiv ℝ (chartTransition c d) (chartAt FourSpace c p)
      (mfderiv I4 I4 (chartAt FourSpace c) p v) = mfderiv I4 I4 (chartAt FourSpace d) p v := by
  have hcd : (chartAt FourSpace c).symm (chartAt FourSpace c p) ∈ (chartAt FourSpace d).source := by
    rw [(chartAt FourSpace c).left_inv hc]
    exact hd
  rw [chartTransition_derivative c d _ ((chartAt FourSpace c).map_source hc) hcd]
  have hcancel := congrArg (fun D => D v) ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hc)
  change mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
    (mfderiv I4 I4 (chartAt FourSpace c) p v) = v at hcancel
  change mfderiv I4 I4 (chartAt FourSpace d)
    ((chartAt FourSpace c).symm (chartAt FourSpace c p))
    (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
      (mfderiv I4 I4 (chartAt FourSpace c) p v)) = _
  rw [hcancel, (chartAt FourSpace c).left_inv hc]


end K24.Global.LieNaturality

/- Inlined checked module: Connection.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

abbrev Cov3 := FourSpace →L[ℝ] Form
abbrev Gamma := FourSpace →L[ℝ] (FourSpace →L[ℝ] FourSpace)

def flipForm : Form →L[ℝ] Form :=
  (ContinuousLinearMap.flipₗᵢ ℝ FourSpace FourSpace ℝ).toContinuousLinearEquiv.toContinuousLinearMap

def koszulForm (D : Cov3) : Cov3 := D + D.flip - flipForm.comp D.flip

@[simp] theorem koszulForm_apply (D : Cov3) (v w t : FourSpace) :
    koszulForm D v w t = D v w t + D w v t - D t v w := rfl

def gammaForm (g : RawCov2 M) (c : M) (x : FourSpace) : Gamma :=
  ∑ i : Fin 4, ∑ j : Fin 4, (coordProj i).smulRight
    ((coordProj j).smulRight (∑ p : Fin 4, christoffelInChart g c x p i j • basisVector p))

@[simp] theorem gammaForm_basis (g : RawCov2 M) (c : M) (x : FourSpace) (i j : Fin 4) :
    gammaForm g c x (basisVector i) (basisVector j) =
      ∑ p : Fin 4, christoffelInChart g c x p i j • basisVector p := by
  simp [gammaForm, coordProj, basisVector]

theorem clm_eq_of_basis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : FourSpace →L[ℝ] V) (h : ∀ i, A (basisVector i) = B (basisVector i)) : A = B := by
  ext v
  calc
    A v = A (∑ i, v i • basisVector i) := by rw [sum_basisVector]
    _ = B (∑ i, v i • basisVector i) := by simp only [map_sum, map_smul, h]
    _ = B v := by rw [sum_basisVector]

def lowerGamma (G : Form) (Q : Gamma) : Cov3 :=
  (ContinuousLinearMap.compL ℝ FourSpace FourSpace (FourSpace →L[ℝ] ℝ) G).comp Q

@[simp] theorem lowerGamma_apply (G : Form) (Q : Gamma) (v w t : FourSpace) :
    lowerGamma G Q v w t = G (Q v w) t := rfl

theorem formInChart_derivative_basis (g : RawCov2 M) (c : M) (x : FourSpace)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) (i j k : Fin 4) :
    fderiv ℝ (formInChart g c) x (basisVector i) (basisVector j) (basisVector k) =
      coordDeriv (fun y => cov2InChart g c y j k) i x := by
  rw [← fderiv_form_const _ x (basisVector i) (basisVector j) (basisVector k)
    (formInChart_differentiableAt g c x hDg)]
  have heq : (fun y => formInChart g c y (basisVector j) (basisVector k)) =
      (fun y => cov2InChart g c y j k) := by
    funext y
    exact matrixToForm_basis _ j k
  rw [heq]
  rfl

theorem gammaForm_lower (g : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) (v w t : FourSpace) :
    2 * formInChart g c x (gammaForm g c x v w) t =
      koszulForm (fderiv ℝ (formInChart g c) x) v w t := by
  have heq : (2 : ℝ) • lowerGamma (formInChart g c x) (gammaForm g c x) =
      koszulForm (fderiv ℝ (formInChart g c) x) := by
    apply clm_eq_of_basis
    intro i
    apply clm_eq_of_basis
    intro j
    apply clm_eq_of_basis
    intro k
    simp only [_root_.smul_apply, smul_eq_mul, lowerGamma_apply, koszulForm_apply,
      gammaForm_basis, map_sum, map_smul, _root_.sum_apply,
      formInChart_derivative_basis g c x hDg]
    simp only [formInChart, Function.comp_apply, matrixToForm_basis]
    change 2 * (∑ p, christoffelInChart g c x p i j * cov2InChart g c x p k) = _
    exact christoffel_lower g hg c x hx i j k
  exact congrArg (fun D : Cov3 => D v w t) heq

theorem fderiv_pullback_relation (A B : FourSpace → Form) (F : FourSpace → FourSpace)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B x)
    (heq : B =ᶠ[𝓝 x] (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y)))
    (v w t : FourSpace) :
    fderiv ℝ B x v w t =
      fderiv ℝ A (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x t) +
      A (F x) (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x t) +
      A (F x) (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v t) := by
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heval : (fun y => B y w t) =ᶠ[𝓝 x]
      (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y) w t) :=
    heq.mono (fun y hy => congrArg (fun Q : Form => Q w t) hy)
  have h := congrArg (fun D : FourSpace →L[ℝ] ℝ => D v) (heval.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_form_const B x v w t hB] at h
  change fderiv ℝ B x v w t =
    fderiv ℝ (fun y => A (F y) (fderiv ℝ F y w) (fderiv ℝ F y t)) x v at h
  rw [fderiv_form_apply (fun y => A (F y)) (fun y => fderiv ℝ F y w)
    (fun y => fderiv ℝ F y t) x v (hA.comp x hF1)
      (hDF.clm_apply (differentiableAt_const _)) (hDF.clm_apply (differentiableAt_const _)),
    fderiv_fun_comp x hA hF1, fderiv_derivative_apply F x v w hDF,
    fderiv_derivative_apply F x v t hDF] at h
  exact h

theorem koszulForm_natural (A B : FourSpace → Form) (F : FourSpace → FourSpace)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B x)
    (hsym : ∀ v w, A (F x) v w = A (F x) w v)
    (heq : B =ᶠ[𝓝 x] (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y)))
    (v w t : FourSpace) :
    koszulForm (fderiv ℝ B x) v w t =
      koszulForm (fderiv ℝ A (F x)) (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x t) +
      2 * A (F x) (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x t) := by
  simp only [koszulForm_apply]
  rw [fderiv_pullback_relation A B F x hF hA hB heq v w t,
    fderiv_pullback_relation A B F x hF hA hB heq w v t,
    fderiv_pullback_relation A B F x hF hA hB heq t v w]
  have hH := hF.isSymmSndFDerivAt (by norm_num)
  rw [hH.eq w v, hH.eq t v, hH.eq t w,
    hsym (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v t)]
  ring

theorem formInChart_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x v w : FourSpace) : formInChart g c x v w = formInChart g c x w v := by
  rw [formInChart_eq]
  exact hg _ _ _

theorem formInChart_positive (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (v : FourSpace) (hv : v ≠ 0) :
    0 < formInChart g c x v v := by
  rw [formInChart_eq]
  apply hg.2
  intro hzero
  apply hv
  have hinj := (mdifferentiable_chart (I := I4) c).symm.mfderiv_injective hx
  apply hinj
  exact hzero.trans (map_zero _).symm

theorem formInChart_separates (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (v w : FourSpace)
    (h : ∀ t, formInChart g c x v t = formInChart g c x w t) : v = w := by
  by_contra hne
  have hpos := formInChart_positive g hg c x hx (v-w) (sub_ne_zero.mpr hne)
  have hzero : formInChart g c x (v-w) (v-w) = 0 := by
    rw [map_sub (formInChart g c x) v w, ContinuousLinearMap.sub_apply, h, sub_self]
  linarith


theorem chartTransition_derivative_bijective (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    Function.Bijective (fderiv ℝ (chartTransition c d) x) := by
  rw [chartTransition_derivative c d x hx hd]
  exact ((mdifferentiable_chart (I := I4) d).mfderiv_bijective hd).comp
    ((mdifferentiable_chart (I := I4) c).symm.mfderiv_bijective hx)

theorem chartTransition_form_eventually (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    formInChart u c =ᶠ[𝓝 x] (fun y =>
      bilinearPullback (formInChart u d (chartTransition c d y))
        (fderiv ℝ (chartTransition c d) y)) := by
  filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
  exact chartTransition_form u c d y hy.1 hy.2

theorem gammaForm_natural (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (v w : FourSpace) :
    fderiv ℝ (chartTransition c d) x (gammaForm g c x v w) =
      gammaForm g d (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) +
      fderiv ℝ (fderiv ℝ (chartTransition c d)) x v w := by
  let F := chartTransition c d
  have hFx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hgc := ((hDg c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd := ((hDg d).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hFx)).differentiableAt (by norm_num)
  apply formInChart_separates g hg d (F x) hFx
  intro t
  obtain ⟨r, rfl⟩ := (chartTransition_derivative_bijective c d x hx hd).2 t
  have hG := congrArg (fun Q : Form => Q (gammaForm g c x v w) r)
    (chartTransition_form g c d x hx hd)
  change formInChart g c x (gammaForm g c x v w) r =
    formInChart g d (F x) (fderiv ℝ F x (gammaForm g c x v w)) (fderiv ℝ F x r) at hG
  have hK := koszulForm_natural (formInChart g d) (formInChart g c) F x
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
    (formInChart_differentiableAt g d (F x) hgd)
    (formInChart_differentiableAt g c x hgc)
    (formInChart_symmetric g hg.1 d (F x))
    (chartTransition_form_eventually g c d x hx hd) v w r
  rw [← gammaForm_lower g hg c x hx hgc v w r,
    ← gammaForm_lower g hg d (F x) hFx hgd] at hK
  rw [hG] at hK
  simp only [map_add, ContinuousLinearMap.add_apply]
  change formInChart g d (F x) (fderiv ℝ F x (gammaForm g c x v w)) (fderiv ℝ F x r) = _
  linarith

end K24.Global.BianchiNaturality

/- Inlined checked module: ActionDefinitions.lean -/
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace K24.Global.BianchiInvariance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
def actionInCharts (rho : CircleAction M) (t : Circle) (c d : M) : FourSpace → FourSpace :=
  (chartAt FourSpace d) ∘ (rho.act t) ∘ (chartAt FourSpace c).symm
end K24.Global.BianchiInvariance

/- Inlined checked module: ActionCoordinates.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.BianchiInvariance
open LieNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem action_smooth_slice (rho : CircleAction M) (t : Circle) :
    ContMDiff I4 I4 ∞ (rho.act t) :=
  rho.smooth.comp (contMDiff_const.prodMk contMDiff_id)

theorem action_deriv_mul (rho : CircleAction M) (s t : Circle) (p : M) :
    mfderiv I4 I4 (rho.act (s * t)) p =
      (mfderiv I4 I4 (rho.act s) (rho.act t p)).comp
        (mfderiv I4 I4 (rho.act t) p) := by
  have heq : rho.act (s * t) = rho.act s ∘ rho.act t := funext (rho.mul_act s t)
  rw [heq]
  exact mfderiv_comp p ((action_smooth_slice rho s).mdifferentiable (by simp) _)
    ((action_smooth_slice rho t).mdifferentiable (by simp) _)

theorem action_derivative_inverse (rho : CircleAction M) (t : Circle) (p : M) :
    (mfderiv I4 I4 (rho.act t) p).comp
        (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t p)) = ContinuousLinearMap.id ℝ _ ∧
    (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t p)).comp
        (mfderiv I4 I4 (rho.act t) p) = ContinuousLinearMap.id ℝ _ := by
  have hone : rho.act 1 = id := funext rho.one_act
  have hc : rho.act t⁻¹ (rho.act t p) = p := by
    rw [← rho.mul_act, inv_mul_cancel, rho.one_act]
  constructor
  · have h := action_deriv_mul rho t t⁻¹ (rho.act t p)
    rw [hc, mul_inv_cancel, hone, mfderiv_id] at h
    exact h.symm
  · rw [← action_deriv_mul, inv_mul_cancel, hone, mfderiv_id]

theorem action_derivative_bijective (rho : CircleAction M) (t : Circle) (p : M) :
    Function.Bijective (mfderiv I4 I4 (rho.act t) p) := by
  have hleft : Function.LeftInverse (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t p))
      (mfderiv I4 I4 (rho.act t) p) := by
    intro v
    exact congrArg (fun L => L v) (action_derivative_inverse rho t p).2
  have hright : Function.RightInverse (mfderiv I4 I4 (rho.act t⁻¹) (rho.act t p))
      (mfderiv I4 I4 (rho.act t) p) := by
    intro v
    exact congrArg (fun L => L v) (action_derivative_inverse rho t p).1
  exact ⟨hleft.injective, hright.surjective⟩

theorem actionInCharts_smooth (rho : CircleAction M) (t : Circle) (c d : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (actionInCharts rho t c d) x := by
  apply ContMDiffAt.contDiffAt
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hd).comp x
    ((action_smooth_slice rho t).contMDiffAt.comp x
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hx))

theorem actionInCharts_derivative (rho : CircleAction M) (t : Circle) (c d : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (actionInCharts rho t c d) x =
      (mfderiv I4 I4 (chartAt FourSpace d) (rho.act t ((chartAt FourSpace c).symm x))).comp
        ((mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm x)).comp
          (mfderiv I4 I4 (chartAt FourSpace c).symm x)) := by
  have hC := (mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hx
  have hA := (action_smooth_slice rho t).mdifferentiableAt (by simp)
    (x := (chartAt FourSpace c).symm x)
  have hD := (mdifferentiable_chart (I := I4) d).mdifferentiableAt hd
  rw [← mfderiv_eq_fderiv]
  change mfderiv I4 I4 ((chartAt FourSpace d) ∘ ((rho.act t) ∘ (chartAt FourSpace c).symm)) x = _
  rw [mfderiv_comp x hD (hA.comp x hC), mfderiv_comp x hA hC]
  rfl

theorem actionInCharts_derivative_bijective (rho : CircleAction M) (t : Circle) (c d : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    Function.Bijective (fderiv ℝ (actionInCharts rho t c d) x) := by
  rw [actionInCharts_derivative rho t c d x hx hd]
  exact ((mdifferentiable_chart (I := I4) d).mfderiv_bijective hd).comp
    ((action_derivative_bijective rho t ((chartAt FourSpace c).symm x)).comp
      ((mdifferentiable_chart (I := I4) c).symm.mfderiv_bijective hx))

theorem actionInCharts_inverse_differential (rho : CircleAction M) (t : Circle) (c d : M)
    (x v : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    mfderiv I4 I4 (chartAt FourSpace d).symm (actionInCharts rho t c d x)
      (fderiv ℝ (actionInCharts rho t c d) x v) =
    mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x v) := by
  rw [actionInCharts_derivative rho t c d x hx hd]
  exact congrArg (fun D => D
    (mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x v)))
    ((mdifferentiable_chart (I := I4) d).symm_comp_deriv hd)

theorem actionInCharts_form (rho : CircleAction M) (t : Circle) (u : RawCov2 M)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    formInChart (actionPullbackCov2 rho t u) c x =
      bilinearPullback (formInChart u d (actionInCharts rho t c d x))
        (fderiv ℝ (actionInCharts rho t c d) x) := by
  rw [formInChart_eq, formInChart_eq]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change u (rho.act t ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm x)
        (mfderiv I4 I4 (chartAt FourSpace c).symm x v))
      (mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm x)
        (mfderiv I4 I4 (chartAt FourSpace c).symm x w)) =
    u ((chartAt FourSpace d).symm (actionInCharts rho t c d x))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (actionInCharts rho t c d x)
        (fderiv ℝ (actionInCharts rho t c d) x v))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (actionInCharts rho t c d x)
        (fderiv ℝ (actionInCharts rho t c d) x w))
  rw [actionInCharts_inverse_differential rho t c d x v hx hd,
    actionInCharts_inverse_differential rho t c d x w hx hd]
  dsimp only [actionInCharts, Function.comp_apply]
  rw [(chartAt FourSpace d).left_inv hd]

theorem actionInCharts_overlap_eventually (rho : CircleAction M) (t : Circle) (c d : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
      rho.act t ((chartAt FourSpace c).symm y) ∈ (chartAt FourSpace d).source := by
  have hA : ContinuousAt (fun y => rho.act t ((chartAt FourSpace c).symm y)) x :=
    (action_smooth_slice rho t).continuous.continuousAt.comp
      ((chartAt FourSpace c).continuousAt_symm hx)
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx,
    hA.tendsto ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hdy
  exact ⟨hy, hdy⟩

theorem actionInCharts_form_eventually (rho : CircleAction M) (t : Circle) (u : RawCov2 M)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    formInChart (actionPullbackCov2 rho t u) c =ᶠ[𝓝 x]
      fun y => bilinearPullback (formInChart u d (actionInCharts rho t c d y))
        (fderiv ℝ (actionInCharts rho t c d) y) := by
  filter_upwards [actionInCharts_overlap_eventually rho t c d x hx hd] with y hy
  exact actionInCharts_form rho t u c d y hy.1 hy.2

theorem actionInCharts_comp_chart_differential (rho : CircleAction M) (t : Circle)
    (c d p : M) (hc : p ∈ (chartAt FourSpace c).source)
    (hd : rho.act t p ∈ (chartAt FourSpace d).source) (v : TangentSpace I4 p) :
    fderiv ℝ (actionInCharts rho t c d) (chartAt FourSpace c p)
      (mfderiv I4 I4 (chartAt FourSpace c) p v) =
    mfderiv I4 I4 (chartAt FourSpace d) (rho.act t p)
      (mfderiv I4 I4 (rho.act t) p v) := by
  have hcd : rho.act t ((chartAt FourSpace c).symm (chartAt FourSpace c p)) ∈
      (chartAt FourSpace d).source := by
    rw [(chartAt FourSpace c).left_inv hc]
    exact hd
  rw [actionInCharts_derivative rho t c d _ ((chartAt FourSpace c).map_source hc) hcd]
  have hcancel := congrArg (fun D => D v)
    ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hc)
  change mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
    (mfderiv I4 I4 (chartAt FourSpace c) p v) = v at hcancel
  change mfderiv I4 I4 (chartAt FourSpace d)
    (rho.act t ((chartAt FourSpace c).symm (chartAt FourSpace c p)))
    (mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p v))) = _
  rw [hcancel, (chartAt FourSpace c).left_inv hc]

end K24.Global.BianchiInvariance

/- Inlined checked module: CovectorForms.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.DeltaStarNaturality
open LieNaturality BianchiNaturality BianchiInvariance
abbrev Dual := FourSpace →L[ℝ] ℝ
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

def covectorFormInChart (eta : RawCovector M) (c : M) : FourSpace → Dual :=
  coefficientsToCovector ∘ covectorInChart eta c

theorem covectorFormInChart_eq (eta : RawCovector M) (c : M) (x : FourSpace) :
    covectorFormInChart eta c x = (eta ((chartAt FourSpace c).symm x)).comp
      (mfderiv I4 I4 (chartAt FourSpace c).symm x) :=
  coefficientsToCovector_recover ((eta ((chartAt FourSpace c).symm x)).comp
    (mfderiv I4 I4 (chartAt FourSpace c).symm x))

@[simp] theorem covectorForm_basis (eta : RawCovector M) (c : M) (x : FourSpace) (j : Fin 4) :
    covectorFormInChart eta c x (basisVector j) = covectorInChart eta c x j := by
  simp [covectorFormInChart, coefficientsToCovector, coordProj, basisVector]

theorem covectorForm_contDiffAt (eta : RawCovector M) (c : M) (x : FourSpace) (k : ℕ∞ω)
    (h : ContDiffAt ℝ k (covectorInChart eta c) x) :
    ContDiffAt ℝ k (covectorFormInChart eta c) x := by
  change ContDiffAt ℝ k (fun y => ∑ i : Fin 4, covectorInChart eta c y i • coordProj i) x
  exact ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp h i).smul contDiffAt_const)

theorem covectorForm_differentiableAt (eta : RawCovector M) (c : M) (x : FourSpace)
    (h : DifferentiableAt ℝ (covectorInChart eta c) x) :
    DifferentiableAt ℝ (covectorFormInChart eta c) x := by
  change DifferentiableAt ℝ (fun y => ∑ i : Fin 4, covectorInChart eta c y i • coordProj i) x
  exact DifferentiableAt.fun_sum (fun i _ => (differentiableAt_pi.mp h i).smul (differentiableAt_const _))

theorem fderiv_covector_const (A : FourSpace → Dual) (x v w : FourSpace)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => A y w) x v = fderiv ℝ A x v w := by
  rw [fderiv_clm_apply hA (differentiableAt_const _)]
  simp

theorem covectorForm_derivative_basis (eta : RawCovector M) (c : M) (x : FourSpace)
    (hDeta : DifferentiableAt ℝ (covectorInChart eta c) x) (i j : Fin 4) :
    fderiv ℝ (covectorFormInChart eta c) x (basisVector i) (basisVector j) =
      coordDeriv (fun y => covectorInChart eta c y j) i x := by
  rw [← fderiv_covector_const _ x (basisVector i) (basisVector j)
    (covectorForm_differentiableAt eta c x hDeta)]
  simp only [covectorForm_basis, coordDeriv]

theorem chartTransition_covector (eta : RawCovector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    covectorFormInChart eta c x =
      (covectorFormInChart eta d (chartTransition c d x)).comp
        (fderiv ℝ (chartTransition c d) x) := by
  rw [covectorFormInChart_eq, covectorFormInChart_eq]
  ext v
  change eta ((chartAt FourSpace c).symm x) (mfderiv I4 I4 (chartAt FourSpace c).symm x v) =
    eta ((chartAt FourSpace d).symm (chartTransition c d x))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v))
  rw [chartTransition_inverse_differential c d x v hx hd]
  dsimp only [chartTransition, Function.comp_apply]
  rw [(chartAt FourSpace d).left_inv hd]

theorem chartTransition_covector_eventually (eta : RawCovector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    covectorFormInChart eta c =ᶠ[𝓝 x] (fun y =>
      (covectorFormInChart eta d (chartTransition c d y)).comp
        (fderiv ℝ (chartTransition c d) y)) := by
  filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
  exact chartTransition_covector eta c d y hy.1 hy.2

theorem actionInCharts_covector (rho : CircleAction M) (t : Circle) (eta : RawCovector M)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    covectorFormInChart (actionPullbackCovector rho t eta) c x =
      (covectorFormInChart eta d (actionInCharts rho t c d x)).comp
        (fderiv ℝ (actionInCharts rho t c d) x) := by
  rw [covectorFormInChart_eq, covectorFormInChart_eq]
  ext v
  change eta (rho.act t ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (rho.act t) ((chartAt FourSpace c).symm x)
        (mfderiv I4 I4 (chartAt FourSpace c).symm x v)) =
    eta ((chartAt FourSpace d).symm (actionInCharts rho t c d x))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (actionInCharts rho t c d x)
        (fderiv ℝ (actionInCharts rho t c d) x v))
  rw [actionInCharts_inverse_differential rho t c d x v hx hd]
  dsimp only [actionInCharts, Function.comp_apply]
  rw [(chartAt FourSpace d).left_inv hd]

theorem actionInCharts_covector_eventually (rho : CircleAction M) (t : Circle) (eta : RawCovector M)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    covectorFormInChart (actionPullbackCovector rho t eta) c =ᶠ[𝓝 x] (fun y =>
      (covectorFormInChart eta d (actionInCharts rho t c d y)).comp
        (fderiv ℝ (actionInCharts rho t c d) y)) := by
  filter_upwards [actionInCharts_overlap_eventually rho t c d x hx hd] with y hy
  exact actionInCharts_covector rho t eta c d y hy.1 hy.2

end K24.Global.DeltaStarNaturality

/- Inlined checked module: MetricTransform.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.DeltaStarNaturality
open LieNaturality BianchiNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem gammaForm_natural_between (g h : RawCov2 M) (hg : IsMetric g) (hh : IsMetric h)
    (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (hy : F x ∈ (chartAt FourSpace d).target)
    (hgc : DifferentiableAt ℝ (cov2InChart g c) x)
    (hhd : DifferentiableAt ℝ (cov2InChart h d) (F x))
    (hF : ContDiffAt ℝ 2 F x) (hJ : Function.Bijective (fderiv ℝ F x))
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart h d (F y)) (fderiv ℝ F y))) (v w : FourSpace) :
    fderiv ℝ F x (gammaForm g c x v w) =
      gammaForm h d (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) +
      fderiv ℝ (fderiv ℝ F) x v w := by
  apply formInChart_separates h hh d (F x) hy
  intro t
  obtain ⟨r, rfl⟩ := hJ.2 t
  have hpoint := congrArg (fun Q : Form => Q (gammaForm g c x v w) r) hG.self_of_nhds
  change formInChart g c x (gammaForm g c x v w) r =
    formInChart h d (F x) (fderiv ℝ F x (gammaForm g c x v w)) (fderiv ℝ F x r) at hpoint
  have hK := koszulForm_natural (formInChart h d) (formInChart g c) F x hF
    (formInChart_differentiableAt h d (F x) hhd)
    (formInChart_differentiableAt g c x hgc)
    (formInChart_symmetric h hh.1 d (F x)) hG v w r
  rw [← gammaForm_lower g hg c x hx hgc v w r,
    ← gammaForm_lower h hh d (F x) hy hhd, hpoint] at hK
  simp only [map_add, _root_.add_apply]
  linarith

end K24.Global.DeltaStarNaturality

/- Inlined checked module: DeltaForms.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.DeltaStarNaturality
open LieNaturality BianchiNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem fderiv_covector_pullback (A B : FourSpace → Dual) (F : FourSpace → FourSpace)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B x)
    (heq : B =ᶠ[𝓝 x] (fun y => (A (F y)).comp (fderiv ℝ F y))) (v w : FourSpace) :
    fderiv ℝ B x v w = fderiv ℝ A (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) +
      A (F x) (fderiv ℝ (fderiv ℝ F) x v w) := by
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heval : (fun y => B y w) =ᶠ[𝓝 x] (fun y => A (F y) (fderiv ℝ F y w)) :=
    heq.mono (fun y hy => congrArg (fun a : Dual => a w) hy)
  have h := congrArg (fun D : FourSpace →L[ℝ] ℝ => D v) (heval.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_covector_const B x v w hB] at h
  change fderiv ℝ B x v w = fderiv ℝ (fun y => (A ∘ F) y (fderiv ℝ F y w)) x v at h
  rw [fderiv_clm_apply (hA.comp x hF1) (hDF.clm_apply (differentiableAt_const w)),
    fderiv_comp x hA hF1] at h
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h
  rw [fderiv_derivative_apply F x v w hDF] at h
  simpa only [Function.comp_apply, add_comm] using h

def nablaCovectorForm (g : RawCov2 M) (eta : RawCovector M) (c : M) (x : FourSpace) : Form :=
  fderiv ℝ (covectorFormInChart eta c) x -
    (ContinuousLinearMap.compL ℝ FourSpace FourSpace ℝ (covectorFormInChart eta c x)).comp
      (gammaForm g c x)

@[simp] theorem nablaCovectorForm_apply (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x v w : FourSpace) :
    nablaCovectorForm g eta c x v w = fderiv ℝ (covectorFormInChart eta c) x v w -
      covectorFormInChart eta c x (gammaForm g c x v w) := rfl

theorem nablaCovectorForm_basis (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (hDeta : DifferentiableAt ℝ (covectorInChart eta c) x)
    (i j : Fin 4) :
    nablaCovectorForm g eta c x (basisVector i) (basisVector j) = nablaCovectorInChart g eta c x i j := by
  simp only [nablaCovectorForm_apply, covectorForm_derivative_basis eta c x hDeta,
    gammaForm_basis, map_sum, map_smul, covectorForm_basis, smul_eq_mul, nablaCovectorInChart]

def deltaStarForm (g : RawCov2 M) (eta : RawCovector M) (c : M) (x : FourSpace) : Form :=
  (1 / 2 : ℝ) • (nablaCovectorForm g eta c x + (nablaCovectorForm g eta c x).flip)

@[simp] theorem deltaStarForm_apply (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x v w : FourSpace) :
    deltaStarForm g eta c x v w = (1 / 2 : ℝ) *
      (nablaCovectorForm g eta c x v w + nablaCovectorForm g eta c x w v) := rfl

theorem deltaStarForm_basis (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (hDeta : DifferentiableAt ℝ (covectorInChart eta c) x)
    (i j : Fin 4) :
    deltaStarForm g eta c x (basisVector i) (basisVector j) = deltaStarInChart g eta c x i j := by
  simp only [deltaStarForm_apply, nablaCovectorForm_basis g eta c x hDeta, deltaStarInChart]

theorem deltaStarForm_eq (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (hDeta : DifferentiableAt ℝ (covectorInChart eta c) x) :
    deltaStarForm g eta c x = matrixToBilinear (deltaStarInChart g eta c x) := by
  rw [← matrixToBilinear_recover (deltaStarForm g eta c x)]
  congr 1
  funext i j
  exact deltaStarForm_basis g eta c x hDeta i j

theorem nablaCovectorForm_natural_between (g h : RawCov2 M) (eta theta : RawCovector M)
    (hg : IsMetric g) (hh : IsMetric h) (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (hy : F x ∈ (chartAt FourSpace d).target)
    (hgc : DifferentiableAt ℝ (cov2InChart g c) x)
    (hhd : DifferentiableAt ℝ (cov2InChart h d) (F x))
    (hetac : DifferentiableAt ℝ (covectorInChart eta c) x)
    (hthetad : DifferentiableAt ℝ (covectorInChart theta d) (F x))
    (hF : ContDiffAt ℝ 2 F x) (hJ : Function.Bijective (fderiv ℝ F x))
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart h d (F y)) (fderiv ℝ F y)))
    (hEta : covectorFormInChart eta c =ᶠ[𝓝 x]
      (fun y => (covectorFormInChart theta d (F y)).comp (fderiv ℝ F y))) (v w : FourSpace) :
    nablaCovectorForm g eta c x v w =
      nablaCovectorForm h theta d (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  simp only [nablaCovectorForm_apply]
  rw [fderiv_covector_pullback (covectorFormInChart theta d) (covectorFormInChart eta c) F x hF
    (covectorForm_differentiableAt theta d _ hthetad) (covectorForm_differentiableAt eta c x hetac) hEta]
  rw [hEta.self_of_nhds]
  simp only [ContinuousLinearMap.comp_apply,
    gammaForm_natural_between g h hg hh c d F x hx hy hgc hhd hF hJ hG, map_add]
  ring

theorem deltaStarForm_natural_between (g h : RawCov2 M) (eta theta : RawCovector M)
    (hg : IsMetric g) (hh : IsMetric h) (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (hy : F x ∈ (chartAt FourSpace d).target)
    (hgc : DifferentiableAt ℝ (cov2InChart g c) x)
    (hhd : DifferentiableAt ℝ (cov2InChart h d) (F x))
    (hetac : DifferentiableAt ℝ (covectorInChart eta c) x)
    (hthetad : DifferentiableAt ℝ (covectorInChart theta d) (F x))
    (hF : ContDiffAt ℝ 2 F x) (hJ : Function.Bijective (fderiv ℝ F x))
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart h d (F y)) (fderiv ℝ F y)))
    (hEta : covectorFormInChart eta c =ᶠ[𝓝 x]
      (fun y => (covectorFormInChart theta d (F y)).comp (fderiv ℝ F y))) (v w : FourSpace) :
    deltaStarForm g eta c x v w =
      deltaStarForm h theta d (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  simp only [deltaStarForm_apply,
    nablaCovectorForm_natural_between g h eta theta hg hh c d F x hx hy hgc hhd hetac hthetad hF hJ hG hEta]

end K24.Global.DeltaStarNaturality

/- Inlined checked module: PullbackRegularity.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.DeltaStarNaturality
open LieNaturality BianchiInvariance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem actionPullback_isMetric (rho : CircleAction M) (t : Circle) (g : RawCov2 M)
    (hg : IsMetric g) : IsMetric (actionPullbackCov2 rho t g) := by
  constructor
  · intro p v w
    exact hg.1 _ _ _
  · intro p v hv
    change 0 < g (rho.act t p) (mfderiv I4 I4 (rho.act t) p v) (mfderiv I4 I4 (rho.act t) p v)
    apply hg.2
    intro hzero
    apply hv
    exact (action_derivative_bijective rho t p).1 (hzero.trans (map_zero _).symm)

theorem actionPullback_cov2ContDiff (rho : CircleAction M) (t : Circle) (u : RawCov2 M)
    (hu : Cov2ContDiff 1 u) : Cov2ContDiff 1 (actionPullbackCov2 rho t u) := by
  intro c x hx
  let d := rho.act t ((chartAt FourSpace c).symm x)
  have hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source :=
    mem_chart_source FourSpace d
  have hy : actionInCharts rho t c d x ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hd
  have hF := actionInCharts_smooth rho t c d x hx hd
  have hA := (hu d (actionInCharts rho t c d x) hy).contDiffAt
    ((chartAt FourSpace d).open_target.mem_nhds hy)
  have hpull := CoverRegularityProof.contDiffAt_pullbackCoefficients (cov2InChart u d)
    (actionInCharts rho t c d) x 1 hA hF
  have heq : cov2InChart (actionPullbackCov2 rho t u) c =ᶠ[𝓝 x]
      CoverRegularityProof.pullbackCoefficients (cov2InChart u d) (actionInCharts rho t c d) := by
    filter_upwards [actionInCharts_form_eventually rho t u c d x hx hd] with y hy
    funext i j
    have h := congrArg (fun A : Form => A (basisVector i) (basisVector j)) hy
    simpa only [formInChart, Function.comp_apply, matrixToForm_basis, bilinearPullback_apply,
      CoverRegularityProof.pullbackCoefficients] using h
  exact (hpull.congr_of_eventuallyEq heq).contDiffWithinAt

theorem actionPullback_covectorContDiff (rho : CircleAction M) (t : Circle) (eta : RawCovector M)
    (heta : CovectorContDiff 1 eta) : CovectorContDiff 1 (actionPullbackCovector rho t eta) := by
  intro c x hx
  let d := rho.act t ((chartAt FourSpace c).symm x)
  have hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source :=
    mem_chart_source FourSpace d
  have hy : actionInCharts rho t c d x ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hd
  have hF := actionInCharts_smooth rho t c d x hx hd
  have hF1 : ContDiffAt ℝ 1 (actionInCharts rho t c d) x := hF.of_le (by decide)
  have hDF : ContDiffAt ℝ 1 (fderiv ℝ (actionInCharts rho t c d)) x :=
    hF.fderiv_right (by decide)
  have hEta := covectorForm_contDiffAt eta d (actionInCharts rho t c d x) 1
    ((heta d _ hy).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hy))
  have hpull := (hEta.comp x hF1).clm_comp hDF
  have hsource := hpull.congr_of_eventuallyEq
    (actionInCharts_covector_eventually rho t eta c d x hx hd)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  have hv : ContDiffAt ℝ 1 (fun y =>
      covectorFormInChart (actionPullbackCovector rho t eta) c y (basisVector i)) x :=
    hsource.clm_apply contDiffAt_const
  simpa only [covectorForm_basis] using hv

end K24.Global.DeltaStarNaturality

/- Inlined checked module: ChartRecovery.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.DeltaStarNaturality
open LieNaturality BianchiNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem cov2_differentiableAt (g : RawCov2 M) (hg : Cov2ContDiff 1 g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    DifferentiableAt ℝ (cov2InChart g c) x :=
  ((hg c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)

theorem covector_differentiableAt (eta : RawCovector M) (heta : CovectorContDiff 1 eta)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    DifferentiableAt ℝ (covectorInChart eta c) x :=
  ((heta c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)

theorem deltaStarForm_natural_inCharts (g : RawCov2 M) (eta : RawCovector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 1 g) (hDeta : CovectorContDiff 1 eta)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) (v w : FourSpace) :
    deltaStarForm g eta c x v w = deltaStarForm g eta d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) := by
  have hy := (chartAt FourSpace d).map_source hd
  exact deltaStarForm_natural_between g g eta eta hg hg c d (chartTransition c d) x hx hy
    (cov2_differentiableAt g hDg c x hx) (cov2_differentiableAt g hDg d _ hy)
    (covector_differentiableAt eta hDeta c x hx) (covector_differentiableAt eta hDeta d _ hy)
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
    (chartTransition_derivative_bijective c d x hx hd)
    (chartTransition_form_eventually g c d x hx hd)
    (chartTransition_covector_eventually eta c d x hx hd) v w

theorem cov2FromCoordinates_chart_value (a : M → FourSpace → Mat4) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (cov2FromCoordinates a) c x i j =
      matrixToBilinear (a ((chartAt FourSpace c).symm x)
        (chartAt FourSpace ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)))
        (fderiv ℝ (chartTransition c ((chartAt FourSpace c).symm x)) x (basisVector i))
        (fderiv ℝ (chartTransition c ((chartAt FourSpace c).symm x)) x (basisVector j)) := by
  rw [chartTransition_derivative c ((chartAt FourSpace c).symm x) x hx
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm x))]
  rfl

theorem deltaStar_chart_recovery (g : RawCov2 M) (eta : RawCovector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 1 g) (hDeta : CovectorContDiff 1 eta)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (deltaStar g eta) c x i j = deltaStarInChart g eta c x i j := by
  let p := (chartAt FourSpace c).symm x
  have hp : p ∈ (chartAt FourSpace p).source := mem_chart_source FourSpace p
  have hy : chartTransition c p x ∈ (chartAt FourSpace p).target := (chartAt FourSpace p).map_source hp
  change cov2InChart (cov2FromCoordinates (deltaStarInChart g eta)) c x i j = _
  rw [cov2FromCoordinates_chart_value (deltaStarInChart g eta) c x hx i j]
  change matrixToBilinear (deltaStarInChart g eta p (chartTransition c p x))
    (fderiv ℝ (chartTransition c p) x (basisVector i))
    (fderiv ℝ (chartTransition c p) x (basisVector j)) = _
  rw [← deltaStarForm_eq g eta p _ (covector_differentiableAt eta hDeta p _ hy),
    ← deltaStarForm_natural_inCharts g eta hg hDg hDeta c p x hx hp]
  exact deltaStarForm_basis g eta c x (covector_differentiableAt eta hDeta c x hx) i j

theorem deltaStar_eval_canonical (g : RawCov2 M) (eta : RawCovector M)
    (hDeta : CovectorContDiff 1 eta) (p : M) (v w : TangentSpace I4 p) :
    deltaStar g eta p v w = deltaStarForm g eta p (chartAt FourSpace p p)
      (mfderiv I4 I4 (chartAt FourSpace p) p v) (mfderiv I4 I4 (chartAt FourSpace p) p w) := by
  rw [deltaStarForm_eq g eta p _
    (covector_differentiableAt eta hDeta p _ (mem_chart_target FourSpace p))]
  rfl

end K24.Global.DeltaStarNaturality

/- Inlined checked module: ActionNaturality.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
namespace K24.Global.DeltaStarNaturality
open LieNaturality BianchiInvariance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem deltaStar_action_natural (rho : CircleAction M) (t : Circle)
    (g : RawCov2 M) (eta : RawCovector M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (hDeta : CovectorContDiff 1 eta) :
    deltaStar (actionPullbackCov2 rho t g) (actionPullbackCovector rho t eta) =
      actionPullbackCov2 rho t (deltaStar g eta) := by
  have hgP := actionPullback_isMetric rho t g hg
  have hDgP := actionPullback_cov2ContDiff rho t g hDg
  have hDetaP := actionPullback_covectorContDiff rho t eta hDeta
  ext p v w
  change deltaStar (actionPullbackCov2 rho t g) (actionPullbackCovector rho t eta) p v w =
    deltaStar g eta (rho.act t p) (mfderiv I4 I4 (rho.act t) p v) (mfderiv I4 I4 (rho.act t) p w)
  have hx := mem_chart_target FourSpace p
  have hp := mem_chart_source FourSpace p
  have hq := mem_chart_source FourSpace (rho.act t p)
  have hd : rho.act t ((chartAt FourSpace p).symm (chartAt FourSpace p p)) ∈
      (chartAt FourSpace (rho.act t p)).source := by
    rw [(chartAt FourSpace p).left_inv hp]
    exact hq
  have hy : actionInCharts rho t p (rho.act t p) (chartAt FourSpace p p) ∈
      (chartAt FourSpace (rho.act t p)).target := (chartAt FourSpace (rho.act t p)).map_source hd
  have h := deltaStarForm_natural_between (actionPullbackCov2 rho t g) g
    (actionPullbackCovector rho t eta) eta hgP hg p (rho.act t p)
    (actionInCharts rho t p (rho.act t p)) (chartAt FourSpace p p) hx hy
    (cov2_differentiableAt _ hDgP p _ hx) (cov2_differentiableAt g hDg _ _ hy)
    (covector_differentiableAt _ hDetaP p _ hx) (covector_differentiableAt eta hDeta _ _ hy)
    ((actionInCharts_smooth rho t p (rho.act t p) (chartAt FourSpace p p) hx hd).of_le (by decide))
    (actionInCharts_derivative_bijective rho t p (rho.act t p) (chartAt FourSpace p p) hx hd)
    (actionInCharts_form_eventually rho t g p (rho.act t p) (chartAt FourSpace p p) hx hd)
    (actionInCharts_covector_eventually rho t eta p (rho.act t p) (chartAt FourSpace p p) hx hd)
    (mfderiv I4 I4 (chartAt FourSpace p) p v) (mfderiv I4 I4 (chartAt FourSpace p) p w)
  rw [actionInCharts_comp_chart_differential rho t p (rho.act t p) p hp hq v,
    actionInCharts_comp_chart_differential rho t p (rho.act t p) p hp hq w] at h
  rw [deltaStar_eval_canonical _ _ hDetaP, deltaStar_eval_canonical _ _ hDeta]
  simpa only [actionInCharts, Function.comp_apply, (chartAt FourSpace p).left_inv hp] using h

end K24.Global.DeltaStarNaturality

set_option autoImplicit false
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open K24.Global
universe u

theorem K24.Global.deltaStar_chart_recovery_and_action_naturality_c1 :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (eta : RawCovector M),
      IsMetric g → Cov2ContDiff 1 g → CovectorContDiff 1 eta →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ i j : Fin 4, cov2InChart (deltaStar g eta) c x i j = deltaStarInChart g eta c x i j) ∧
      (∀ (rho : CircleAction M) (t : Circle),
        deltaStar (actionPullbackCov2 rho t g) (actionPullbackCovector rho t eta) =
          actionPullbackCov2 rho t (deltaStar g eta)) := by
  intro M _ _ _ g eta hg hDg hDeta
  exact ⟨fun c x hx i j => DeltaStarNaturality.deltaStar_chart_recovery g eta hg hDg hDeta c x hx i j,
    fun rho t => DeltaStarNaturality.deltaStar_action_natural rho t g eta hg hDg hDeta⟩

theorem solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (eta : RawCovector M),
      IsMetric g → Cov2ContDiff 1 g → CovectorContDiff 1 eta →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ i j : Fin 4, cov2InChart (deltaStar g eta) c x i j = deltaStarInChart g eta c x i j) ∧
      (∀ (rho : CircleAction M) (t : Circle),
        deltaStar (actionPullbackCov2 rho t g) (actionPullbackCovector rho t eta) =
          actionPullbackCov2 rho t (deltaStar g eta)) := @K24.Global.deltaStar_chart_recovery_and_action_naturality_c1

end
end
end
end
end
end
end
end
end
end
end

set_option pp.coercions false
