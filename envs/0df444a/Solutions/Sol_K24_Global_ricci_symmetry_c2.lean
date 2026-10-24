-- Prove2me | solution 1 for K24.Global.ricci_symmetry_c2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:30:37.20948+00:00
-- url     : https://prove2.me/submissions/2f212284-ff6b-4fb5-be3d-6bca7e4e6567

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.RicciCoverRegularitySupport

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

end K24.Global.RicciCoverRegularitySupport

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem ricci_cov2ContDiff_of_cover_coefficients (C : BoundedLocalCover M) (k : ℕ)
    (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u)
      (C.chart ν).innerDomain) : Cov2ContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy⟩ := C.exists_inner_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]
    exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, hinner, heq⟩ := RicciCoverRegularitySupport.local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]
    exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS hinner heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCov2 u) (S y) := by
    rw [hSx]
    exact (hu ν x hx).contDiffAt ((C.chart ν).innerOpen.mem_nhds hx)
  have hpull := RicciCoverRegularitySupport.contDiffAt_pullbackCoefficients _ S y k hA hS
  have hequal := RicciCoverRegularitySupport.pullbackCoefficients_eventually (C.chart ν) u q S y
    hS hinner heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

theorem ricci_cov2ContDiff_of_cov2Holder (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) :
    Cov2ContDiff k u := ricci_cov2ContDiff_of_cover_coefficients C k u hu.1

theorem ricci_cov2ContDiff_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff b.order g := by
  apply ricci_cov2ContDiff_of_cover_coefficients C b.order g
  intro ν
  exact (hg.regularity ν).1.mono (fun x hx =>
    (C.chart ν).closureInnerSubset (subset_closure hx))

end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
open Matrix
namespace K24.Global.RicciSymmetrySupport
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

theorem coordDeriv_differentiableAt (f : FourSpace → ℝ) (x : FourSpace)
    (hf : ContDiffAt ℝ 2 f x) (a : Fin 4) :
    DifferentiableAt ℝ (coordDeriv f a) x := by
  exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)

theorem coordDeriv_commute (f : FourSpace → ℝ) (x : FourSpace)
    (hf : ContDiffAt ℝ 2 f x) (a b : Fin 4) :
    coordDeriv (coordDeriv f b) a x = coordDeriv (coordDeriv f a) b x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold coordDeriv
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using (hf.isSymmSndFDerivAt (by norm_num)).eq (basisVector a) (basisVector b)

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

theorem nablaTensor_metric_zero [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    nablaTensorInChart g g c x a b d = 0 := by
  have hs (i j : Fin 4) : (fun y => cov2InChart g c y i j) =
      (fun y => cov2InChart g c y j i) := funext (fun y => hg.1 _ _ _)
  have h1 := christoffel_lower g hg c x hx a b d
  have h2 := christoffel_lower g hg c x hx a d b
  rw [hs d b] at h2
  have hsum : (∑ p, christoffelInChart g c x p a d * cov2InChart g c x p b) =
      ∑ p, christoffelInChart g c x p a d * cov2InChart g c x b p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [cov2InChart_symmetric g hg.1 c x p b]
  rw [hsum] at h2
  unfold nablaTensorInChart
  linarith


theorem christoffel_differentiableAt [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x) (d a b : Fin 4) :
    DifferentiableAt ℝ (fun y => christoffelInChart g c y d a b) x := by
  have hentry (i j : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hDg i) j
  have hInv := differentiableAt_inverseMetric g hg c x hx
    (hDg.differentiableAt (by norm_num))
  unfold christoffelInChart
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro p _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hInv d) p).mul
    (((coordDeriv_differentiableAt _ x (hentry b p) a).add
      (coordDeriv_differentiableAt _ x (hentry a p) b)).sub
      (coordDeriv_differentiableAt _ x (hentry a b) p))

end K24.Global.RicciSymmetrySupport

namespace K24.Global.RicciSymmetryProof
open Matrix RicciSymmetrySupport
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def matrixD (A : FourSpace → Mat4) (i : Fin 4) (x : FourSpace) : Mat4 :=
  fun a b => coordDeriv (fun y => A y a b) i x

theorem matrixD_congr (A B : FourSpace → Mat4) (i : Fin 4) (x : FourSpace)
    (h : A =ᶠ[𝓝 x] B) : matrixD A i x = matrixD B i x := by
  ext a b
  have hab : (fun y => A y a b) =ᶠ[𝓝 x] (fun y => B y a b) :=
    h.mono fun y hy => congrFun (congrFun hy a) b
  exact congrArg (fun D : FourSpace →L[ℝ] ℝ => D (basisVector i)) hab.fderiv_eq

theorem matrixD_add (A B : FourSpace → Mat4) (i : Fin 4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    matrixD (fun y => A y + B y) i x = matrixD A i x + matrixD B i x := by
  ext a b
  change fderiv ℝ (fun y => A y a b + B y a b) x (basisVector i) = _
  rw [fderiv_fun_add (differentiableAt_pi.mp (differentiableAt_pi.mp hA a) b)
    (differentiableAt_pi.mp (differentiableAt_pi.mp hB a) b)]
  rfl

theorem matrixD_transpose (A : FourSpace → Mat4) (i : Fin 4) (x : FourSpace) :
    matrixD (fun y => (A y)ᵀ) i x = (matrixD A i x)ᵀ := rfl

theorem matrixD_mul (A B : FourSpace → Mat4) (i : Fin 4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    matrixD (fun y => A y * B y) i x = matrixD A i x * B x + A x * matrixD B i x := by
  ext a b
  have hAa (p : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hA a) p
  have hBb (p : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hB p) b
  change fderiv ℝ (fun y => ∑ p, A y a p * B y p b) x (basisVector i) = _
  rw [fderiv_fun_sum (A := fun p y => A y a p * B y p b)
    (u := Finset.univ) (fun p _ => (hAa p).mul (hBb p))]
  simp only [_root_.sum_apply, Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [fderiv_fun_mul (hAa p) (hBb p)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, matrixD, coordDeriv]
  ring

theorem diff_transpose (A : FourSpace → Mat4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) : DifferentiableAt ℝ (fun y => (A y)ᵀ) x := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  exact differentiableAt_pi.mp (differentiableAt_pi.mp hA b) a

theorem diff_mul (A B : FourSpace → Mat4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => A y * B y) x := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  change DifferentiableAt ℝ (fun y => ∑ p, A y a p * B y p b) x
  apply DifferentiableAt.fun_sum
  intro p _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hA a) p).mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp hB p) b)

def gamma (g : RawCov2 M) (c : M) (a : Fin 4) (x : FourSpace) : Mat4 :=
  fun b d => christoffelInChart g c x b a d

theorem matrix_metric_compatibility [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a : Fin 4) :
    matrixD (cov2InChart g c) a x =
      (gamma g c a x)ᵀ * cov2InChart g c x + cov2InChart g c x * gamma g c a x := by
  ext b d
  have h := nablaTensor_metric_zero g hg c x hx a b d
  simp only [nablaTensorInChart] at h
  change _ = (∑ p, christoffelInChart g c x p a b * cov2InChart g c x p d) +
    ∑ p, cov2InChart g c x b p * christoffelInChart g c x p a d
  simp_rw [mul_comm (cov2InChart g c x b _) (christoffelInChart g c x _ a d)]
  change coordDeriv (fun y => cov2InChart g c y b d) a x = _
  linarith

theorem gamma_differentiable [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x) (a : Fin 4) :
    DifferentiableAt ℝ (gamma g c a) x := by
  apply differentiableAt_pi.mpr
  intro b
  apply differentiableAt_pi.mpr
  intro d
  exact christoffel_differentiableAt g hg c x hx hDg b a d

theorem matrix_second_deriv [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x) (a b : Fin 4) :
    matrixD (matrixD (cov2InChart g c) b) a x =
      (matrixD (gamma g c b) a x)ᵀ * cov2InChart g c x +
      (gamma g c b x)ᵀ * matrixD (cov2InChart g c) a x +
      (matrixD (cov2InChart g c) a x * gamma g c b x +
      cov2InChart g c x * matrixD (gamma g c b) a x) := by
  have heq : matrixD (cov2InChart g c) b =ᶠ[𝓝 x]
      (fun y => (gamma g c b y)ᵀ * cov2InChart g c y + cov2InChart g c y * gamma g c b y) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    exact matrix_metric_compatibility g hg c y hy b
  rw [matrixD_congr _ _ a x heq]
  have hG := gamma_differentiable g hg c x hx hDg b
  have hD := hDg.differentiableAt (by norm_num)
  rw [matrixD_add _ _ a x (diff_mul _ _ x (diff_transpose _ _ hG) hD)
    (diff_mul _ _ x hD hG), matrixD_mul _ _ a x (diff_transpose _ _ hG) hD,
    matrixD_mul _ _ a x hD hG, matrixD_transpose]

theorem curvature_matrix_skew [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x) (a b : Fin 4) :
    let R : Mat4 := fun l k => curvatureInChart g c x l a b k
    Rᵀ * cov2InChart g c x + cov2InChart g c x * R = 0 := by
  have hcomm : matrixD (matrixD (cov2InChart g c) b) a x =
      matrixD (matrixD (cov2InChart g c) a) b x := by
    ext i j
    exact coordDeriv_commute _ x (contDiffAt_pi.mp (contDiffAt_pi.mp hDg i) j) a b
  rw [matrix_second_deriv g hg c x hx hDg a b,
    matrix_second_deriv g hg c x hx hDg b a,
    matrix_metric_compatibility g hg c x hx a,
    matrix_metric_compatibility g hg c x hx b] at hcomm
  have hR : (fun l k => curvatureInChart g c x l a b k) =
      matrixD (gamma g c b) a x - matrixD (gamma g c a) b x +
      gamma g c a x * gamma g c b x - gamma g c b x * gamma g c a x := by
    ext l k
    simp only [curvatureInChart, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      matrixD, gamma, Finset.sum_sub_distrib]
    ring
  dsimp only
  rw [hR]
  simp only [transpose_add, transpose_sub, transpose_mul]
  linear_combination (norm := noncomm_ring) hcomm


theorem trace_of_metric_skew (G R : Mat4) (hG : IsUnit G.det)
    (hR : Rᵀ * G + G * R = 0) : R.trace = 0 := by
  have h := congrArg (fun A : Mat4 => (G⁻¹ * A).trace) hR
  have hfirst : (G⁻¹ * (Rᵀ * G)).trace = R.trace := by
    rw [Matrix.trace_mul_cycle' , ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.one_mul, Matrix.trace_transpose]
  rw [Matrix.mul_add, Matrix.trace_add, hfirst,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul,
    Matrix.mul_zero, Matrix.trace_zero] at h
  linarith

theorem curvature_trace_zero [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x) (a b : Fin 4) :
    (∑ k : Fin 4, curvatureInChart g c x k a b k) = 0 := by
  exact trace_of_metric_skew (cov2InChart g c x)
    (fun l k => curvatureInChart g c x l a b k)
    (cov2InChart_isUnit_det g hg c x hx) (curvature_matrix_skew g hg c x hx hDg a b)

theorem ricci_antisymmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (a b : Fin 4) :
    ricciInChart g c x a b - ricciInChart g c x b a =
      -(∑ k : Fin 4, curvatureInChart g c x k a b k) := by
  have hG := christoffel_symmetric g hg c
  have hd (l i j k : Fin 4) :
      coordDeriv (fun y => christoffelInChart g c y l i j) k x =
      coordDeriv (fun y => christoffelInChart g c y l j i) k x := by
    rw [show (fun y => christoffelInChart g c y l i j) =
      (fun y => christoffelInChart g c y l j i) from funext (fun y => hG y l i j)]
  have hterm (k : Fin 4) :
      curvatureInChart g c x k k a b - curvatureInChart g c x k k b a =
        -curvatureInChart g c x k a b k := by
    unfold curvatureInChart
    rw [hd k a b k, hd k k b a, hd k k a b]
    have hsum : (∑ p : Fin 4,
        (christoffelInChart g c x k k p * christoffelInChart g c x p a b -
          christoffelInChart g c x k a p * christoffelInChart g c x p k b)) -
      (∑ p : Fin 4,
        (christoffelInChart g c x k k p * christoffelInChart g c x p b a -
          christoffelInChart g c x k b p * christoffelInChart g c x p k a)) =
      -(∑ p : Fin 4,
        (christoffelInChart g c x k a p * christoffelInChart g c x p b k -
          christoffelInChart g c x k b p * christoffelInChart g c x p a k)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [hG x p a b, hG x p k b, hG x p k a]
      ring
    linarith
  unfold ricciInChart
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => hterm k)

theorem ricci_symmetric_at [IsManifold I4 ∞ M]
    (z : RawCov2 M) (hz : IsMetric z) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x) (i j : Fin 4) :
    ricciInChart z c x i j = ricciInChart z c x j i := by
  have h := ricci_antisymmetric z hz.1 c x i j
  rw [curvature_trace_zero z hz c x hx hDz i j] at h
  linarith

end K24.Global.RicciSymmetryProof

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem ricciInChart_symmetric [IsManifold I4 ∞ M]
    (z : RawCov2 M) (hz : IsMetric z) (hDz : Cov2ContDiff 2 z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ricciInChart z c x i j = ricciInChart z c x j i := by
  exact RicciSymmetryProof.ricci_symmetric_at z hz c x hx
    ((hDz c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)) i j

theorem ricciInChart_symmetric_of_metricAdmissible [IsManifold I4 ∞ M]
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C b z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ricciInChart z c x i j = ricciInChart z c x j i := by
  apply ricciInChart_symmetric z hz.metric _ c x hx i j
  intro q y hy
  exact (ricci_cov2ContDiff_of_metricAdmissible C b z hz q y hy).of_le
    (by exact_mod_cast b.order_ge_two)

end K24.Global

open K24.Global in
theorem solution :
  ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M],
    ∀ (z : RawCov2 M), IsMetric z → Cov2ContDiff 2 z →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ i j : Fin 4, ricciInChart z c x i j = ricciInChart z c x j i := by
  intro M _ _ _ z hz hDz c x hx i j
  exact ricciInChart_symmetric z hz hDz c x hx i j
