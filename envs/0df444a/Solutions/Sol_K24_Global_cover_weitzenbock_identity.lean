-- Prove2me | solution 1 for K24.Global.cover_weitzenbock_identity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:36:26.508042+00:00
-- url     : https://prove2.me/submissions/bc4f227b-525f-4524-bbf9-bed50d558da9

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

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


namespace K24.Global.VectorCovectorCoverRegularityProof
open CoverRegularityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}
def vectorCoefficients (A : FourSpace → FourSpace) (T S : FourSpace → FourSpace)
    (y : FourSpace) : FourSpace := fderiv ℝ T (S y) (A (S y))

theorem contDiffAt_vectorCoefficients (A T S : FourSpace → FourSpace)
    (y : FourSpace) (k : ℕ) (hA : ContDiffAt ℝ k A (S y))
    (hT : ContDiffAt ℝ ∞ T (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (vectorCoefficients A T S) y := by
  have hd : ContDiffAt ℝ k (fderiv ℝ T) (S y) :=
    hT.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hSk : ContDiffAt ℝ k S y := hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  exact (hd.comp y hSk).clm_apply (hA.comp y hSk)

theorem vectorCoefficients_eventually (c : LocalCoverChart F) (Y : RawVector M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hy : y ∈ (chartAt FourSpace q).target)
    (hinner : ∀ᶠ z in 𝓝 y, S z ∈ c.innerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    vectorCoefficients (c.liftedVector Y) ((chartAt FourSpace q) ∘ c.lift) S
      =ᶠ[𝓝 y] vectorInChart Y q := by
  filter_upwards [hinner, heq, (chartAt FourSpace q).open_target.mem_nhds hy] with z hz heqz hzt
  have hzo : S z ∈ c.outerDomain := c.closureInnerSubset (subset_closure hz)
  have hq : c.lift (S z) ∈ (chartAt FourSpace q).source := by
    rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz]
    exact (chartAt FourSpace q).map_target hzt
  have hd := mfderiv_comp (I := I4) (I' := I4) (I'' := I4) (S z)
    ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
    ((contMDiffAt_lift c (S z) hzo).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ ((chartAt FourSpace q) ∘ c.lift) (S z) (c.liftedVector Y (S z)) = _
  rw [hd]
  change mfderiv I4 I4 (chartAt FourSpace q) (c.lift (S z))
    (mfderiv I4 I4 c.lift (S z) (c.liftedVector Y (S z))) = _
  rw [c.differential_liftedVector Y (S z) hzo]
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz]
  rfl
end K24.Global.VectorCovectorCoverRegularityProof

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem vectorContDiff_of_cover_coefficients (C : BoundedLocalCover M) (k : ℕ)
    (Y : RawVector M)
    (hY : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector Y) (C.chart ν).innerDomain) :
    VectorContDiff k Y := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy⟩ := C.exists_inner_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]; exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, hinner, heq⟩ := CoverRegularityProof.local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]; exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS hinner heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedVector Y) (S y) := by
    rw [hSx]; exact (hY ν x hx).contDiffAt ((C.chart ν).innerOpen.mem_nhds hx)
  have hT : ContDiffAt ℝ ∞ ((chartAt FourSpace q) ∘ (C.chart ν).lift) (S y) := by
    rw [hSx]
    exact CoverRegularityProof.transition_smooth (C.chart ν) q x
      ((C.chart ν).closureInnerSubset (subset_closure hx)) hq
  have hpull := VectorCovectorCoverRegularityProof.contDiffAt_vectorCoefficients _ _ S y k hA hT hS
  have hequal := VectorCovectorCoverRegularityProof.vectorCoefficients_eventually
    (C.chart ν) Y q S y hy hinner heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
open Matrix
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

theorem lieTensorInChart_covariant [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (Y : RawVector M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (i j : Fin 4) :
    lieTensorInChart Y g c x i j =
      (∑ p : Fin 4, cov2InChart g c x p j * nablaVectorInChart g Y c x i p) +
      (∑ p : Fin 4, cov2InChart g c x i p * nablaVectorInChart g Y c x j p) := by
  have hD (a : Fin 4) : coordDeriv (fun y => cov2InChart g c y i j) a x =
      (∑ p, christoffelInChart g c x p a i * cov2InChart g c x p j) +
      (∑ p, christoffelInChart g c x p a j * cov2InChart g c x i p) := by
    have h := nablaTensor_metric_zero g hg c x hx a i j
    unfold nablaTensorInChart at h
    linarith
  have hleft :
      (∑ a, vectorInChart Y c x a * ∑ p, christoffelInChart g c x p a i * cov2InChart g c x p j) =
      ∑ p, cov2InChart g c x p j * ∑ a, christoffelInChart g c x p i a * vectorInChart Y c x a := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro a _
    rw [christoffel_symmetric g hg.1 c x p a i]
    ring
  have hright :
      (∑ a, vectorInChart Y c x a * ∑ p, christoffelInChart g c x p a j * cov2InChart g c x i p) =
      ∑ p, cov2InChart g c x i p * ∑ a, christoffelInChart g c x p j a * vectorInChart Y c x a := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro a _
    rw [christoffel_symmetric g hg.1 c x p a j]
    ring
  simp only [lieTensorInChart, hD, nablaVectorInChart, mul_add,
    Finset.sum_add_distrib]
  rw [hleft, hright]
  have hswap (k l : Fin 4) :
      (∑ p, coordDeriv (fun y => vectorInChart Y c y p) k x * cov2InChart g c x p l) =
      ∑ p, cov2InChart g c x p l * coordDeriv (fun y => vectorInChart Y c y p) k x := by
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hswap i j]
  have hswap2 :
      (∑ p, coordDeriv (fun y => vectorInChart Y c y p) j x * cov2InChart g c x i p) =
      ∑ p, cov2InChart g c x i p * coordDeriv (fun y => vectorInChart Y c y p) j x := by
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hswap2]
  ring

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

theorem coordDeriv_nablaVector (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hG : ∀ d a b : Fin 4,
      DifferentiableAt ℝ (fun y => christoffelInChart g c y d a b) x)
    (hY : ∀ d : Fin 4, ContDiffAt ℝ 2 (fun y => vectorInChart Y c y d) x)
    (a b d : Fin 4) :
    coordDeriv (fun y => nablaVectorInChart g Y c y b d) a x =
      coordDeriv (coordDeriv (fun y => vectorInChart Y c y d) b) a x +
      ∑ p : Fin 4,
        (coordDeriv (fun y => christoffelInChart g c y d b p) a x * vectorInChart Y c x p +
          christoffelInChart g c x d b p * coordDeriv (fun y => vectorInChart Y c y p) a x) := by
  have hprod (p : Fin 4) := (hG d b p).mul ((hY p).differentiableAt (by norm_num))
  have hsum : DifferentiableAt ℝ (fun y =>
      ∑ p : Fin 4, christoffelInChart g c y d b p * vectorInChart Y c y p) x :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => hprod p)
  unfold nablaVectorInChart
  change fderiv ℝ (fun y => coordDeriv (fun z => vectorInChart Y c z d) b y +
    ∑ p : Fin 4, christoffelInChart g c y d b p * vectorInChart Y c y p) x (basisVector a) = _
  rw [fderiv_fun_add (coordDeriv_differentiableAt _ x (hY d) b)
    hsum]
  simp only [_root_.add_apply]
  congr 1
  rw [fderiv_fun_sum (A := fun p y => christoffelInChart g c y d b p * vectorInChart Y c y p)
    (u := Finset.univ) (fun p _ => hprod p)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [fderiv_fun_mul (hG d b p) ((hY p).differentiableAt (by norm_num))]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, coordDeriv]
  ring

theorem commutator_algebra
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dG : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (V : Fin 4 → ℝ) (dV : Fin 4 → Fin 4 → ℝ)
    (ddV : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hG : ∀ d a b, G d a b = G d b a)
    (hV : ∀ a b d, ddV a b d = ddV b a d) (a b d : Fin 4) :
    (ddV a b d + ∑ p, (dG a d b p * V p + G d b p * dV a p)) +
        (∑ p, G d a p * (dV b p + ∑ q, G p b q * V q)) -
        (∑ p, G p a b * (dV p d + ∑ q, G d p q * V q)) -
      ((ddV b a d + ∑ p, (dG b d a p * V p + G d a p * dV b p)) +
        (∑ p, G d b p * (dV a p + ∑ q, G p a q * V q)) -
        (∑ p, G p b a * (dV p d + ∑ q, G d p q * V q))) =
      ∑ p, (dG a d b p - dG b d a p +
        ∑ q, (G d a q * G q b p - G d b q * G q a p)) * V p := by
  have hquad (i j : Fin 4) :
      (∑ p, G d i p * ∑ q, G p j q * V q) =
        ∑ p, (∑ q, G d i q * G q j p) * V p := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp only [hV a b d, hG _ b a, mul_add, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hquad a b, hquad b a]
  ring

theorem secondNabla_commutator_of_differentiableAt
    (g : RawCov2 M) (hg : IsSymmetricCov2 g) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hG : ∀ d a b : Fin 4,
      DifferentiableAt ℝ (fun y => christoffelInChart g c y d a b) x)
    (hY : ∀ d : Fin 4, ContDiffAt ℝ 2 (fun y => vectorInChart Y c y d) x)
    (a b d : Fin 4) :
    secondNablaVectorInChart g Y c x a b d -
      secondNablaVectorInChart g Y c x b a d =
        ∑ p : Fin 4, curvatureInChart g c x d a b p * vectorInChart Y c x p := by
  unfold secondNablaVectorInChart
  rw [coordDeriv_nablaVector g Y c x hG hY, coordDeriv_nablaVector g Y c x hG hY]
  simp only [nablaVectorInChart, curvatureInChart]
  exact commutator_algebra (christoffelInChart g c x)
    (fun i k j p => coordDeriv (fun y => christoffelInChart g c y k j p) i x)
    (fun p => vectorInChart Y c x p)
    (fun i p => coordDeriv (fun y => vectorInChart Y c y p) i x)
    (fun i j k => coordDeriv (coordDeriv (fun y => vectorInChart Y c y k) j) i x)
    (christoffel_symmetric g hg c x)
    (fun i j k => coordDeriv_commute _ x (hY k) i j) a b d

theorem secondNabla_commutator_of_contDiffAt [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (Y : RawVector M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x)
    (hY : ContDiffAt ℝ 2 (vectorInChart Y c) x) (a b d : Fin 4) :
    secondNablaVectorInChart g Y c x a b d -
      secondNablaVectorInChart g Y c x b a d =
        ∑ p : Fin 4, curvatureInChart g c x d a b p * vectorInChart Y c x p := by
  apply secondNabla_commutator_of_differentiableAt g hg.1 Y c x
  · exact christoffel_differentiableAt g hg c x hx hDg
  · intro p
    exact (coordProj p).contDiff.contDiffAt.comp x hY

end K24.Global.IdentityProof

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem secondNablaVector_commutator_of_holder
    (C : BoundedLocalCover M) (bounds : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C bounds z)
    (Y : RawVector M) (hY : C.VectorHolder 2 bounds.exponent.value Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (a b d : Fin 4) :
    secondNablaVectorInChart z Y c x a b d -
      secondNablaVectorInChart z Y c x b a d =
        ∑ p : Fin 4, curvatureInChart z c x d a b p * vectorInChart Y c x p := by
  have hDz : ContDiffOn ℝ 2 (cov2InChart z c) (chartAt FourSpace c).target :=
    (cov2ContDiff_of_metricAdmissible C bounds z hz c).of_le
      (by exact_mod_cast bounds.order_ge_two)
  have hDY := vectorContDiff_of_cover_coefficients C 2 Y hY.1 c
  exact IdentityProof.secondNabla_commutator_of_contDiffAt z hz.metric Y c x hx
    ((hDz x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx))
    ((hDY x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)) a b d

theorem ricci_commutator_of_holder
    (C : BoundedLocalCover M) (bounds : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C bounds z)
    (Y : RawVector M) (hY : C.VectorHolder 2 bounds.exponent.value Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    (∑ a : Fin 4, secondNablaVectorInChart z Y c x a j a) -
      (∑ a : Fin 4, secondNablaVectorInChart z Y c x j a a) =
        ∑ p : Fin 4, ricciInChart z c x j p * vectorInChart Y c x p := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [secondNablaVector_commutator_of_holder C bounds z hz Y hY c x hx]
  rw [Finset.sum_comm]
  simp only [ricciInChart, Finset.sum_mul]

theorem secondNablaVector_commutator
    (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M]
    (C : BoundedLocalCover M) (bounds : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C bounds z)
    (Y : RawVector M) (hY : C.VectorHolder 2 bounds.exponent.value Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (a b d : Fin 4) :
    secondNablaVectorInChart z Y c x a b d -
      secondNablaVectorInChart z Y c x b a d =
        ∑ p : Fin 4, curvatureInChart z c x d a b p * vectorInChart Y c x p :=
  secondNablaVector_commutator_of_holder C bounds z hz Y hY c x hx a b d

end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.LieNaturality
abbrev Form := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

abbrev matrixToForm : Mat4 → Form := matrixToBilinear

@[simp] theorem matrixToForm_apply (A : Mat4) : matrixToForm A = matrixToBilinear A := rfl

def lieForm (A : FourSpace → Form) (V : FourSpace → FourSpace) (x : FourSpace) : Form :=
  fderiv ℝ A x (V x) + (A x).comp (fderiv ℝ V x) +
    (ContinuousLinearMap.precomp ℝ (fderiv ℝ V x)).comp (A x)

@[simp] theorem lieForm_apply (A : FourSpace → Form) (V : FourSpace → FourSpace)
    (x u v : FourSpace) :
    lieForm A V x u v = fderiv ℝ A x (V x) u v +
      A x (fderiv ℝ V x u) v + A x u (fderiv ℝ V x v) := rfl

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

theorem lieForm_natural (A B : FourSpace → Form) (U V F : FourSpace → FourSpace)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B x)
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V (F x))
    (hmetric : B =ᶠ[𝓝 x] (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y)))
    (hvector : (fun y => fderiv ℝ F y (U y)) =ᶠ[𝓝 x] V ∘ F) :
    lieForm B U x = bilinearPullback (lieForm A V (F x)) (fderiv ℝ F x) := by
  have hF1 : DifferentiableAt ℝ F x := hF.differentiableAt (by norm_num)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hF.isSymmSndFDerivAt (by norm_num)
  have hrelation (t : FourSpace) :
      fderiv ℝ (fderiv ℝ F) x (U x) t + fderiv ℝ F x (fderiv ℝ U x t) =
        fderiv ℝ V (F x) (fderiv ℝ F x t) := by
    have h := congrArg (fun D : FourSpace →L[ℝ] FourSpace => D t) hvector.fderiv_eq
    rw [fderiv_clm_apply hDF hU, fderiv_comp x hV hF1] at h
    simpa only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, hsym.eq t (U x), add_comm] using h
  ext u v
  have hmetricEval : (fun y => B y u v) =ᶠ[𝓝 x]
      (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y) u v) :=
    hmetric.mono (fun y hy => congrArg (fun Q : Form => Q u v) hy)
  have hmetricD := hmetricEval.fderiv_eq (𝕜 := ℝ)
  have hdiff := congrArg (fun D : FourSpace →L[ℝ] ℝ => D (U x)) hmetricD
  rw [fderiv_form_const B x (U x) u v hB] at hdiff
  change fderiv ℝ B x (U x) u v =
    fderiv ℝ (fun y => A (F y) (fderiv ℝ F y u) (fderiv ℝ F y v)) x (U x) at hdiff
  rw [fderiv_form_apply (fun y => A (F y)) (fun y => fderiv ℝ F y u) (fun y => fderiv ℝ F y v)
    x (U x) (DifferentiableAt.comp (f := F) (g := A) x hA hF1) (hDF.clm_apply (differentiableAt_const _))
      (hDF.clm_apply (differentiableAt_const _)), fderiv_fun_comp (f := F) (g := A) x hA hF1,
      fderiv_derivative_apply F x (U x) u hDF,
      fderiv_derivative_apply F x (U x) v hDF] at hdiff
  simp only [ContinuousLinearMap.comp_apply] at hdiff
  have hu := congrArg (fun t => A (F x) t (fderiv ℝ F x v)) (hrelation u)
  have hv := congrArg (fun t => A (F x) (fderiv ℝ F x u) t) (hrelation v)
  simp only [map_add, _root_.add_apply] at hu hv
  simp only [lieForm_apply, bilinearPullback_apply]
  rw [hmetric.self_of_nhds]
  simp only [bilinearPullback_apply]
  have hvectorAt : fderiv ℝ F x (U x) = V (F x) := hvector.self_of_nhds
  rw [hdiff, hvectorAt]
  linarith


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

theorem coordDeriv_vector_component (V : FourSpace → FourSpace) (x : FourSpace)
    (hV : DifferentiableAt ℝ V x) (a p : Fin 4) :
    coordDeriv (fun y => V y p) a x = (fderiv ℝ V x (basisVector a)) p := by
  change fderiv ℝ ((coordProj p) ∘ V) x (basisVector a) = _
  rw [fderiv_comp x (coordProj p).differentiableAt hV, (coordProj p).fderiv]
  rfl

theorem lieTensorInChart_form (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hg : DifferentiableAt ℝ (cov2InChart g c) x)
    (hY : DifferentiableAt ℝ (vectorInChart Y c) x) :
    matrixToForm (lieTensorInChart Y g c x) =
      lieForm (formInChart g c) (vectorInChart Y c) x := by
  have hform := formInChart_differentiableAt g c x hg
  have hD (p i j : Fin 4) :
      fderiv ℝ (formInChart g c) x (basisVector p) (basisVector i) (basisVector j) =
        coordDeriv (fun y => cov2InChart g c y i j) p x := by
    rw [← fderiv_form_const _ x (basisVector p) (basisVector i) (basisVector j) hform]
    have heq : (fun y => formInChart g c y (basisVector i) (basisVector j)) =
        (fun y => cov2InChart g c y i j) := by
      funext y
      exact matrixToForm_basis _ i j
    rw [heq]
    rfl
  have hfirst (i j : Fin 4) :
      fderiv ℝ (formInChart g c) x (vectorInChart Y c x) (basisVector i) (basisVector j) =
        ∑ p : Fin 4, vectorInChart Y c x p * coordDeriv (fun y => cov2InChart g c y i j) p x := by
    calc
      _ = fderiv ℝ (formInChart g c) x
          (∑ p, vectorInChart Y c x p • basisVector p) (basisVector i) (basisVector j) := by
        rw [sum_basisVector]
      _ = _ := by simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, hD]
  have hsecond (a i j : Fin 4) :
      formInChart g c x (fderiv ℝ (vectorInChart Y c) x (basisVector a)) (basisVector j) =
        ∑ p : Fin 4, coordDeriv (fun y => vectorInChart Y c y p) a x * cov2InChart g c x p j := by
    calc
      _ = formInChart g c x (∑ p,
          (fderiv ℝ (vectorInChart Y c) x (basisVector a)) p • basisVector p) (basisVector j) := by
        rw [sum_basisVector]
      _ = _ := by
        simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
          formInChart, Function.comp_apply, matrixToForm_basis,
          coordDeriv_vector_component _ x hY]
  have hthird (a i : Fin 4) :
      formInChart g c x (basisVector i) (fderiv ℝ (vectorInChart Y c) x (basisVector a)) =
        ∑ p : Fin 4, coordDeriv (fun y => vectorInChart Y c y p) a x * cov2InChart g c x i p := by
    calc
      _ = formInChart g c x (basisVector i) (∑ p,
          (fderiv ℝ (vectorInChart Y c) x (basisVector a)) p • basisVector p) := by
        rw [sum_basisVector]
      _ = _ := by
        simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
          formInChart, Function.comp_apply, matrixToForm_basis,
          coordDeriv_vector_component _ x hY]
  change matrixToBilinear _ = _
  rw [← matrixToBilinear_recover (lieForm (formInChart g c) (vectorInChart Y c) x)]
  congr 1
  funext i j
  simp only [lieForm_apply, hfirst, hsecond i i j, hthird j i,
    lieTensorInChart, Finset.sum_add_distrib]

end K24.Global.LieNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.LieNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

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

theorem chartTransition_vector (Y : RawVector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (chartTransition c d) x (vectorInChart Y c x) =
      vectorInChart Y d (chartTransition c d x) := by
  rw [chartTransition_derivative c d x hx hd]
  have hcancel := congrArg (fun D => D (Y ((chartAt FourSpace c).symm x)))
    ((mdifferentiable_chart (I := I4) c).symm_comp_deriv
      ((chartAt FourSpace c).map_target hx))
  have hright := (chartAt FourSpace c).right_inv hx
  rw [hright] at hcancel
  change mfderiv I4 I4 (chartAt FourSpace c).symm x
      (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
        (Y ((chartAt FourSpace c).symm x))) = Y ((chartAt FourSpace c).symm x) at hcancel
  change mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x
        (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
          (Y ((chartAt FourSpace c).symm x)))) =
    mfderiv I4 I4 (chartAt FourSpace d)
      ((chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x)))
      (Y ((chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x))))
  rw [hcancel, (chartAt FourSpace d).left_inv hd]

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

end K24.Global.LieNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.LieNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem lieTensorInChart_transition (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hY : VectorContDiff 1 Y)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    matrixToForm (lieTensorInChart Y g c x) =
      bilinearPullback (matrixToForm (lieTensorInChart Y g d (chartTransition c d x)))
        (fderiv ℝ (chartTransition c d) x) := by
  have hxd : chartTransition c d x ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hd
  have hgc := ((hg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd := ((hg d _ hxd).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hxd)).differentiableAt (by norm_num)
  have hYc := ((hY c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)
  have hYd := ((hY d _ hxd).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hxd)).differentiableAt (by norm_num)
  rw [lieTensorInChart_form g Y c x hgc hYc,
    lieTensorInChart_form g Y d _ hgd hYd]
  have hF2 : ContDiffAt ℝ 2 (chartTransition c d) x :=
    (chartTransition_smooth c d x hx hd).of_le (by decide)
  apply lieForm_natural _ _ _ _ _ x hF2
    (formInChart_differentiableAt g d _ hgd) (formInChart_differentiableAt g c x hgc) hYc hYd
  · filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
    exact chartTransition_form g c d y hy.1 hy.2
  · filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
    exact chartTransition_vector Y c d y hy.1 hy.2

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

theorem lieTensor_eq_chart (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hY : VectorContDiff 1 Y)
    (c p : M) (hp : p ∈ (chartAt FourSpace c).source) :
    lieTensor Y g p = cov2FromChartAt c p (lieTensorInChart Y g c (chartAt FourSpace c p)) := by
  have hdp : (chartAt FourSpace c).symm (chartAt FourSpace c p) ∈ (chartAt FourSpace p).source := by
    rw [(chartAt FourSpace c).left_inv hp]
    exact mem_chart_source FourSpace p
  have h := lieTensorInChart_transition g Y hg hY c p (chartAt FourSpace c p)
    ((chartAt FourSpace c).map_source hp) hdp
  have hbase : chartTransition c p (chartAt FourSpace c p) = chartAt FourSpace p p := by
    change chartAt FourSpace p ((chartAt FourSpace c).symm (chartAt FourSpace c p)) = _
    rw [(chartAt FourSpace c).left_inv hp]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have heval := congrArg (fun Q : Form =>
      Q (mfderiv I4 I4 (chartAt FourSpace c) p v) (mfderiv I4 I4 (chartAt FourSpace c) p w)) h
  change matrixToForm (lieTensorInChart Y g c (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c) p v) (mfderiv I4 I4 (chartAt FourSpace c) p w) =
    matrixToForm (lieTensorInChart Y g p (chartTransition c p (chartAt FourSpace c p)))
      (fderiv ℝ (chartTransition c p) (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p v))
      (fderiv ℝ (chartTransition c p) (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p w)) at heval
  rw [chartTransition_comp_chart_differential c p p hp (mem_chart_source FourSpace p) v,
    chartTransition_comp_chart_differential c p p hp (mem_chart_source FourSpace p) w, hbase] at heval
  exact heval.symm

theorem lieTensor_chart_recovery (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hY : VectorContDiff 1 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (lieTensor Y g) c x = lieTensorInChart Y g c x := by
  have hp := (chartAt FourSpace c).map_target hx
  funext i j
  change lieTensor Y g ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j)) = _
  rw [lieTensor_eq_chart g Y hg hY c _ hp]
  have hcancel (v : FourSpace) := congrArg (fun D => D v)
    ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
  change matrixToForm (lieTensorInChart Y g c (chartAt FourSpace c ((chartAt FourSpace c).symm x)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))) = _
  have hc (v : FourSpace) : mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x v) = v := hcancel v
  rw [hc, hc, (chartAt FourSpace c).right_inv hx]
  exact matrixToForm_basis _ i j

theorem lieTensor_chart_eventually (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hY : VectorContDiff 1 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (lieTensor Y g) c =ᶠ[𝓝 x] lieTensorInChart Y g c := by
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
  exact lieTensor_chart_recovery g Y hg hY c y hy

end K24.Global.LieNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.WeitzenbockProof

theorem covariant_sym_algebra (A N : Mat4)
    (G dA dN : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hA : ∀ a i j, dA a i j =
      (∑ p, G p a i * A p j) + (∑ p, G p a j * A i p))
    (a b j : Fin 4) :
    ((∑ p, (dA a p j * N b p + A p j * dN a b p)) +
      (∑ p, (dA a b p * N j p + A b p * dN a j p))) -
      (∑ q, G q a b * ((∑ p, A p j * N q p) + (∑ p, A q p * N j p))) -
      (∑ q, G q a j * ((∑ p, A p q * N b p) + (∑ p, A b p * N q p))) =
      (∑ p, A p j * (dN a b p + (∑ q, G p a q * N b q) - (∑ q, G q a b * N q p))) +
      (∑ p, A b p * (dN a j p + (∑ q, G p a q * N j q) - (∑ q, G q a j * N q p))) := by
  simp only [hA, Fin.sum_univ_succ]
  ring

theorem coordDeriv_sum_mul (f h : Fin 4 → FourSpace → ℝ) (x : FourSpace)
    (hf : ∀ p, DifferentiableAt ℝ (f p) x) (hh : ∀ p, DifferentiableAt ℝ (h p) x)
    (a : Fin 4) :
    coordDeriv (fun y => ∑ p, f p y * h p y) a x =
      ∑ p, (coordDeriv (f p) a x * h p x + f p x * coordDeriv (h p) a x) := by
  unfold coordDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun p y => f p y * h p y)
    (fun p _ => (hf p).mul (hh p))]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [fderiv_fun_mul (hf p) (hh p)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem nablaVector_differentiableAt (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hG : ∀ d a b, DifferentiableAt ℝ (fun y => christoffelInChart g c y d a b) x)
    (hY : ContDiffAt ℝ 2 (vectorInChart Y c) x) (a d : Fin 4) :
    DifferentiableAt ℝ (fun y => nablaVectorInChart g Y c y a d) x := by
  have hYentry (p : Fin 4) : ContDiffAt ℝ 2 (fun y => vectorInChart Y c y p) x :=
    (coordProj p).contDiff.contDiffAt.comp x hY
  apply (IdentityProof.coordDeriv_differentiableAt _ x (hYentry d) a).add
  apply DifferentiableAt.fun_sum (u := Finset.univ)
    (A := fun p y => christoffelInChart g c y d a p * vectorInChart Y c y p)
  intro p _
  exact (hG d a p).mul ((hYentry p).differentiableAt (by norm_num))

theorem killing_covariant_coefficients (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 1 g) (hDY : VectorContDiff 1 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (killing g Y) c x i j =
      (∑ p, cov2InChart g c x p j * nablaVectorInChart g Y c x i p) +
      (∑ p, cov2InChart g c x i p * nablaVectorInChart g Y c x j p) := by
  rw [killing, LieNaturality.lieTensor_chart_recovery g Y hDg hDY c x hx]
  exact IdentityProof.lieTensorInChart_covariant g hg Y c x hx i j

theorem nabla_killing (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (a b j : Fin 4) :
    nablaTensorInChart g (killing g Y) c x a b j =
      (∑ p, cov2InChart g c x p j * secondNablaVectorInChart g Y c x a b p) +
      (∑ p, cov2InChart g c x b p * secondNablaVectorInChart g Y c x a j p) := by
  have hDg1 : Cov2ContDiff 1 g := fun q => (hDg q).of_le (by decide)
  have hDY1 : VectorContDiff 1 Y := fun q => (hDY q).of_le (by decide)
  have hmetricAt := (hDg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hvectorAt := (hDY c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hG := IdentityProof.christoffel_differentiableAt g hg c x hx hmetricAt
  have hN := nablaVector_differentiableAt g Y c x hG hvectorAt
  have hA (i k : Fin 4) : DifferentiableAt ℝ (fun y => cov2InChart g c y i k) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (hmetricAt.differentiableAt (by decide)) i) k
  have hEq : (fun y => cov2InChart (killing g Y) c y b j) =ᶠ[𝓝 x]
      (fun y => (∑ p, cov2InChart g c y p j * nablaVectorInChart g Y c y b p) +
        (∑ p, cov2InChart g c y b p * nablaVectorInChart g Y c y j p)) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    exact killing_covariant_coefficients g Y hg hDg1 hDY1 c y hy b j
  have hder : coordDeriv (fun y => cov2InChart (killing g Y) c y b j) a x =
      (∑ p, (coordDeriv (fun y => cov2InChart g c y p j) a x * nablaVectorInChart g Y c x b p +
        cov2InChart g c x p j * coordDeriv (fun y => nablaVectorInChart g Y c y b p) a x)) +
      (∑ p, (coordDeriv (fun y => cov2InChart g c y b p) a x * nablaVectorInChart g Y c x j p +
        cov2InChart g c x b p * coordDeriv (fun y => nablaVectorInChart g Y c y j p) a x)) := by
    have hd := congrArg (fun D : FourSpace →L[ℝ] ℝ => D (basisVector a))
      (hEq.fderiv_eq (𝕜 := ℝ))
    change coordDeriv (fun y => cov2InChart (killing g Y) c y b j) a x =
      coordDeriv (fun y => (∑ p, cov2InChart g c y p j * nablaVectorInChart g Y c y b p) +
        (∑ p, cov2InChart g c y b p * nablaVectorInChart g Y c y j p)) a x at hd
    rw [hd]
    have hleft : DifferentiableAt ℝ (fun y => ∑ p, cov2InChart g c y p j * nablaVectorInChart g Y c y b p) x :=
      DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => (hA p j).mul (hN b p))
    have hright : DifferentiableAt ℝ (fun y => ∑ p, cov2InChart g c y b p * nablaVectorInChart g Y c y j p) x :=
      DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => (hA b p).mul (hN j p))
    change fderiv ℝ _ x (basisVector a) = _
    rw [fderiv_fun_add hleft hright]
    change coordDeriv _ a x + coordDeriv _ a x = _
    rw [coordDeriv_sum_mul _ _ x (fun p => hA p j) (hN b),
      coordDeriv_sum_mul _ _ x (hA b) (hN j)]
  have hcompat (k i l : Fin 4) : coordDeriv (fun y => cov2InChart g c y i l) k x =
      (∑ p, christoffelInChart g c x p k i * cov2InChart g c x p l) +
      (∑ p, christoffelInChart g c x p k l * cov2InChart g c x i p) := by
    have h := IdentityProof.nablaTensor_metric_zero g hg c x hx k i l
    unfold nablaTensorInChart at h
    linarith
  simp only [nablaTensorInChart, hder,
    killing_covariant_coefficients g Y hg hDg1 hDY1 c x hx, secondNablaVectorInChart]
  exact covariant_sym_algebra (cov2InChart g c x) (nablaVectorInChart g Y c x)
    (christoffelInChart g c x)
    (fun k i l => coordDeriv (fun y => cov2InChart g c y i l) k x)
    (fun k i l => coordDeriv (fun y => nablaVectorInChart g Y c y i l) k x) hcompat a b j

end K24.Global.WeitzenbockProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter Matrix
namespace K24.Global.WeitzenbockProof

theorem inverse_contract (A N : Mat4) (hA : IsUnit A.det) :
    (∑ a : Fin 4, ∑ b : Fin 4, A⁻¹ a b * (∑ p : Fin 4, A b p * N a p)) =
      ∑ a : Fin 4, N a a := by
  apply Finset.sum_congr rfl
  intro a _
  change (A⁻¹ *ᵥ (A *ᵥ (N a))) a = N a a
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]

theorem trace_sym_gradient (A N : Mat4) (hA : IsUnit A.det)
    (hs : ∀ i j, A i j = A j i) :
    (∑ a : Fin 4, ∑ b : Fin 4, A⁻¹ a b *
      ((∑ p : Fin 4, A p b * N a p) + (∑ p : Fin 4, A a p * N b p))) =
      2 * ∑ a : Fin 4, N a a := by
  have hsym : A.IsSymm := by ext i j; exact hs j i
  have hi (i j : Fin 4) : A⁻¹ i j = A⁻¹ j i := by
    exact congrArg (fun B : Mat4 => B j i) hsym.inv
  have hsecond : (∑ a : Fin 4, ∑ b : Fin 4, A⁻¹ a b * (∑ p : Fin 4, A a p * N b p)) =
      ∑ a : Fin 4, ∑ b : Fin 4, A⁻¹ a b * (∑ p : Fin 4, A b p * N a p) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hi b a]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hsecond]
  have hfirst : (∑ a : Fin 4, ∑ b : Fin 4, A⁻¹ a b * (∑ p : Fin 4, A p b * N a p)) =
      ∑ a : Fin 4, ∑ b : Fin 4, A⁻¹ a b * (∑ p : Fin 4, A b p * N a p) := by
    congr 1
    funext a
    congr 1
    funext b
    congr 1
    congr 1
    funext p
    rw [hs p b]
  rw [hfirst, inverse_contract A N hA]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem trace_killing (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 1 g) (hDY : VectorContDiff 1 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    metricTraceInChart g (killing g Y) c x =
      2 * ∑ a : Fin 4, nablaVectorInChart g Y c x a a := by
  simp only [metricTraceInChart, killing_covariant_coefficients g Y hg hDg hDY c x hx]
  exact trace_sym_gradient (cov2InChart g c x) (nablaVectorInChart g Y c x)
    (IdentityProof.cov2InChart_isUnit_det g hg c x hx)
    (IdentityProof.cov2InChart_symmetric g hg.1 c x)

theorem trace_secondNabla (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace) (j : Fin 4) :
    (∑ a : Fin 4, coordDeriv (fun y => nablaVectorInChart g Y c y a a) j x) =
      ∑ a : Fin 4, secondNablaVectorInChart g Y c x j a a := by
  have hcancel : (∑ a : Fin 4, ∑ p : Fin 4,
      christoffelInChart g c x a j p * nablaVectorInChart g Y c x a p) =
    ∑ a : Fin 4, ∑ p : Fin 4,
      christoffelInChart g c x p j a * nablaVectorInChart g Y c x p a :=
    Finset.sum_comm
  simp only [secondNablaVectorInChart, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcancel]
  ring

theorem coordDeriv_trace_killing (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    coordDeriv (metricTraceInChart g (killing g Y) c) j x =
      2 * ∑ a : Fin 4, secondNablaVectorInChart g Y c x j a a := by
  have hDg1 : Cov2ContDiff 1 g := fun q => (hDg q).of_le (by decide)
  have hDY1 : VectorContDiff 1 Y := fun q => (hDY q).of_le (by decide)
  have hmetricAt := (hDg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hvectorAt := (hDY c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hG := IdentityProof.christoffel_differentiableAt g hg c x hx hmetricAt
  have hN := nablaVector_differentiableAt g Y c x hG hvectorAt
  have hEq : metricTraceInChart g (killing g Y) c =ᶠ[𝓝 x]
      (fun y => 2 * ∑ a : Fin 4, nablaVectorInChart g Y c y a a) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    exact trace_killing g Y hg hDg1 hDY1 c y hy
  have hsum : DifferentiableAt ℝ (fun y => ∑ a : Fin 4, nablaVectorInChart g Y c y a a) x :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun a _ => hN a a)
  unfold coordDeriv
  rw [hEq.fderiv_eq (𝕜 := ℝ), fderiv_const_mul hsum 2,
    fderiv_fun_sum (u := Finset.univ) (A := fun a y => nablaVectorInChart g Y c y a a)
      (fun a _ => hN a a)]
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply]
  congr 1
  exact trace_secondNabla g Y c x j

theorem divergence_killing (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    (∑ a : Fin 4, ∑ b : Fin 4,
      inverseMetricInChart g c x a b * nablaTensorInChart g (killing g Y) c x a b j) =
      (∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
        inverseMetricInChart g c x a b * cov2InChart g c x j d *
          secondNablaVectorInChart g Y c x a b d) +
      (∑ a : Fin 4, secondNablaVectorInChart g Y c x a j a) := by
  simp only [nabla_killing g Y hg hDg hDY c x hx, mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [IdentityProof.cov2InChart_symmetric g hg.1 c x d j]
    ring
  · exact inverse_contract (cov2InChart g c x)
      (fun a d => secondNablaVectorInChart g Y c x a j d)
      (IdentityProof.cov2InChart_isUnit_det g hg c x hx)

theorem ricci_commutator (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    (∑ a : Fin 4, secondNablaVectorInChart g Y c x a j a) -
      (∑ a : Fin 4, secondNablaVectorInChart g Y c x j a a) =
        ∑ p : Fin 4, ricciInChart g c x j p * vectorInChart Y c x p := by
  have hmetricAt := (hDg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hvectorAt := (hDY c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  rw [← Finset.sum_sub_distrib]
  simp_rw [IdentityProof.secondNabla_commutator_of_contDiffAt g hg Y c x hx hmetricAt hvectorAt]
  rw [Finset.sum_comm]
  simp only [ricciInChart, Finset.sum_mul]

theorem bianchi_killing_coefficients (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    bianchiInChart g (killing g Y) c x j =
      -(∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
        inverseMetricInChart g c x a b * cov2InChart g c x j d *
          secondNablaVectorInChart g Y c x a b d) -
      (∑ p : Fin 4, ricciInChart g c x j p * vectorInChart Y c x p) := by
  have hd := divergence_killing g Y hg hDg hDY c x hx j
  have ht := coordDeriv_trace_killing g Y hg hDg hDY c x hx j
  have hr := ricci_commutator g Y hg hDg hDY c x hx j
  unfold bianchiInChart
  rw [hd, ht]
  linarith

end K24.Global.WeitzenbockProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
namespace K24.Global.WeitzenbockProof

theorem matrixToBilinear_contract (A : Mat4) (v : FourSpace) :
    matrixToBilinear A v = coefficientsToCovector (fun j => ∑ p : Fin 4, A p j * v p) := by
  ext w
  simp only [matrixToBilinear, coefficientsToCovector, _root_.sum_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, coordProj,
    PiLp.proj_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem ricciVectorFlat_coordinates (g : RawCov2 M) (Y : RawVector M) :
    ricciVectorFlat g Y = covectorFromCoordinates
      (fun c x j => ∑ p : Fin 4, ricciInChart g c x p j * vectorInChart Y c x p) := by
  funext p
  have hbase := (chartAt FourSpace p).left_inv (mem_chart_source FourSpace p)
  change (bilinearPullback (matrixToBilinear (ricciInChart g p (chartAt FourSpace p p)))
    (mfderiv I4 I4 (chartAt FourSpace p) p)) (Y p) = _
  rw [show (bilinearPullback (matrixToBilinear (ricciInChart g p (chartAt FourSpace p p)))
      (mfderiv I4 I4 (chartAt FourSpace p) p)) (Y p) =
      (matrixToBilinear (ricciInChart g p (chartAt FourSpace p p))
        (mfderiv I4 I4 (chartAt FourSpace p) p (Y p))).comp
        (mfderiv I4 I4 (chartAt FourSpace p) p) from rfl,
    matrixToBilinear_contract]
  change (coefficientsToCovector
      (fun j => ∑ q : Fin 4, ricciInChart g p (chartAt FourSpace p p) q j *
        (show FourSpace from mfderiv I4 I4 (chartAt FourSpace p) p (Y p)) q)).comp
      (mfderiv I4 I4 (chartAt FourSpace p) p) =
    (coefficientsToCovector
      (fun j => ∑ q : Fin 4, ricciInChart g p (chartAt FourSpace p p) q j *
        vectorInChart Y p (chartAt FourSpace p p) q)).comp
      (mfderiv I4 I4 (chartAt FourSpace p) p)
  have hvector : vectorInChart Y p (chartAt FourSpace p p) =
      (show FourSpace from mfderiv I4 I4 (chartAt FourSpace p) p (Y p)) := by
    exact congrArg (fun q : M =>
      (show FourSpace from mfderiv I4 I4 (chartAt FourSpace p) q (Y q))) hbase
  rw [hvector]

theorem covectorFromCoordinates_sub
    (A B : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (fun c x j => A c x j - B c x j) =
      covectorFromCoordinates A - covectorFromCoordinates B := by
  funext p
  ext v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    Finset.sum_sub_distrib, sub_mul]

theorem covectorFromCoordinates_congr_on_target
    (A B : M → FourSpace → Fin 4 → ℝ)
    (h : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ∀ j, A c x j = B c x j) :
    covectorFromCoordinates A = covectorFromCoordinates B := by
  funext p
  have hcoeff : A p (chartAt FourSpace p p) = B p (chartAt FourSpace p p) :=
    funext (h p (chartAt FourSpace p p) ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)))
  simp only [covectorFromCoordinates, hcoeff]

variable [IsManifold I4 ∞ M]

theorem bianchi_killing_ricci_transpose (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y) :
    bianchi g (killing g Y) = roughVectorLaplacianFlat g Y -
      covectorFromCoordinates (fun c x j =>
        ∑ p : Fin 4, ricciInChart g c x j p * vectorInChart Y c x p) := by
  change covectorFromCoordinates (bianchiInChart g (killing g Y)) = _
  unfold roughVectorLaplacianFlat
  rw [← covectorFromCoordinates_sub]
  apply covectorFromCoordinates_congr_on_target
  intro c x hx j
  exact bianchi_killing_coefficients g Y hg hDg hDY c x hx j

theorem bianchi_killing_ricci_transpose_of_holder
    (C : BoundedLocalCover M) (bounds : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C bounds z)
    (Y : RawVector M) (hY : C.VectorHolder 2 bounds.exponent.value Y) :
    bianchi z (killing z Y) = roughVectorLaplacianFlat z Y -
      covectorFromCoordinates (fun c x j =>
        ∑ p : Fin 4, ricciInChart z c x j p * vectorInChart Y c x p) := by
  apply bianchi_killing_ricci_transpose z Y hz.metric
  · intro c
    exact (cov2ContDiff_of_metricAdmissible C bounds z hz c).of_le
      (by exact_mod_cast bounds.order_ge_two)
  · exact vectorContDiff_of_cover_coefficients C 2 Y hY.1

end K24.Global.WeitzenbockProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.RicciSymmetryProof
open Matrix IdentityProof
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise NNReal
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem weitzenbock_of_cov2ContDiff (g : RawCov2 M) (Y : RawVector M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y) :
    bianchi g (killing g Y) = roughVectorLaplacianFlat g Y - ricciVectorFlat g Y := by
  have hRic : covectorFromCoordinates (fun c x j =>
      ∑ p : Fin 4, ricciInChart g c x j p * vectorInChart Y c x p) = ricciVectorFlat g Y := by
    rw [WeitzenbockProof.ricciVectorFlat_coordinates]
    apply WeitzenbockProof.covectorFromCoordinates_congr_on_target
    intro c x hx j
    apply Finset.sum_congr rfl
    intro p _
    rw [RicciSymmetryProof.ricci_symmetric_at g hg c x hx
      ((hDg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)) j p]
  rw [WeitzenbockProof.bianchi_killing_ricci_transpose g Y hg hDg hDY, hRic]

theorem weitzenbock_of_holder (C : BoundedLocalCover M) (bounds : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C bounds z)
    (Y : RawVector M) (hY : C.VectorHolder 2 bounds.exponent.value Y) :
    bianchi z (killing z Y) = roughVectorLaplacianFlat z Y - ricciVectorFlat z Y := by
  apply weitzenbock_of_cov2ContDiff z Y hz.metric
  · intro c
    exact (cov2ContDiff_of_metricAdmissible C bounds z hz c).of_le
      (by exact_mod_cast bounds.order_ge_two)
  · exact vectorContDiff_of_cover_coefficients C 2 Y hY.1

universe u

theorem weitzenbock :
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics)
    (H : ℝ≥0), 1 ≤ H →
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ C : BoundedLocalCover M, C.numerics = coverBounds →
      ∀ rho : CircleAction M,
        HolderActionControl C metricBounds.exponent.value H 2 rho →
      ∀ (lam : ℝ) (ghat z g : RawCov2 M),
        MetricAdmissible C metricBounds ghat →
        MetricAdmissible C metricBounds z →
        MetricAdmissible C metricBounds g →
        IsInvariantCov2 rho ghat → IsInvariantCov2 rho z →
        ∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          bianchi z (killing z Y) = roughVectorLaplacianFlat z Y - ricciVectorFlat z Y := by
  intro coverBounds metricBounds H hH M _ _ _ _ _ C hC rho hrho lam ghat z g hghat hz hg highat hiz Y hY
  exact weitzenbock_of_holder C metricBounds z hz Y hY

end K24.Global

open K24.Global in
theorem solution :
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics)
    (H : ℝ≥0), 1 ≤ H →
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ C : BoundedLocalCover M, C.numerics = coverBounds →
      ∀ rho : CircleAction M,
        HolderActionControl C metricBounds.exponent.value H 2 rho →
      ∀ (lam : ℝ) (ghat z g : RawCov2 M),
        MetricAdmissible C metricBounds ghat →
        MetricAdmissible C metricBounds z →
        MetricAdmissible C metricBounds g →
        IsInvariantCov2 rho ghat → IsInvariantCov2 rho z →
        ∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          bianchi z (killing z Y) = roughVectorLaplacianFlat z Y - ricciVectorFlat z Y :=
  weitzenbock
