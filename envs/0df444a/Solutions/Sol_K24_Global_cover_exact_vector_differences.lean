-- Prove2me | solution 1 for K24.Global.cover_exact_vector_differences
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:28:12.877423+00:00
-- url     : https://prove2.me/submissions/32008515-02e2-43a6-ab4c-232eca15098c

import Definitions.Def_K24GlobalStatement

/- Inlined module: IdentitySupport -/
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

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

end

/- Inlined module: LieNaturality -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
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
end

/- Inlined module: ChartTransitions -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
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
end

/- Inlined module: LieRecovery -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
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
end

/- Inlined module: Connection -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
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
end

/- Inlined module: Covariant -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem chartTransition_symm_apply (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    chartTransition d c (chartTransition c d x) = x := by
  simp only [chartTransition, Function.comp_apply,
    (chartAt FourSpace d).left_inv hd, (chartAt FourSpace c).right_inv hx]

theorem cov2InChart_differentiableAt_overlap (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) :
    DifferentiableAt ℝ (cov2InChart u d) (chartTransition c d x) := by
  let y := chartTransition c d x
  let F := chartTransition d c
  have hy : y ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hc : (chartAt FourSpace d).symm y ∈ (chartAt FourSpace c).source := by
    dsimp [y, chartTransition]
    rw [(chartAt FourSpace d).left_inv hd]
    exact (chartAt FourSpace c).map_target hx
  have hFy : F y = x := chartTransition_symm_apply c d x hx hd
  have hF : ContDiffAt ℝ 2 F y := (chartTransition_smooth d c y hy hc).of_le (by decide)
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hU : DifferentiableAt ℝ (formInChart u c) (F y) := by
    rw [hFy]
    exact formInChart_differentiableAt u c x hDu
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have h := ((hU.comp y hF1).clm_apply (hDF.clm_apply (differentiableAt_const (basisVector i)))).clm_apply
    (hDF.clm_apply (differentiableAt_const (basisVector j)))
  apply h.congr_of_eventuallyEq
  filter_upwards [chartTransition_form_eventually u d c y hy hc] with z hz
  have hz' := congrArg (fun A : Form => A (basisVector i) (basisVector j)) hz
  simpa only [bilinearPullback_apply, formInChart, Function.comp_apply, matrixToForm_basis] using hz'

def nablaForm (g u : RawCov2 M) (c : M) (x : FourSpace) : Cov3 :=
  fderiv ℝ (formInChart u c) x - lowerGamma (formInChart u c x) (gammaForm g c x) -
    flipForm.comp (lowerGamma (formInChart u c x).flip (gammaForm g c x))

@[simp] theorem nablaForm_apply (g u : RawCov2 M) (c : M) (x v w t : FourSpace) :
    nablaForm g u c x v w t = fderiv ℝ (formInChart u c) x v w t -
      formInChart u c x (gammaForm g c x v w) t -
      formInChart u c x w (gammaForm g c x v t) := rfl

theorem nablaForm_basis (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (i j k : Fin 4) :
    nablaForm g u c x (basisVector i) (basisVector j) (basisVector k) =
      nablaTensorInChart g u c x i j k := by
  simp only [nablaForm_apply, formInChart_derivative_basis u c x hDu,
    gammaForm_basis, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [formInChart, Function.comp_apply, matrixToForm_basis, nablaTensorInChart]

theorem nablaForm_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (v w t : FourSpace) :
    nablaForm g u c x v w t = nablaForm g u d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w)
      (fderiv ℝ (chartTransition c d) x t) := by
  have hDd := cov2InChart_differentiableAt_overlap u c d x hx hd hDu
  simp only [nablaForm_apply]
  rw [fderiv_pullback_relation (formInChart u d) (formInChart u c) (chartTransition c d) x
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
    (formInChart_differentiableAt u d _ hDd)
    (formInChart_differentiableAt u c x hDu)
    (chartTransition_form_eventually u c d x hx hd)]
  rw [chartTransition_form u c d x hx hd]
  simp only [bilinearPullback_apply, gammaForm_natural g hg hDg c d x hx hd,
    map_add, _root_.add_apply]
  ring

end K24.Global.BianchiNaturality
end

/- Inlined module: TraceBasics -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

def cov3Slice (C : Cov3) (t : FourSpace) : Form :=
  (ContinuousLinearMap.compL ℝ FourSpace (FourSpace →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ t)).comp C

@[simp] theorem cov3Slice_apply (C : Cov3) (t v w : FourSpace) :
    cov3Slice C t v w = C v w t := rfl

def divergenceForm (g u : RawCov2 M) (c : M) (x : FourSpace) : FourSpace →L[ℝ] ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, inverseMetricInChart g c x i j •
    nablaForm g u c x (basisVector i) (basisVector j)

@[simp] theorem divergenceForm_apply (g u : RawCov2 M) (c : M) (x t : FourSpace) :
    divergenceForm g u c x t = ∑ i : Fin 4, ∑ j : Fin 4,
      inverseMetricInChart g c x i j * nablaForm g u c x (basisVector i) (basisVector j) t := by
  simp [divergenceForm]

def bianchiForm (g u : RawCov2 M) (c : M) (x : FourSpace) : FourSpace →L[ℝ] ℝ :=
  -divergenceForm g u c x + (1 / 2 : ℝ) • fderiv ℝ (metricTraceInChart g u c) x

@[simp] theorem bianchiForm_apply (g u : RawCov2 M) (c : M) (x t : FourSpace) :
    bianchiForm g u c x t = -divergenceForm g u c x t +
      (1 / 2 : ℝ) * fderiv ℝ (metricTraceInChart g u c) x t := by
  rfl

theorem bianchiForm_basis (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    bianchiForm g u c x (basisVector j) = bianchiInChart g u c x j := by
  simp only [bianchiForm_apply, divergenceForm_apply, nablaForm_basis g u c x hDu,
    bianchiInChart, coordDeriv]

theorem bianchiForm_eq (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) :
    bianchiForm g u c x = coefficientsToCovector (bianchiInChart g u c x) := by
  rw [← coefficientsToCovector_recover (bianchiForm g u c x)]
  congr 1
  funext j
  exact bianchiForm_basis g u c x hDu j

theorem metricTraceInChart_differentiableAt (g u : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  have hinv := differentiableAt_inverseMetric g hg c x hx hDg
  unfold metricTraceInChart
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.fun_sum
  intro j _
  exact ((differentiableAt_pi.mp (differentiableAt_pi.mp hinv i) j)).mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp hDu i) j)


theorem covectorFromCoordinates_chart_value
    (a : M → FourSpace → Fin 4 → ℝ) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    covectorInChart (covectorFromCoordinates a) c x j =
      coefficientsToCovector
        (a ((chartAt FourSpace c).symm x)
          (chartAt FourSpace ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)))
        (fderiv ℝ (chartTransition c ((chartAt FourSpace c).symm x)) x (basisVector j)) := by
  rw [chartTransition_derivative c ((chartAt FourSpace c).symm x) x hx
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm x))]
  rfl

end K24.Global.BianchiNaturality
end

/- Inlined module: Contraction -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
open scoped BigOperators Matrix.Norms.Elementwise

namespace K24.Global.BianchiContraction

def matrixOf (J : FourSpace →L[ℝ] FourSpace) : Mat4 :=
  fun k i => J (basisVector i) k

theorem matrixToBilinear_apply (G : Mat4) (v w : FourSpace) :
    matrixToBilinear G v w = ∑ i : Fin 4, ∑ j : Fin 4, v i * (G i j * w j) := by
  simp [matrixToBilinear, coordProj]

theorem matrixToBilinear_basis (G : Mat4) (i j : Fin 4) :
    matrixToBilinear G (basisVector i) (basisVector j) = G i j := by
  simp [matrixToBilinear_apply, basisVector]

theorem bilinear_apply (A : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)) (v w : FourSpace) :
    A v w = ∑ i : Fin 4, ∑ j : Fin 4,
      v i * (A (basisVector i) (basisVector j) * w j) := by
  have h := congrArg (fun B : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) => B v w)
    (matrixToBilinear_recover A)
  exact h.symm.trans (matrixToBilinear_apply _ _ _)

theorem metric_matrix (J : FourSpace →L[ℝ] FourSpace) (G H : Mat4)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w)) :
    G = (matrixOf J).transpose * H * matrixOf J := by
  ext i j
  calc
    G i j = matrixToBilinear H (J (basisVector i)) (J (basisVector j)) := by
      rw [← hmetric, matrixToBilinear_basis]
    _ = ((matrixOf J).transpose * H * matrixOf J) i j := by
      simp only [matrixToBilinear_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_mul, matrixOf]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem matrixOf_isUnit_det (J : FourSpace →L[ℝ] FourSpace) (G H : Mat4)
    (hG : IsUnit G.det)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w)) :
    IsUnit (matrixOf J).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply isUnit_iff_ne_zero.mp hG
  rw [metric_matrix J G H hmetric, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp [hz]

theorem inverse_metric_matrix (J : FourSpace →L[ℝ] FourSpace) (G H : Mat4)
    (hG : IsUnit G.det)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w)) :
    matrixOf J * G⁻¹ * (matrixOf J).transpose = H⁻¹ := by
  have hJ := matrixOf_isUnit_det J G H hG hmetric
  calc
    matrixOf J * G⁻¹ * (matrixOf J).transpose =
        (matrixOf J * (matrixOf J)⁻¹) * H⁻¹ *
          (((matrixOf J).transpose)⁻¹ * (matrixOf J).transpose) := by
      rw [metric_matrix J G H hmetric, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    _ = H⁻¹ := by
      rw [Matrix.mul_nonsing_inv _ hJ,
        Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose _ hJ)]
      simp


theorem contract_natural (J : FourSpace →L[ℝ] FourSpace) (_hJ : Function.Bijective J)
    (G H : Mat4) (hG : IsUnit G.det) (_hH : IsUnit H.det)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w))
    (A : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)) :
    (∑ i : Fin 4, ∑ j : Fin 4, (G⁻¹) i j * A (J (basisVector i)) (J (basisVector j))) =
      ∑ i : Fin 4, ∑ j : Fin 4, (H⁻¹) i j * A (basisVector i) (basisVector j) := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        (matrixOf J k i * (G⁻¹) i j * matrixOf J l j) *
          A (basisVector k) (basisVector l) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [bilinear_apply A (J (basisVector i)) (J (basisVector j))]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      dsimp [matrixOf]
      ring
    _ = ∑ k : Fin 4, ∑ l : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        (matrixOf J k i * (G⁻¹) i j * matrixOf J l j) *
          A (basisVector k) (basisVector l) := by
      simpa only [Fintype.sum_prod_type] using
        (Finset.sum_comm (s := (Finset.univ : Finset (Fin 4 × Fin 4)))
          (t := (Finset.univ : Finset (Fin 4 × Fin 4)))
          (f := fun p q => (matrixOf J q.1 p.1 * (G⁻¹) p.1 p.2 * matrixOf J q.2 p.2) *
            A (basisVector q.1) (basisVector q.2)))
    _ = ∑ k : Fin 4, ∑ l : Fin 4,
        (matrixOf J * G⁻¹ * (matrixOf J).transpose) k l *
          A (basisVector k) (basisVector l) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by rw [inverse_metric_matrix J G H hG hmetric]

end K24.Global.BianchiContraction
end

/- Inlined module: BianchiRecovery -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof BianchiContraction
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem chartTransition_metric (g : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) (v w : FourSpace) :
    matrixToBilinear (cov2InChart g c x) v w =
      matrixToBilinear (cov2InChart g d (chartTransition c d x))
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) := by
  exact congrArg (fun A : Form => A v w) (chartTransition_form g c d x hx hd)

theorem metricTraceInChart_natural (g u : RawCov2 M) (hg : IsMetric g)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    metricTraceInChart g u c x = metricTraceInChart g u d (chartTransition c d x) := by
  have hy := (chartAt FourSpace d).map_source hd
  have hC := contract_natural (fderiv ℝ (chartTransition c d) x)
    (chartTransition_derivative_bijective c d x hx hd)
    (cov2InChart g c x) (cov2InChart g d (chartTransition c d x))
    (cov2InChart_isUnit_det g hg c x hx)
    (cov2InChart_isUnit_det g hg d _ hy)
    (chartTransition_metric g c d x hx hd)
    (formInChart u d (chartTransition c d x))
  have hu (i j : Fin 4) : cov2InChart u c x i j =
      formInChart u d (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x (basisVector i))
        (fderiv ℝ (chartTransition c d) x (basisVector j)) := by
    simpa only [bilinearPullback_apply, formInChart, Function.comp_apply, matrixToForm_basis] using
      congrArg (fun A : Form => A (basisVector i) (basisVector j))
        (chartTransition_form u c d x hx hd)
  unfold metricTraceInChart inverseMetricInChart
  simp_rw [hu]
  simpa only [formInChart, Function.comp_apply, matrixToForm_basis] using hC

theorem divergenceForm_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (t : FourSpace) :
    divergenceForm g u c x t = divergenceForm g u d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x t) := by
  have hy := (chartAt FourSpace d).map_source hd
  have hC := contract_natural (fderiv ℝ (chartTransition c d) x)
    (chartTransition_derivative_bijective c d x hx hd)
    (cov2InChart g c x) (cov2InChart g d (chartTransition c d x))
    (cov2InChart_isUnit_det g hg c x hx)
    (cov2InChart_isUnit_det g hg d _ hy)
    (chartTransition_metric g c d x hx hd)
    (cov3Slice (nablaForm g u d (chartTransition c d x))
      (fderiv ℝ (chartTransition c d) x t))
  simp only [divergenceForm_apply]
  simp_rw [nablaForm_natural g u hg hDg c d x hx hd hDu]
  simpa only [cov3Slice_apply, inverseMetricInChart] using hC

theorem metricTraceInChart_derivative_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (t : FourSpace) :
    fderiv ℝ (metricTraceInChart g u c) x t =
      fderiv ℝ (metricTraceInChart g u d) (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x t) := by
  have hy := (chartAt FourSpace d).map_source hd
  have hgd := ((hDg d).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hy)).differentiableAt (by norm_num)
  have hud := cov2InChart_differentiableAt_overlap u c d x hx hd hDu
  have htrace : metricTraceInChart g u c =ᶠ[𝓝 x]
      (fun y => metricTraceInChart g u d (chartTransition c d y)) := by
    filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
    exact metricTraceInChart_natural g u hg c d y hy.1 hy.2
  have hder := htrace.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x (metricTraceInChart_differentiableAt g u hg d _ hy hgd hud)
    ((chartTransition_smooth c d x hx hd).differentiableAt (by decide))] at hder
  exact congrArg (fun D : FourSpace →L[ℝ] ℝ => D t) hder

theorem bianchiForm_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (t : FourSpace) :
    bianchiForm g u c x t = bianchiForm g u d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x t) := by
  simp only [bianchiForm_apply,
    divergenceForm_natural g u hg hDg c d x hx hd hDu,
    metricTraceInChart_derivative_natural g u hg hDg c d x hx hd hDu]

theorem bianchi_chart_recovery_of_differentiableAt (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    covectorInChart (bianchi g u) c x j = bianchiInChart g u c x j := by
  let p := (chartAt FourSpace c).symm x
  have hp : p ∈ (chartAt FourSpace p).source := mem_chart_source FourSpace p
  have hud := cov2InChart_differentiableAt_overlap u c p x hx hp hDu
  change covectorInChart (covectorFromCoordinates (bianchiInChart g u)) c x j = _
  rw [covectorFromCoordinates_chart_value (bianchiInChart g u) c x hx j]
  change coefficientsToCovector (bianchiInChart g u p (chartTransition c p x))
    (fderiv ℝ (chartTransition c p) x (basisVector j)) = _
  rw [← bianchiForm_eq g u p _ hud,
    ← bianchiForm_natural g u hg hDg c p x hx hp hDu]
  exact bianchiForm_basis g u c x hDu j

theorem bianchi_chart_recovery (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDu : ContDiffAt ℝ 1 (cov2InChart u c) x) (j : Fin 4) :
    covectorInChart (bianchi g u) c x j = bianchiInChart g u c x j :=
  bianchi_chart_recovery_of_differentiableAt g u hg hDg c x hx
    (hDu.differentiableAt (by norm_num)) j

end K24.Global.BianchiNaturality
end

/- Inlined module: LieRegularity -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.GeometricRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem coordDeriv_contDiffAt (k : ℕ) (f : FourSpace → ℝ) (x : FourSpace)
    (hf : ContDiffAt ℝ (k + 1) f x) (a : Fin 4) :
    ContDiffAt ℝ k (coordDeriv f a) x := by
  exact (hf.fderiv_right (m := k) (by simp)).clm_apply contDiffAt_const

theorem lieTensorInChart_contDiffAt (k : ℕ) (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hg : ContDiffAt ℝ (k + 1) (cov2InChart g c) x)
    (hY : ContDiffAt ℝ (k + 1) (vectorInChart Y c) x) :
    ContDiffAt ℝ k (lieTensorInChart Y g c) x := by
  have hgentry (i j : Fin 4) : ContDiffAt ℝ (k + 1)
      (fun y => cov2InChart g c y i j) x := contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hYentry (i : Fin 4) : ContDiffAt ℝ (k + 1)
      (fun y => vectorInChart Y c y i) x :=
    (coordProj i).contDiff.contDiffAt.comp x hY
  have hle : (k : ℕ∞ω) ≤ k + 1 := by simp
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  apply ContDiffAt.sum
  intro p _
  exact (((hYentry p).of_le hle).mul (coordDeriv_contDiffAt k _ x (hgentry i j) p)).add
      ((coordDeriv_contDiffAt k _ x (hYentry p) i).mul ((hgentry p j).of_le hle)) |>.add
      ((coordDeriv_contDiffAt k _ x (hYentry p) j).mul ((hgentry i p).of_le hle))

theorem lieTensor_contDiff (k : ℕ) (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff (k + 1) g) (hY : VectorContDiff (k + 1) Y) :
    Cov2ContDiff k (lieTensor Y g) := by
  have hg1 : Cov2ContDiff 1 g := fun c => (hg c).of_le (by simp)
  have hY1 : VectorContDiff 1 Y := fun c => (hY c).of_le (by simp)
  intro c x hx
  have hgx := (hg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hYx := (hY c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  exact ((lieTensorInChart_contDiffAt k g Y c x hgx hYx).congr_of_eventuallyEq
    (LieNaturality.lieTensor_chart_eventually g Y hg1 hY1 c x hx)).contDiffWithinAt

theorem cov2ContDiff_two_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff 2 g := by
  intro c
  exact (cov2ContDiff_of_metricAdmissible C b g hg c).of_le (by exact_mod_cast b.order_ge_two)

theorem lieTensor_contDiff_one_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g)
    (Y : RawVector M) (hY : C.VectorHolder 2 b.exponent.value Y) :
    Cov2ContDiff 1 (lieTensor Y g) := by
  exact lieTensor_contDiff 1 g Y (cov2ContDiff_two_of_metricAdmissible C b g hg)
    (vectorContDiff_of_cover_coefficients C 2 Y hY.1)

end K24.Global.GeometricRegularity
end

/- Inlined module: BianchiLocalRegularity -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
namespace K24.Global.GeometricRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem inverseMetricInChart_contDiffAt (k : ℕ∞ω) (g : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ k (cov2InChart g c) x) :
    ContDiffAt ℝ k (inverseMetricInChart g c) x := by
  have hentry (a b : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hDg a) b
  have hdet : ContDiffAt ℝ k (fun y => (cov2InChart g c y).det) x := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    exact contDiffAt_prod (fun i _ => hentry (σ i) i)
  have hne : (cov2InChart g c x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (IdentityProof.cov2InChart_isUnit_det g hg c x hx)
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  simp only [inverseMetricInChart, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  apply (hdet.inv hne).mul
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  simp only [Matrix.updateRow_apply]
  split_ifs <;> first | exact contDiffAt_const | exact hentry _ _

theorem christoffelInChart_contDiffAt (k : ℕ) (g : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ (k + 1) (cov2InChart g c) x) (a b d : Fin 4) :
    ContDiffAt ℝ k (fun y => christoffelInChart g c y a b d) x := by
  have hentry (i j : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hDg i) j
  have hinv := inverseMetricInChart_contDiffAt k g hg c x hx (hDg.of_le (by simp))
  unfold christoffelInChart
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hinv a) l).mul
    (((coordDeriv_contDiffAt k _ x (hentry d l) b).add
      (coordDeriv_contDiffAt k _ x (hentry b l) d)).sub
      (coordDeriv_contDiffAt k _ x (hentry b d) l))

theorem metricTraceInChart_contDiffAt (k : ℕ∞ω) (g u : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ k (cov2InChart g c) x)
    (hDu : ContDiffAt ℝ k (cov2InChart u c) x) :
    ContDiffAt ℝ k (metricTraceInChart g u c) x := by
  have hinv := inverseMetricInChart_contDiffAt k g hg c x hx hDg
  unfold metricTraceInChart
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hinv a) b).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hDu a) b)

theorem nablaTensorInChart_contDiffAt (k : ℕ) (g u : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ (k + 1) (cov2InChart g c) x)
    (hDu : ContDiffAt ℝ (k + 1) (cov2InChart u c) x) (a b d : Fin 4) :
    ContDiffAt ℝ k (fun y => nablaTensorInChart g u c y a b d) x := by
  have hentry (i j : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hDu i) j
  have hgamma := christoffelInChart_contDiffAt k g hg c x hx hDg
  unfold nablaTensorInChart
  refine ((coordDeriv_contDiffAt k _ x (hentry b d) a).sub ?_).sub ?_
  · exact ContDiffAt.sum (fun p _ => (hgamma p a b).mul ((hentry p d).of_le (by simp)))
  · exact ContDiffAt.sum (fun p _ => (hgamma p a d).mul ((hentry b p).of_le (by simp)))

theorem bianchiInChart_contDiffAt (k : ℕ) (g u : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ (k + 1) (cov2InChart g c) x)
    (hDu : ContDiffAt ℝ (k + 1) (cov2InChart u c) x) :
    ContDiffAt ℝ k (bianchiInChart g u c) x := by
  have hinv := inverseMetricInChart_contDiffAt k g hg c x hx (hDg.of_le (by simp))
  apply contDiffAt_pi.mpr
  intro j
  unfold bianchiInChart
  refine ContDiffAt.add (ContDiffAt.neg ?_) ?_
  · exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hinv a) b).mul
        (nablaTensorInChart_contDiffAt k g u hg c x hx hDg hDu a b j)))
  · exact contDiffAt_const.mul (coordDeriv_contDiffAt k _ x
      (metricTraceInChart_contDiffAt (k + 1) g u hg c x hx hDg hDu) j)

end K24.Global.GeometricRegularity
end

/- Inlined module: HaarContinuity -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff BigOperators NNReal Topology
open Filter MeasureTheory
namespace K24.Global.VectorCovectorHaarProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
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

theorem continuous_actionPullbackCovector_eval
    (rho : CircleAction M) (u : RawCovector M)
    (hu : ∀ q : M, ContinuousOn (covectorInChart u q) (chartAt FourSpace q).target)
    (p : M) (v : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCovector rho t u p v) := by
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
      (fun t : Circle => covectorInChart u q (chartAt FourSpace q (rho.act t p))) t₀ := by
    apply ((hu q).continuousAt ((chartAt FourSpace q).open_target.mem_nhds
      ((chartAt FourSpace q).map_source hq))).comp_of_eq hchart rfl
  have hformula : ContinuousAt (fun t : Circle =>
      coefficientsToCovector (covectorInChart u q (chartAt FourSpace q (rho.act t p)))
        (D t v)) t₀ := by
    simp only [coefficientsToCovector, sum_apply, smul_apply, smul_eq_mul]
    apply tendsto_finsetSum
    intro a _ha
    exact ((continuous_apply a).continuousAt.comp hcoeff).mul
      ((coordProj a).continuous.continuousAt.comp (hD.clm_apply continuousAt_const))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  have hrec := covector_chart_recovery u q (rho.act t p) ht
  have hd := action_differential_coordinates_eq rho p t₀ t ht
  change D t = _ at hd
  rw [hd]
  dsimp only [actionPullbackCovector, pullbackCovector]
  change u (rho.act t p) (mfderiv I4 I4 (rho.act t) p v) = _
  rw [← hrec]
  rfl

theorem covectorHaarIntegrable_of_canonical_continuity
    (rho : CircleAction M) (u : RawCovector M)
    (hu : ∀ q : M, ContinuousOn (covectorInChart u q) (chartAt FourSpace q).target) :
    CovectorHaarIntegrable rho u := by
  intro c x _hx i
  exact Continuous.integrable_of_hasCompactSupport
    (continuous_actionPullbackCovector_eval rho u hu ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i)))
    (HasCompactSupport.of_compactSpace _)

end K24.Global.VectorCovectorHaarProof
end

/- Inlined module: CanonicalRegularity -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.GeometricRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem bianchi_contDiff (k : ℕ) (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff (k + 1) g) (hDu : Cov2ContDiff (k + 1) u) :
    CovectorContDiff k (bianchi g u) := by
  have hDg1 : Cov2ContDiff 1 g := fun c => (hDg c).of_le (by simp)
  intro c x hx
  have hnear : covectorInChart (bianchi g u) c =ᶠ[𝓝 x] bianchiInChart g u c := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    funext j
    exact BianchiNaturality.bianchi_chart_recovery g u hg hDg1 c y hy
      (((hDu c y hy).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hy)).of_le
        (by simp)) j
  have hDgx := (hDg c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hDux := (hDu c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  exact ((bianchiInChart_contDiffAt k g u hg c x hx hDgx hDux).congr_of_eventuallyEq
    hnear).contDiffWithinAt

theorem bianchi_haarIntegrable (rho : CircleAction M) (g u : RawCov2 M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 1 g) (hDu : Cov2ContDiff 1 u) :
    CovectorHaarIntegrable rho (bianchi g u) := by
  apply VectorCovectorHaarProof.covectorHaarIntegrable_of_canonical_continuity rho _
  exact fun c => (bianchi_contDiff 0 g u hg hDg hDu c).continuousOn

theorem vectorOperator_contDiff_zero (ghat g : RawCov2 M) (Y : RawVector M)
    (hghat : IsMetric ghat) (hDghat : Cov2ContDiff 1 ghat)
    (hDg : Cov2ContDiff 2 g) (hDY : VectorContDiff 2 Y) :
    CovectorContDiff 0 (vectorOperator ghat g Y) := by
  exact bianchi_contDiff 0 ghat (lieTensor Y g) hghat hDghat
    (lieTensor_contDiff 1 g Y hDg hDY)

theorem vectorOperator_haarIntegrable (rho : CircleAction M)
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (ghat g : RawCov2 M)
    (hghat : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (Y : RawVector M) (hY : C.VectorHolder 2 b.exponent.value Y) :
    CovectorHaarIntegrable rho (vectorOperator ghat g Y) := by
  apply VectorCovectorHaarProof.covectorHaarIntegrable_of_canonical_continuity rho _
  exact fun c => (vectorOperator_contDiff_zero ghat g Y hghat.metric
    (fun d => (cov2ContDiff_two_of_metricAdmissible C b ghat hghat d).of_le (by norm_num))
    (cov2ContDiff_two_of_metricAdmissible C b g hg)
    (vectorContDiff_of_cover_coefficients C 2 Y hY.1) c).continuousOn

theorem bianchi_contDiff_one_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g)
    (u : RawCov2 M) (hu : C.Cov2Holder 2 b.exponent.value u) :
    CovectorContDiff 1 (bianchi g u) := by
  exact bianchi_contDiff 1 g u hg.metric (cov2ContDiff_two_of_metricAdmissible C b g hg)
    (cov2ContDiff_of_cov2Holder C 2 b.exponent.value u hu)

end K24.Global.GeometricRegularity
end

/- Inlined module: ExactAlgebra -/
noncomputable section

/-!
Exact operator algebra for the literal frozen K24 definitions.
No target file with admitted theorems is imported.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.Research20261024

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

@[simp] theorem covectorInChart_sub (eta theta : RawCovector M) (c : M) (x : FourSpace) :
    covectorInChart (eta - theta) c x = covectorInChart eta c x - covectorInChart theta c x := by
  rfl

@[simp] theorem covectorInChart_zero (c : M) (x : FourSpace) :
    covectorInChart (0 : RawCovector M) c x = 0 := by
  rfl

@[simp] theorem cov2InChart_zero (c : M) (x : FourSpace) :
    cov2InChart (0 : RawCov2 M) c x = 0 := by
  rfl

@[simp] theorem cov2FromCoordinates_zero :
    cov2FromCoordinates (fun (_ : M) (_ : FourSpace) => (0 : Mat4)) = 0 := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear]

@[simp] theorem cov2FromCoordinates_sub (a b : M → FourSpace → Mat4) :
    cov2FromCoordinates (a - b) = cov2FromCoordinates a - cov2FromCoordinates b := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear, sub_mul,
    mul_sub, Finset.sum_sub_distrib]

/-- This is the genuine coordinate derivative rule, with its essential hypotheses. -/
theorem coordDeriv_sub {f h : FourSpace → ℝ} {x : FourSpace}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    coordDeriv (f - h) i x = coordDeriv f i x - coordDeriv h i x := by
  simp [coordDeriv, fderiv_sub hf hh]

/-- Coordinate regularity on the chart target supplies ordinary, not merely
within-set, differentiability because the chart target is open. -/
theorem covector_coefficient_differentiableAt (eta : RawCovector M)
    (h : CovectorContDiff 1 eta) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    DifferentiableAt ℝ (fun y => covectorInChart eta c y j) x := by
  exact differentiableAt_pi.mp
    (((h c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt_one) j

@[simp] theorem deltaStar_zero (g : RawCov2 M) : deltaStar g 0 = 0 := by
  have hz : deltaStarInChart g 0 = fun _ _ => (0 : Mat4) := by
    funext c x i j
    simp [deltaStarInChart, nablaCovectorInChart, coordDeriv]
  rw [deltaStar, hz, cov2FromCoordinates_zero]

/-- Subtraction for the actual Levi-Civita symmetrized gradient. The metric
is arbitrary: this law only differentiates its covector argument. -/
theorem deltaStar_sub (g : RawCov2 M) (eta theta : RawCovector M)
    (heta : CovectorContDiff 1 eta) (htheta : CovectorContDiff 1 theta) :
    deltaStar g (eta - theta) = deltaStar g eta - deltaStar g theta := by
  have hlocal (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
      (a b : Fin 4) :
      nablaCovectorInChart g (eta - theta) c x a b =
        nablaCovectorInChart g eta c x a b - nablaCovectorInChart g theta c x a b := by
    have hd := coordDeriv_sub
      (covector_coefficient_differentiableAt eta heta c x hx b)
      (covector_coefficient_differentiableAt theta htheta c x hx b) a
    simp only [nablaCovectorInChart, covectorInChart_sub, Pi.sub_apply]
    change coordDeriv ((fun y => covectorInChart eta c y b) -
      (fun y => covectorInChart theta c y b)) a x - _ = _
    rw [hd]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  unfold deltaStar
  rw [← cov2FromCoordinates_sub]
  funext p
  change cov2FromChartAt p p (deltaStarInChart g (eta - theta) p (chartAt FourSpace p p)) =
    cov2FromChartAt p p ((deltaStarInChart g eta - deltaStarInChart g theta) p
      (chartAt FourSpace p p))
  congr 1
  ext i j
  simp only [Pi.sub_apply, deltaStarInChart]
  rw [hlocal p _ (mem_chart_target FourSpace p) i j,
    hlocal p _ (mem_chart_target FourSpace p) j i]
  ring

/-- The exact unprojected tensor-defect identity for the frozen operators.
Regularity of the two Bianchi outputs is explicit, not presumed from the
unproved coordinate-compatibility results. -/
theorem gaugedLinearization_difference (lam : ℝ) (ghat z u : RawCov2 M)
    (hfixed : CovectorContDiff 1 (bianchi ghat u))
    (hcenter : CovectorContDiff 1 (bianchi z u)) :
    gaugedLinearization lam ghat z u - gaugedLinearization lam z z u =
      tensorDefect ghat z u := by
  unfold gaugedLinearization tensorDefect
  rw [deltaStar_sub z _ _ hfixed hcenter]
  abel

@[simp] theorem cov2VariationDerivative_zero (t : ℝ) :
    cov2VariationDerivative (fun _ => (0 : RawCov2 M)) t = 0 := by
  simp only [cov2VariationDerivative, cov2InChart_zero, deriv_const]
  exact cov2FromCoordinates_zero

/-- The metric-dependent variation term vanishes on an identically zero
covector without differentiability or positivity assumptions. -/
@[simp] theorem deltaStarMetricVariation_zero (z u : RawCov2 M) :
    deltaStarMetricVariation z u 0 = 0 := by
  simp [deltaStarMetricVariation]

/-- Cancels the dangerous metric-variation term once genuine Haar cancellation
has been established; it does not assume a product rule. -/
theorem dangerous_term_zero_of_cancellation (rho : CircleAction M)
    (ghat z u : RawCov2 M)
    (hc : covectorPiPerp rho (bianchi ghat (z - ghat)) = 0) :
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0 := by
  rw [hc, deltaStarMetricVariation_zero]

@[simp] theorem cov2InChart_sub (u v : RawCov2 M) (c : M) (x : FourSpace) :
    cov2InChart (u - v) c x = cov2InChart u c x - cov2InChart v c x := by
  rfl

@[simp] theorem covectorFromCoordinates_sub (a b : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (a - b) = covectorFromCoordinates a - covectorFromCoordinates b := by
  ext p v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    sub_mul, Finset.sum_sub_distrib]

theorem cov2_coefficient_differentiableAt (u : RawCov2 M)
    (h : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x := by
  exact differentiableAt_pi.mp (differentiableAt_pi.mp
    (((h c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt_one) i) j

/-- The actual Lie derivative is additive in its tensor argument. There is
no regularity premise on Y: its coordinate derivatives are fixed coefficients. -/
theorem lieTensor_sub (Y : RawVector M) (u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v) :
    lieTensor Y (u - v) = lieTensor Y u - lieTensor Y v := by
  have hlocal (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
      (i j : Fin 4) :
      lieTensorInChart Y (u - v) c x i j =
        lieTensorInChart Y u c x i j - lieTensorInChart Y v c x i j := by
    have hd (a : Fin 4) := coordDeriv_sub
      (cov2_coefficient_differentiableAt u hu c x hx i j)
      (cov2_coefficient_differentiableAt v hv c x hx i j) a
    simp only [lieTensorInChart, cov2InChart_sub, Matrix.sub_apply]
    change (∑ a, (vectorInChart Y c x a *
      coordDeriv ((fun y => cov2InChart u c y i j) -
        (fun y => cov2InChart v c y i j)) a x + _ + _)) = _
    simp only [hd, mul_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold lieTensor
  rw [← cov2FromCoordinates_sub]
  funext p
  change cov2FromChartAt p p (lieTensorInChart Y (u - v) p (chartAt FourSpace p p)) =
    cov2FromChartAt p p ((lieTensorInChart Y u - lieTensorInChart Y v) p
      (chartAt FourSpace p p))
  congr 1
  ext i j
  exact hlocal p _ (mem_chart_target FourSpace p) i j

theorem nablaTensorInChart_sub (g u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    nablaTensorInChart g (u - v) c x a b d =
      nablaTensorInChart g u c x a b d - nablaTensorInChart g v c x a b d := by
  have hd := coordDeriv_sub
    (cov2_coefficient_differentiableAt u hu c x hx b d)
    (cov2_coefficient_differentiableAt v hv c x hx b d) a
  simp only [nablaTensorInChart, cov2InChart_sub, Matrix.sub_apply]
  change coordDeriv ((fun y => cov2InChart u c y b d) -
    (fun y => cov2InChart v c y b d)) a x - _ - _ = _
  rw [hd]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

@[simp] theorem metricTraceInChart_sub (g u v : RawCov2 M) (c : M) :
    metricTraceInChart g (u - v) c = metricTraceInChart g u c - metricTraceInChart g v c := by
  funext x
  simp [metricTraceInChart, mul_sub, Finset.sum_sub_distrib]

/-- A transparent sufficient hypothesis for the differentiability of each
metric trace. Smoothness of inversion is not silently assumed here. -/
theorem metricTraceInChart_differentiableAt (g u : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hinv : DifferentiableAt ℝ (inverseMetricInChart g c) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  unfold metricTraceInChart
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.fun_sum
  intro j _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hinv i) j).mul
    (cov2_coefficient_differentiableAt u hu c x hx i j)

/-- Bianchi subtraction follows from genuine differentiation of the tensor
coefficients and inverse metric. This is independent of naturality. -/
theorem bianchi_sub (g u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v)
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart g c) x) :
    bianchi g (u - v) = bianchi g u - bianchi g v := by
  have hlocal (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
      (j : Fin 4) :
      bianchiInChart g (u - v) c x j = bianchiInChart g u c x j - bianchiInChart g v c x j := by
    have hd := coordDeriv_sub
      (metricTraceInChart_differentiableAt g u hu c x hx (hinv c x hx))
      (metricTraceInChart_differentiableAt g v hv c x hx (hinv c x hx)) j
    simp only [bianchiInChart, metricTraceInChart_sub,
      nablaTensorInChart_sub g u v hu hv c x hx, hd, mul_sub, Finset.sum_sub_distrib]
    ring
  unfold bianchi
  rw [← covectorFromCoordinates_sub]
  funext p
  change covectorFromChartAt p p (bianchiInChart g (u - v) p (chartAt FourSpace p p)) =
    covectorFromChartAt p p ((bianchiInChart g u - bianchiInChart g v) p
      (chartAt FourSpace p p))
  congr 1
  ext j
  exact hlocal p _ (mem_chart_target FourSpace p) j

/-- The complete, unprojected actual-metric vector defect, including its
second Lie term. Input regularity of the reconstructed Lie tensors and
inverse metric is made explicit rather than inferred from missing chart
compatibility theorems. -/
theorem actualMetricVector_difference (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g)) (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x) :
    vectorOperator ghat g Y - vectorOperator z z Y =
      actualMetricVectorDefect ghat z g Y := by
  unfold vectorOperator actualMetricVectorDefect killing
  rw [lieTensor_sub Y g z hg hz, bianchi_sub ghat _ _ hLg hLz hinv]
  abel

@[simp] theorem actionPullbackCovector_sub (rho : CircleAction M) (t : Circle)
    (eta theta : RawCovector M) :
    actionPullbackCovector rho t (eta - theta) =
      actionPullbackCovector rho t eta - actionPullbackCovector rho t theta := by
  rfl

/-- Linearity of the genuine scalar Haar integrals uses their explicit
integrability premises, rather than the integral's default outside its domain. -/
theorem covectorPi0_sub (rho : CircleAction M) (eta theta : RawCovector M)
    (heta : CovectorHaarIntegrable rho eta) (htheta : CovectorHaarIntegrable rho theta) :
    covectorPi0 rho (eta - theta) = covectorPi0 rho eta - covectorPi0 rho theta := by
  unfold covectorPi0
  rw [← covectorFromCoordinates_sub]
  funext p
  change covectorFromChartAt p p _ = covectorFromChartAt p p _
  congr 1
  ext i
  simp only [actionPullbackCovector_sub, covectorInChart_sub, Pi.sub_apply]
  exact MeasureTheory.integral_sub
    (heta p _ (mem_chart_target FourSpace p) i)
    (htheta p _ (mem_chart_target FourSpace p) i)

theorem covectorPiPerp_sub (rho : CircleAction M) (eta theta : RawCovector M)
    (heta : CovectorHaarIntegrable rho eta) (htheta : CovectorHaarIntegrable rho theta) :
    covectorPiPerp rho (eta - theta) = covectorPiPerp rho eta - covectorPiPerp rho theta := by
  unfold covectorPiPerp
  rw [covectorPi0_sub rho eta theta heta htheta]
  abel

/-- The center vector difference needs only integrability to pass subtraction
through the common projection. -/
theorem projected_center_vector_difference (rho : CircleAction M)
    (ghat z : RawCov2 M) (Y : RawVector M)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat z Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y =
      covectorPiPerp rho (bianchi ghat (killing z Y) - bianchi z (killing z Y)) := by
  exact (covectorPiPerp_sub rho _ _ hfixed hcenter).symm

/-- K24's complete projected actual-metric vector defect under explicit
regularity and genuine Haar-integrability premises. -/
theorem projected_actual_vector_difference (rho : CircleAction M)
    (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g)) (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat g Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y := by
  unfold projectedVectorOperator projectedActualVectorDefect
  rw [← covectorPiPerp_sub rho _ _ hfixed hcenter,
    actualMetricVector_difference ghat z g Y hg hz hLg hLz hinv]

/-- A genuine invariant covector has constant orbit coefficients and hence
fiberwise Haar integrability. -/
theorem covectorHaarIntegrable_of_invariant (rho : CircleAction M) (eta : RawCovector M)
    (heta : IsInvariantCovector rho eta) : CovectorHaarIntegrable rho eta := by
  intro c x _ i
  unfold IsInvariantCovector at heta
  simp only [heta]
  exact MeasureTheory.integrable_const _

/-- The normalized scalar Haar integral fixes an invariant covector. Chart
reconstruction is justified by the actual inverse-chart differential theorem. -/
theorem covectorPi0_of_invariant [IsManifold I4 ∞ M]
    (rho : CircleAction M) (eta : RawCovector M) (heta : IsInvariantCovector rho eta) :
    covectorPi0 rho eta = eta := by
  unfold IsInvariantCovector at heta
  funext p
  change covectorFromChartAt p p (fun i =>
    ∫ t : Circle, covectorInChart (actionPullbackCovector rho t eta) p
      (chartAt FourSpace p p) i ∂circleHaar) = eta p
  simp only [heta, MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  exact covector_chart_recovery eta p p (mem_chart_source FourSpace p)

theorem covectorPiPerp_of_invariant [IsManifold I4 ∞ M]
    (rho : CircleAction M) (eta : RawCovector M) (heta : IsInvariantCovector rho eta) :
    covectorPiPerp rho eta = 0 := by
  rw [covectorPiPerp, covectorPi0_of_invariant rho eta heta, sub_self]

/-- Exact dangerous-term cancellation from invariance of the Bianchi output.
Establishing that invariance from invariant metrics still requires naturality. -/
theorem dangerous_term_zero_of_invariant [IsManifold I4 ∞ M]
    (rho : CircleAction M) (ghat z u : RawCov2 M)
    (hinv : IsInvariantCovector rho (bianchi ghat (z - ghat))) :
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0 := by
  exact dangerous_term_zero_of_cancellation rho ghat z u
    (covectorPiPerp_of_invariant rho _ hinv)

end K24.Global.Research20261024


namespace K24.Global
universe uM

theorem tensor_defect_identity_of_regular_bianchi
    {M : Type uM} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (lam : ℝ) (ghat z u : RawCov2 M)
    (hfixed : CovectorContDiff 1 (bianchi ghat u))
    (hcenter : CovectorContDiff 1 (bianchi z u)) :
    gaugedLinearization lam ghat z u - gaugedLinearization lam z z u =
      tensorDefect ghat z u := by
  exact Research20261024.gaugedLinearization_difference lam ghat z u hfixed hcenter
end K24.Global

namespace K24.Global
universe uM

theorem projected_actual_vector_defect_identity
    {M : Type uM} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (rho : CircleAction M) (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g))
    (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat g Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y := by
  exact Research20261024.projected_actual_vector_difference rho ghat z g Y
    hg hz hLg hLz hinv hfixed hcenter
end K24.Global

end

/- Inlined module: Closure -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global.GeometricRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem center_vector_difference_of_metricAdmissible (rho : CircleAction M)
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (ghat z : RawCov2 M)
    (hghat : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (Y : RawVector M) (hY : C.VectorHolder 2 b.exponent.value Y) :
    projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y =
      covectorPiPerp rho (bianchi ghat (killing z Y) - bianchi z (killing z Y)) := by
  exact Research20261024.projected_center_vector_difference rho ghat z Y
    (vectorOperator_haarIntegrable rho C b ghat z hghat hz Y hY)
    (vectorOperator_haarIntegrable rho C b z z hz hz Y hY)

theorem actual_vector_difference_of_metricAdmissible (rho : CircleAction M)
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (ghat z g : RawCov2 M)
    (hghat : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (hg : MetricAdmissible C b g)
    (Y : RawVector M) (hY : C.VectorHolder 2 b.exponent.value Y) :
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y := by
  apply Research20261024.projected_actual_vector_difference rho ghat z g Y
  · exact fun c => (cov2ContDiff_two_of_metricAdmissible C b g hg c).of_le (by norm_num)
  · exact fun c => (cov2ContDiff_two_of_metricAdmissible C b z hz c).of_le (by norm_num)
  · exact lieTensor_contDiff_one_of_metricAdmissible C b g hg Y hY
  · exact lieTensor_contDiff_one_of_metricAdmissible C b z hz Y hY
  · intro c x hx
    exact (inverseMetricInChart_contDiffAt 2 ghat hghat.metric c x hx
      ((cov2ContDiff_two_of_metricAdmissible C b ghat hghat c x hx).contDiffAt
        ((chartAt FourSpace c).open_target.mem_nhds hx))).differentiableAt (by norm_num)
  · exact vectorOperator_haarIntegrable rho C b ghat g hghat hg Y hY
  · exact vectorOperator_haarIntegrable rho C b z z hz hz Y hY

end K24.Global.GeometricRegularity

namespace K24.Global
universe u

theorem _root_.solution :
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics)
    (H : ℝ≥0), 1 ≤ H →
    ∃ CT CV : ℝ≥0, 0 < CT ∧ 0 < CV ∧
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
        (∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y =
            covectorPiPerp rho (bianchi ghat (killing z Y) - bianchi z (killing z Y))) ∧
        (∀ Y : RawVector M, C.VectorHolder 2 metricBounds.exponent.value Y →
          projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
            projectedActualVectorDefect rho ghat z g Y) := by
  intro coverBounds metricBounds H hH
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro M _ _ _ _ _ C hC rho hrho lam ghat z g hghat hz hg highat hiz
  constructor
  · intro Y hY
    exact GeometricRegularity.center_vector_difference_of_metricAdmissible rho C metricBounds
      ghat z hghat hz Y hY
  · intro Y hY
    exact GeometricRegularity.actual_vector_difference_of_metricAdmissible rho C metricBounds
      ghat z g hghat hz hg Y hY

end K24.Global
end
