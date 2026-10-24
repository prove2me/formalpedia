-- Prove2me | solution 1 for K24.Global.cover_second_nabla_commutator
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:03:23.628255+00:00
-- url     : https://prove2.me/submissions/deb133ba-34d4-4067-ae24-9a98668caa4b

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

open K24.Global in
theorem solution :
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ (C : BoundedLocalCover M) (bounds : MetricCoefficientNumerics)
        (z : RawCov2 M), MetricAdmissible C bounds z →
        ∀ (Y : RawVector M), C.VectorHolder 2 bounds.exponent.value Y →
          ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
            ∀ a b d : Fin 4,
              secondNablaVectorInChart z Y c x a b d -
                secondNablaVectorInChart z Y c x b a d =
                  ∑ p : Fin 4, curvatureInChart z c x d a b p * vectorInChart Y c x p :=
  secondNablaVector_commutator
