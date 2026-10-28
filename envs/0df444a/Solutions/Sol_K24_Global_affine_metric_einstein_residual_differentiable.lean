-- Prove2me | solution 1 for K24.Global.affine_metric_einstein_residual_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:46:38.17145+00:00
-- url     : https://prove2.me/submissions/b19e1d26-3434-4a7f-80ef-02fa186d53c0

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false

/- Checked source module: Regularity. -/
section K24StandalonePart0

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

namespace K24.Global.PrincipalSymbolRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
open Matrix
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


theorem contDiffAt_inverseMetric [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (n : ℕ∞ω)
    (hDg : ContDiffAt ℝ n (cov2InChart g c) x) :
    ContDiffAt ℝ n (inverseMetricInChart g c) x := by
  have hentry (a b : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hDg a) b
  have hdet : ContDiffAt ℝ n (fun y => (cov2InChart g c y).det) x := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply ContDiffAt.mul contDiffAt_const
    exact contDiffAt_prod (fun i _ => hentry (σ i) i)
  have hne : (cov2InChart g c x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (cov2InChart_isUnit_det g hg c x hx)
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
  apply ContDiffAt.mul contDiffAt_const
  apply contDiffAt_prod
  intro i _
  simp only [Matrix.updateRow_apply]
  split_ifs <;> first | exact contDiffAt_const | exact hentry _ _

theorem christoffel_differentiableAt [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x) (d a b : Fin 4) :
    DifferentiableAt ℝ (fun y => christoffelInChart g c y d a b) x := by
  have hentry (i j : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hDg i) j
  have hInv := (contDiffAt_inverseMetric g hg c x hx 2 hDg).differentiableAt (by norm_num)
  have hDeriv (i j k : Fin 4) : DifferentiableAt ℝ
      (coordDeriv (fun y => cov2InChart g c y j k) i) x :=
    (((hentry j k).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  unfold christoffelInChart
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro p _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hInv d) p).mul
    (((hDeriv a b p).add (hDeriv b a p)).sub (hDeriv p a b))

end K24.Global.PrincipalSymbolRegularity
end
end K24StandalonePart0

/- Checked source module: JetCalculus. -/
section K24StandalonePart1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.AffineMetricVariation

abbrev FirstJet := Mat4 × (FourSpace →L[ℝ] Mat4)

def firstJet (A : FourSpace → Mat4) (x : FourSpace) : FirstJet :=
  (A x, fderiv ℝ A x)

def gammaJet (k i j : Fin 4) (J : FirstJet) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, J.1⁻¹ k l *
    (J.2 (basisVector i) j l + J.2 (basisVector j) i l - J.2 (basisVector l) i j)

theorem contDiffAt_matrixInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Mat4) (x : E) (n : ℕ∞ω) (hA : ContDiffAt ℝ n A x)
    (hne : (A x).det ≠ 0) : ContDiffAt ℝ n (fun y => (A y)⁻¹) x := by
  have hentry (a b : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hA a) b
  have hdet : ContDiffAt ℝ n (fun y => (A y).det) x := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply ContDiffAt.mul contDiffAt_const
    exact contDiffAt_prod (fun i _ => hentry (σ i) i)
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  apply (hdet.inv hne).mul
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply ContDiffAt.mul contDiffAt_const
  apply contDiffAt_prod
  intro i _
  simp only [Matrix.updateRow_apply]
  split_ifs <;> first | exact contDiffAt_const | exact hentry _ _

theorem gammaJet_smooth (k i j : Fin 4) (J : FirstJet) (hne : J.1.det ≠ 0) :
    ContDiffAt ℝ ∞ (gammaJet k i j) J := by
  have hInv := contDiffAt_matrixInverse (fun J : FirstJet => J.1) J ∞
    contDiffAt_fst hne
  have hD (r a b : Fin 4) :
      ContDiffAt ℝ ∞ (fun J : FirstJet => J.2 (basisVector r) a b) J := by
    have he : ContDiffAt ℝ ∞ (fun J : FirstJet => J.2 (basisVector r)) J :=
      contDiffAt_snd.clm_apply contDiffAt_const
    exact contDiffAt_pi.mp (contDiffAt_pi.mp he a) b
  unfold gammaJet
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hInv k) l).mul
    (((hD i j l).add (hD j i l)).sub (hD l i j))

theorem coordDeriv_entry (A : FourSpace → Mat4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) (k i j : Fin 4) :
    coordDeriv (fun y => A y i j) k x = fderiv ℝ A x (basisVector k) i j := by
  unfold coordDeriv
  rw [fderiv_apply (differentiableAt_pi.mp hA i) j, fderiv_apply hA i]
  rfl

theorem firstJet_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ContDiffAt ℝ 2 A x) : DifferentiableAt ℝ (firstJet A) x := by
  exact (hA.differentiableAt (by norm_num)).prodMk
    ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem firstJet_derivative (A : FourSpace → Mat4) (x v : FourSpace)
    (hA : ContDiffAt ℝ 2 A x) :
    fderiv ℝ (firstJet A) x v =
      (fderiv ℝ A x v, fderiv ℝ (fderiv ℝ A) x v) := by
  exact congrArg (fun D : FourSpace →L[ℝ] FirstJet => D v)
    (((hA.differentiableAt (by norm_num)).hasFDerivAt.prodMk
      ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasFDerivAt).fderiv)

def affineCoefficients (Z U : FourSpace → Mat4) (t : ℝ) : FourSpace → Mat4 :=
  fun y => Z y + t • U y

theorem affineCoefficients_contDiffAt (Z U : FourSpace → Mat4) (x : FourSpace)
    (hZ : ContDiffAt ℝ 2 Z x) (hU : ContDiffAt ℝ 2 U x) (t : ℝ) :
    ContDiffAt ℝ 2 (affineCoefficients Z U t) x := hZ.add (hU.const_smul t)

theorem affineCoefficients_fderiv (Z U : FourSpace → Mat4) (x : FourSpace)
    (hZ : DifferentiableAt ℝ Z x) (hU : DifferentiableAt ℝ U x) (t : ℝ) :
    fderiv ℝ (affineCoefficients Z U t) x = fderiv ℝ Z x + t • fderiv ℝ U x := by
  exact (hZ.hasFDerivAt.add (hU.hasFDerivAt.const_smul t)).fderiv

theorem affineCoefficients_second (Z U : FourSpace → Mat4) (x : FourSpace)
    (hZ : ContDiffAt ℝ 2 Z x) (hU : ContDiffAt ℝ 2 U x) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (affineCoefficients Z U t)) x =
      fderiv ℝ (fderiv ℝ Z) x + t • fderiv ℝ (fderiv ℝ U) x := by
  have he : fderiv ℝ (affineCoefficients Z U t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ Z y + t • fderiv ℝ U y) := by
    filter_upwards [hZ.eventually (by norm_num), hU.eventually (by norm_num)] with y hZy hUy
    exact affineCoefficients_fderiv Z U y (hZy.differentiableAt (by norm_num))
      (hUy.differentiableAt (by norm_num)) t
  have hDZ := (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDU := (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [he.fderiv_eq]
  exact (hDZ.hasFDerivAt.add (hDU.hasFDerivAt.const_smul t)).fderiv

theorem affine_firstJet_smooth (Z U : FourSpace → Mat4) (x : FourSpace)
    (hZ : DifferentiableAt ℝ Z x) (hU : DifferentiableAt ℝ U x) :
    ContDiff ℝ ∞ (fun t : ℝ => firstJet (affineCoefficients Z U t) x) := by
  simp only [firstJet, affineCoefficients_fderiv Z U x hZ hU, affineCoefficients]
  fun_prop

theorem affine_secondJet_smooth (Z U : FourSpace → Mat4) (x v : FourSpace)
    (hZ : ContDiffAt ℝ 2 Z x) (hU : ContDiffAt ℝ 2 U x) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      (fderiv ℝ (affineCoefficients Z U t) x v,
       fderiv ℝ (fderiv ℝ (affineCoefficients Z U t)) x v)) := by
  simp only [affineCoefficients_fderiv Z U x (hZ.differentiableAt (by norm_num))
    (hU.differentiableAt (by norm_num)), affineCoefficients_second Z U x hZ hU]
  fun_prop

end K24.Global.AffineMetricVariation
end
end K24StandalonePart1

/- Checked source module: ChristoffelVariation. -/
section K24StandalonePart2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.AffineMetricVariation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem cov2InChart_affine (z u : RawCov2 M) (c : M) (t : ℝ) :
    cov2InChart (z + t • u) c =
      affineCoefficients (cov2InChart z c) (cov2InChart u c) t := by
  funext y i j
  rfl

theorem christoffel_eq_gammaJet (g : RawCov2 M) (c : M) (x : FourSpace)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) (k i j : Fin 4) :
    christoffelInChart g c x k i j = gammaJet k i j (firstJet (cov2InChart g c) x) := by
  simp only [christoffelInChart, inverseMetricInChart, gammaJet, firstJet,
    coordDeriv_entry _ x hDg]

theorem christoffel_spatial_derivative (g : RawCov2 M) (c : M) (x : FourSpace)
    (hDg : ContDiffAt ℝ 2 (cov2InChart g c) x)
    (hne : (cov2InChart g c x).det ≠ 0) (r k i j : Fin 4) :
    coordDeriv (fun y => christoffelInChart g c y k i j) r x =
      fderiv ℝ (gammaJet k i j) (firstJet (cov2InChart g c) x)
        (fderiv ℝ (cov2InChart g c) x (basisVector r),
         fderiv ℝ (fderiv ℝ (cov2InChart g c)) x (basisVector r)) := by
  have he : (fun y => christoffelInChart g c y k i j) =ᶠ[𝓝 x]
      (fun y => gammaJet k i j (firstJet (cov2InChart g c) y)) := by
    filter_upwards [hDg.eventually (by norm_num)] with y hy
    exact christoffel_eq_gammaJet g c y (hy.differentiableAt (by norm_num)) k i j
  have hg := (gammaJet_smooth k i j (firstJet (cov2InChart g c) x) hne).differentiableAt
    (by simp)
  unfold coordDeriv
  rw [he.fderiv_eq, fderiv_fun_comp x hg (firstJet_differentiableAt _ x hDg)]
  simp only [ContinuousLinearMap.comp_apply, firstJet_derivative _ x _ hDg]

theorem affine_christoffel_smooth (z u : RawCov2 M) (c : M) (x : FourSpace)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x)
    (hDu : ContDiffAt ℝ 2 (cov2InChart u c) x)
    (hne : (cov2InChart z c x).det ≠ 0) (k i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ => christoffelInChart (z + t • u) c x k i j) 0 := by
  let J : ℝ → FirstJet := fun t => firstJet (cov2InChart (z + t • u) c) x
  have hJ : ContDiff ℝ ∞ J := by
    simp only [J, cov2InChart_affine]
    exact affine_firstJet_smooth _ _ x (hDz.differentiableAt (by norm_num))
      (hDu.differentiableAt (by norm_num))
  have hJne : (J 0).1.det ≠ 0 := by
    change (cov2InChart (z + (0 : ℝ) • u) c x).det ≠ 0
    rw [cov2InChart_affine]
    simpa only [affineCoefficients, zero_smul, add_zero] using hne
  have hs := (gammaJet_smooth k i j (J 0) hJne).comp 0 hJ.contDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [] with t
  apply christoffel_eq_gammaJet
  rw [cov2InChart_affine]
  exact (affineCoefficients_contDiffAt _ _ x hDz hDu t).differentiableAt (by norm_num)

theorem affine_christoffel_spatial_derivative_smooth (z u : RawCov2 M)
    (c : M) (x : FourSpace)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x)
    (hDu : ContDiffAt ℝ 2 (cov2InChart u c) x)
    (hne : (cov2InChart z c x).det ≠ 0) (r k i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ =>
      coordDeriv (fun y => christoffelInChart (z + t • u) c y k i j) r x) 0 := by
  let J : ℝ → FirstJet := fun t => firstJet (cov2InChart (z + t • u) c) x
  let K : ℝ → FirstJet := fun t =>
    (fderiv ℝ (cov2InChart (z + t • u) c) x (basisVector r),
     fderiv ℝ (fderiv ℝ (cov2InChart (z + t • u) c)) x (basisVector r))
  have hJ : ContDiff ℝ ∞ J := by
    simp only [J, cov2InChart_affine]
    exact affine_firstJet_smooth _ _ x (hDz.differentiableAt (by norm_num))
      (hDu.differentiableAt (by norm_num))
  have hK : ContDiff ℝ ∞ K := by
    simp only [K, cov2InChart_affine]
    exact affine_secondJet_smooth _ _ x (basisVector r) hDz hDu
  have hJne : (J 0).1.det ≠ 0 := by
    change (cov2InChart (z + (0 : ℝ) • u) c x).det ≠ 0
    rw [cov2InChart_affine]
    simpa only [affineCoefficients, zero_smul, add_zero] using hne
  have hGamma : ContDiffAt ℝ ∞ (fderiv ℝ (gammaJet k i j)) (J 0) :=
    (gammaJet_smooth k i j (J 0) hJne).fderiv_right (by simp)
  have hs : ContDiffAt ℝ ∞ (fun t => fderiv ℝ (gammaJet k i j) (J t) (K t)) 0 :=
    (hGamma.comp 0 hJ.contDiffAt).clm_apply hK.contDiffAt
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), (J t).1.det ≠ 0 :=
    (hJ.continuous.fst.matrix_det.continuousAt).eventually_ne hJne
  apply hs.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  apply christoffel_spatial_derivative
  · rw [cov2InChart_affine]
    exact affineCoefficients_contDiffAt _ _ x hDz hDu t
  · exact ht

end K24.Global.AffineMetricVariation
end
end K24StandalonePart2

/- Checked source module: Solution. -/
section K24StandalonePart3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology

namespace K24.Global.AffineMetricVariation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem affine_curvature_smooth (z u : RawCov2 M) (c : M) (x : FourSpace)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x)
    (hDu : ContDiffAt ℝ 2 (cov2InChart u c) x)
    (hne : (cov2InChart z c x).det ≠ 0) (l i j k : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ => curvatureInChart (z + t • u) c x l i j k) 0 := by
  have hG := affine_christoffel_smooth z u c x hDz hDu hne
  have hDG := affine_christoffel_spatial_derivative_smooth z u c x hDz hDu hne
  unfold curvatureInChart
  apply ((hDG i l j k).sub (hDG j l i k)).add
  apply ContDiffAt.sum
  intro p _
  exact ((hG l i p).mul (hG p j k)).sub ((hG l j p).mul (hG p i k))

theorem affine_ricci_smooth (z u : RawCov2 M) (c : M) (x : FourSpace)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x)
    (hDu : ContDiffAt ℝ 2 (cov2InChart u c) x)
    (hne : (cov2InChart z c x).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ => ricciInChart (z + t • u) c x i j) 0 := by
  apply ContDiffAt.sum
  intro k _
  exact affine_curvature_smooth z u c x hDz hDu hne k k i j

theorem affine_einsteinResidual_smooth_local (z u : RawCov2 M) (c : M) (x : FourSpace)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x)
    (hDu : ContDiffAt ℝ 2 (cov2InChart u c) x)
    (hne : (cov2InChart z c x).det ≠ 0) (lam : ℝ) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ => einsteinResidualInChart lam (z + t • u) c x i j) 0 := by
  have hA : ContDiffAt ℝ ∞ (fun t : ℝ => cov2InChart (z + t • u) c x i j) 0 := by
    simp only [cov2InChart_affine, affineCoefficients]
    fun_prop
  exact (affine_ricci_smooth z u c x hDz hDu hne i j).sub (contDiffAt_const.mul hA)

variable [IsManifold I4 ∞ M]

theorem affine_einsteinResidual_smooth (z u : RawCov2 M) (hz : IsMetric z)
    (hDz : Cov2ContDiff 2 z) (hDu : Cov2ContDiff 2 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (lam : ℝ) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ => einsteinResidualInChart lam (z + t • u) c x i j) 0 := by
  exact affine_einsteinResidual_smooth_local z u c x
    ((hDz c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx))
    ((hDu c x hx).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx))
    (isUnit_iff_ne_zero.mp (PrincipalSymbolRegularity.cov2InChart_isUnit_det z hz c x hx))
    lam i j

theorem affine_einsteinResidual_differentiable (z u : RawCov2 M) (hz : IsMetric z)
    (hDz : Cov2ContDiff 2 z) (hDu : Cov2ContDiff 2 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (lam : ℝ) (i j : Fin 4) :
    DifferentiableAt ℝ
      (fun t : ℝ => einsteinResidualInChart lam (z + t • u) c x i j) 0 :=
  (affine_einsteinResidual_smooth z u hz hDz hDu c x hx lam i j).differentiableAt (by simp)

theorem affine_einsteinResidual_differentiable_of_admissible
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (alpha : ℝ≥0)
    (z u : RawCov2 M) (hz : MetricAdmissible C b z) (hu : C.Cov2Holder 2 alpha u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (lam : ℝ) (i j : Fin 4) :
    DifferentiableAt ℝ
      (fun t : ℝ => einsteinResidualInChart lam (z + t • u) c x i j) 0 := by
  apply affine_einsteinResidual_differentiable z u hz.metric
  · intro d
    exact (cov2ContDiff_of_metricAdmissible C b z hz d).of_le
      (by exact_mod_cast b.order_ge_two)
  · exact cov2ContDiff_of_cov2Holder C 2 alpha u hu
  · exact hx

end K24.Global.AffineMetricVariation

universe u
open K24.Global

theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M],
      ∀ (z u : RawCov2 M), IsMetric z → Cov2ContDiff 2 z → Cov2ContDiff 2 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ (lam : ℝ) (i j : Fin 4),
            DifferentiableAt ℝ
              (fun t : ℝ => einsteinResidualInChart lam (z + t • u) c x i j) 0 := by
  intro M _ _ _ z u hz hDz hDu c x hx lam i j
  exact AffineMetricVariation.affine_einsteinResidual_differentiable z u hz hDz hDu
    c x hx lam i j
end
end K24StandalonePart3
