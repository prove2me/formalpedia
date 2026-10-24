-- Prove2me | solution 1 for K24.Global.bianchi_difference
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:00:58.045998+00:00
-- url     : https://prove2.me/submissions/354467d1-c25d-4eb3-9e26-d3e31a896ee4

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
open Matrix

namespace K24.Global.BianchiProof

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

theorem contraction_leibniz (A U dA dU : Mat4)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (j : Fin 4) :
    (∑ a, ∑ b, (dA a b * U a b + A a b * dU a b)) =
    (∑ a, ∑ b, A a b * (dU a b - (∑ p, G p j a * U p b) -
      (∑ p, G p j b * U a p))) +
    (∑ a, ∑ b, (dA a b + (∑ p, G a j p * A p b) +
      (∑ p, G b j p * A a p)) * U a b) := by
  have h₁ : (∑ a, ∑ b, ∑ p, A a b * (G p j a * U p b)) =
      ∑ a, ∑ b, ∑ p, (G a j p * A p b) * U a b := by
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h₂ : (∑ a, ∑ b, ∑ p, A a b * (G p j b * U a p)) =
      ∑ a, ∑ b, ∑ p, (G b j p * A a p) * U a b := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp only [mul_sub, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  rw [h₁, h₂]
  ring

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

theorem coordDeriv_contract (A U : FourSpace → Mat4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hU : DifferentiableAt ℝ U x) (j : Fin 4) :
    coordDeriv (fun y => ∑ a, ∑ b, A y a b * U y a b) j x =
      ∑ a, ∑ b, (coordDeriv (fun y => A y a b) j x * U x a b +
        A x a b * coordDeriv (fun y => U y a b) j x) := by
  have hA' (a b : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hA a) b
  have hU' (a b : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hU a) b
  unfold coordDeriv
  rw [fderiv_fun_sum (A := fun a y => ∑ b, A y a b * U y a b) (u := Finset.univ) (fun a _ => DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ => (hA' a b).mul (hU' a b)))]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_fun_sum (A := fun b y => A y a b * U y a b) (u := Finset.univ) (fun b _ => (hA' a b).mul (hU' a b))]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [fderiv_fun_mul (hA' a b) (hU' a b)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem differentiableAt_contract (A U : FourSpace → Mat4) (x : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hU : DifferentiableAt ℝ U x) :
    DifferentiableAt ℝ (fun y => ∑ a, ∑ b, A y a b * U y a b) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hA a) b).mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp hU a) b)

theorem trace_difference (ghat z u : RawCov2 M) (c : M) (x : FourSpace)
    (hA : DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hB : DifferentiableAt ℝ (inverseMetricInChart z c) x)
    (hU : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    coordDeriv (metricTraceInChart ghat u c) j x -
      coordDeriv (metricTraceInChart z u c) j x =
      (∑ a, ∑ b, inverseDifferenceInChart ghat z c x a b *
        nablaTensorInChart z u c x j a b) +
      (∑ a, ∑ b, nablaContravariantInChart z
        (inverseDifferenceInChart ghat z) c x j a b * cov2InChart u c x a b) := by
  have hdiff : DifferentiableAt ℝ (inverseDifferenceInChart ghat z c) x := hA.sub hB
  have htraceA : DifferentiableAt ℝ (metricTraceInChart ghat u c) x :=
    differentiableAt_contract _ _ x hA hU
  have htraceB : DifferentiableAt ℝ (metricTraceInChart z u c) x :=
    differentiableAt_contract _ _ x hB hU
  have heq : (metricTraceInChart ghat u c - metricTraceInChart z u c) =
      (fun y => ∑ a, ∑ b, inverseDifferenceInChart ghat z c y a b * cov2InChart u c y a b) := by
    funext y
    simp only [Pi.sub_apply, metricTraceInChart, inverseDifferenceInChart,
      Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hd : coordDeriv (metricTraceInChart ghat u c) j x -
      coordDeriv (metricTraceInChart z u c) j x =
      coordDeriv (fun y => ∑ a, ∑ b,
        inverseDifferenceInChart ghat z c y a b * cov2InChart u c y a b) j x := by
    rw [← heq]
    unfold coordDeriv
    rw [fderiv_sub htraceA htraceB]
    rfl
  rw [hd, coordDeriv_contract _ _ x hdiff hU j]
  exact contraction_leibniz (inverseDifferenceInChart ghat z c x) (cov2InChart u c x)
    (fun a b => coordDeriv (fun y => inverseDifferenceInChart ghat z c y a b) j x)
    (fun a b => coordDeriv (fun y => cov2InChart u c y a b) j x)
    (christoffelInChart z c x) j

theorem divergence_difference (ghat z u : RawCov2 M) (c : M) (x : FourSpace)
    (j : Fin 4) :
    -(∑ a, ∑ b, inverseMetricInChart ghat c x a b * nablaTensorInChart ghat u c x a b j) +
      (∑ a, ∑ b, inverseMetricInChart z c x a b * nablaTensorInChart z u c x a b j) =
    -(∑ a, ∑ b, inverseDifferenceInChart ghat z c x a b * nablaTensorInChart z u c x a b j) +
    (∑ a, ∑ b, ∑ p, inverseMetricInChart ghat c x a b *
      connectionDifferenceInChart ghat z c x p a b * cov2InChart u c x p j) +
    (∑ a, ∑ b, ∑ p, inverseMetricInChart ghat c x a b *
      connectionDifferenceInChart ghat z c x p a j * cov2InChart u c x b p) := by
  have hN (a b : Fin 4) : nablaTensorInChart ghat u c x a b j =
      nablaTensorInChart z u c x a b j -
      (∑ p, connectionDifferenceInChart ghat z c x p a b * cov2InChart u c x p j) -
      (∑ p, connectionDifferenceInChart ghat z c x p a j * cov2InChart u c x b p) := by
    simp only [nablaTensorInChart, connectionDifferenceInChart, sub_mul,
      Finset.sum_sub_distrib]
    ring
  simp only [hN, inverseDifferenceInChart, Matrix.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, ← mul_assoc]
  ring

theorem bianchi_difference_of_inverse_differentiableAt
    (ghat z u : RawCov2 M) (c : M) (x : FourSpace)
    (hA : DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hB : DifferentiableAt ℝ (inverseMetricInChart z c) x)
    (hU : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  have hd := divergence_difference ghat z u c x j
  have ht := trace_difference ghat z u c x hA hB hU j
  unfold bianchiInChart bianchiDifferenceExpansion
  linarith

end K24.Global.BianchiProof


namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem bianchi_difference_of_differentiableAt
    [IsManifold I4 ∞ M] (ghat z u : RawCov2 M)
    (hghat : IsMetric ghat) (hz : IsMetric z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDghat : DifferentiableAt ℝ (cov2InChart ghat c) x)
    (hDz : DifferentiableAt ℝ (cov2InChart z c) x)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  exact BianchiProof.bianchi_difference_of_inverse_differentiableAt ghat z u c x
    (BianchiProof.differentiableAt_inverseMetric ghat hghat c x hx hDghat)
    (BianchiProof.differentiableAt_inverseMetric z hz c x hx hDz) hDu j

theorem bianchi_difference_of_cov2ContDiff
    [IsManifold I4 ∞ M] (ghat z u : RawCov2 M)
    (hghat : IsMetric ghat) (hz : IsMetric z)
    (hDghat : Cov2ContDiff 1 ghat) (hDz : Cov2ContDiff 1 z)
    (hDu : Cov2ContDiff 1 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  apply bianchi_difference_of_differentiableAt ghat z u hghat hz c x hx
  · exact ((hDghat c).differentiableOn (by simp) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  · exact ((hDz c).differentiableOn (by simp) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  · exact ((hDu c).differentiableOn (by simp) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)

theorem bianchi_difference_of_sobolev_admissible
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (P : SobolevPartition C)
    (L : SobolevLocalizers C) (s : ℝ) (b : SobolevMetricNumerics)
    (ghat z u : RawCov2 M)
    (hghat : MetricSobolevAdmissible C L s b ghat)
    (hz : MetricSobolevAdmissible C L s b z) (hu : P.Cov2Sobolev 2 s u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  apply bianchi_difference_of_cov2ContDiff ghat z u hghat.metric hz.metric
  · intro c
    exact (hghat.representative c).of_le (by norm_num)
  · intro c
    exact (hz.representative c).of_le (by norm_num)
  · intro c
    exact (hu.1 c).of_le (by norm_num)
  · exact hx

universe u

theorem _root_.solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M],
      ∀ (ghat z u : RawCov2 M), IsMetric ghat → IsMetric z →
        Cov2ContDiff 1 ghat → Cov2ContDiff 1 z → Cov2ContDiff 1 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ j : Fin 4, bianchiInChart ghat u c x j - bianchiInChart z u c x j =
            bianchiDifferenceExpansion ghat z u c x j := by
  intro M _ _ _ ghat z u hghat hz hDghat hDz hDu c x hx j
  exact bianchi_difference_of_cov2ContDiff ghat z u hghat hz hDghat hDz hDu c x hx j

end K24.Global
