-- Prove2me | solution 1 for K24.Global.cover_partial_gauge_product_rule
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:12:42.526718+00:00
-- url     : https://prove2.me/submissions/ef7e98dd-7365-4977-8820-320c23540402

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false

/- Checked source module: Infrastructure. -/
section ProductStandalonePart0
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
end
end ProductStandalonePart0

/- Checked source module: Connection. -/
section ProductStandalonePart1
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
end
end ProductStandalonePart1

/- Checked source module: Covariant. -/
section ProductStandalonePart2
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
end ProductStandalonePart2

/- Checked source module: TraceBasics. -/
section ProductStandalonePart3
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
end ProductStandalonePart3

/- Checked source module: Contraction. -/
section ProductStandalonePart4
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
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
end ProductStandalonePart4

/- Checked source module: BianchiRecovery. -/
section ProductStandalonePart5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
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
end ProductStandalonePart5

/- Checked source module: Regularity. -/
section ProductStandalonePart6

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
end ProductStandalonePart6

/- Checked source module: LocalCovariance. -/
section ProductStandalonePart7
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter Matrix
namespace K24.Global.BianchiInvariance
open LieNaturality IdentityProof BianchiNaturality BianchiContraction
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem cov2_differentiableAt (u : RawCov2 M) (hu : Cov2ContDiff 1 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    DifferentiableAt ℝ (cov2InChart u c) x :=
  ((hu c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)

theorem jacobian_bijective_of_metric_pullback (g : RawCov2 M) (hg : IsMetric g)
    (c d : M) (x y : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (J : FourSpace →L[ℝ] FourSpace)
    (hG : formInChart g c x = bilinearPullback (formInChart g d y) J) :
    Function.Bijective J := by
  have hinj : Function.Injective J := by
    intro v w hvw
    apply formInChart_separates g hg c x hx v w
    intro t
    rw [hG]
    simp only [bilinearPullback_apply, hvw]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := J.toLinearMap)).mp hinj⟩

theorem gammaForm_natural_local (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hy : F x ∈ (chartAt FourSpace d).target) (hF : ContDiffAt ℝ 2 F x)
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart g d (F y)) (fderiv ℝ F y)))
    (v w : FourSpace) :
    fderiv ℝ F x (gammaForm g c x v w) =
      gammaForm g d (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) +
      fderiv ℝ (fderiv ℝ F) x v w := by
  have hgc := cov2_differentiableAt g hDg c x hx
  have hgd := cov2_differentiableAt g hDg d (F x) hy
  apply formInChart_separates g hg d (F x) hy
  intro t
  obtain ⟨r, rfl⟩ := (jacobian_bijective_of_metric_pullback g hg c d x (F x) hx
    (fderiv ℝ F x) hG.self_of_nhds).2 t
  have hpoint := congrArg (fun Q : Form => Q (gammaForm g c x v w) r) hG.self_of_nhds
  change formInChart g c x (gammaForm g c x v w) r =
    formInChart g d (F x) (fderiv ℝ F x (gammaForm g c x v w)) (fderiv ℝ F x r) at hpoint
  have hK := koszulForm_natural (formInChart g d) (formInChart g c) F x hF
    (formInChart_differentiableAt g d (F x) hgd)
    (formInChart_differentiableAt g c x hgc)
    (formInChart_symmetric g hg.1 d (F x)) hG v w r
  rw [← gammaForm_lower g hg c x hx hgc v w r,
    ← gammaForm_lower g hg d (F x) hy hgd, hpoint] at hK
  simp only [map_add, _root_.add_apply]
  linarith

theorem nablaForm_natural_local (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (hDu : Cov2ContDiff 1 u)
    (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hy : F x ∈ (chartAt FourSpace d).target) (hF : ContDiffAt ℝ 2 F x)
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart g d (F y)) (fderiv ℝ F y)))
    (hU : formInChart u c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart u d (F y)) (fderiv ℝ F y)))
    (v w t : FourSpace) :
    nablaForm g u c x v w t = nablaForm g u d (F x)
      (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x t) := by
  simp only [nablaForm_apply]
  rw [fderiv_pullback_relation (formInChart u d) (formInChart u c) F x hF
    (formInChart_differentiableAt u d _ (cov2_differentiableAt u hDu d _ hy))
    (formInChart_differentiableAt u c x (cov2_differentiableAt u hDu c x hx)) hU]
  rw [hU.self_of_nhds]
  simp only [bilinearPullback_apply, gammaForm_natural_local g hg hDg c d F x hx hy hF hG,
    map_add, _root_.add_apply]
  ring

theorem metricTrace_eq_of_pullback (g u : RawCov2 M) (hg : IsMetric g)
    (c d : M) (x y : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hy : y ∈ (chartAt FourSpace d).target) (J : FourSpace →L[ℝ] FourSpace)
    (hG : formInChart g c x = bilinearPullback (formInChart g d y) J)
    (hU : formInChart u c x = bilinearPullback (formInChart u d y) J) :
    metricTraceInChart g u c x = metricTraceInChart g u d y := by
  have hC := contract_natural J (jacobian_bijective_of_metric_pullback g hg c d x y hx J hG)
    (cov2InChart g c x) (cov2InChart g d y)
    (cov2InChart_isUnit_det g hg c x hx) (cov2InChart_isUnit_det g hg d y hy)
    (fun v w => congrArg (fun A : Form => A v w) hG) (formInChart u d y)
  have hu (i j : Fin 4) : cov2InChart u c x i j =
      formInChart u d y (J (basisVector i)) (J (basisVector j)) := by
    simpa only [bilinearPullback_apply, formInChart, Function.comp_apply, matrixToForm_basis] using
      congrArg (fun A : Form => A (basisVector i) (basisVector j)) hU
  unfold metricTraceInChart inverseMetricInChart
  simp_rw [hu]
  simpa only [formInChart, Function.comp_apply, matrixToForm_basis] using hC

theorem divergenceForm_natural_local (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (hDu : Cov2ContDiff 1 u)
    (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hy : F x ∈ (chartAt FourSpace d).target) (hF : ContDiffAt ℝ 2 F x)
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart g d (F y)) (fderiv ℝ F y)))
    (hU : formInChart u c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart u d (F y)) (fderiv ℝ F y))) (t : FourSpace) :
    divergenceForm g u c x t = divergenceForm g u d (F x) (fderiv ℝ F x t) := by
  have hC := contract_natural (fderiv ℝ F x)
    (jacobian_bijective_of_metric_pullback g hg c d x (F x) hx (fderiv ℝ F x) hG.self_of_nhds)
    (cov2InChart g c x) (cov2InChart g d (F x))
    (cov2InChart_isUnit_det g hg c x hx) (cov2InChart_isUnit_det g hg d (F x) hy)
    (fun v w => congrArg (fun A : Form => A v w) hG.self_of_nhds)
    (cov3Slice (nablaForm g u d (F x)) (fderiv ℝ F x t))
  simp only [divergenceForm_apply]
  simp_rw [nablaForm_natural_local g u hg hDg hDu c d F x hx hy hF hG hU]
  simpa only [cov3Slice_apply, inverseMetricInChart] using hC

theorem bianchiForm_natural_local (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (hDu : Cov2ContDiff 1 u)
    (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hy : F x ∈ (chartAt FourSpace d).target) (hF : ContDiffAt ℝ 2 F x)
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart g d (F y)) (fderiv ℝ F y)))
    (hU : formInChart u c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart u d (F y)) (fderiv ℝ F y))) (t : FourSpace) :
    bianchiForm g u c x t = bianchiForm g u d (F x) (fderiv ℝ F x t) := by
  have htrace : metricTraceInChart g u c =ᶠ[𝓝 x] (fun y => metricTraceInChart g u d (F y)) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx,
      hF.continuousAt.tendsto ((chartAt FourSpace d).open_target.mem_nhds hy), hG, hU]
      with y hcy hdy hGy hUy
    exact metricTrace_eq_of_pullback g u hg c d y (F y) hcy hdy (fderiv ℝ F y) hGy hUy
  have hder := htrace.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x
    (metricTraceInChart_differentiableAt g u hg d (F x) hy
      (cov2_differentiableAt g hDg d _ hy) (cov2_differentiableAt u hDu d _ hy))
    (hF.differentiableAt (by norm_num))] at hder
  simp only [bianchiForm_apply, divergenceForm_natural_local g u hg hDg hDu c d F x hx hy hF hG hU]
  rw [congrArg (fun D : FourSpace →L[ℝ] ℝ => D t) hder]
  rfl

end K24.Global.BianchiInvariance
end
end ProductStandalonePart7

/- Checked source module: ActionDefinitions. -/
section ProductStandalonePart8
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace K24.Global.BianchiInvariance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
def actionInCharts (rho : CircleAction M) (t : Circle) (c d : M) : FourSpace → FourSpace :=
  (chartAt FourSpace d) ∘ (rho.act t) ∘ (chartAt FourSpace c).symm
end K24.Global.BianchiInvariance
end
end ProductStandalonePart8

/- Checked source module: ActionCoordinates. -/
section ProductStandalonePart9
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
end
end ProductStandalonePart9

/- Checked source module: ZeroHaar. -/
section ProductStandalonePart10
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.BianchiInvariance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

@[simp] theorem covectorInChart_zero (c : M) (x : FourSpace) :
    covectorInChart (0 : RawCovector M) c x = 0 := rfl

@[simp] theorem cov2InChart_zero (c : M) (x : FourSpace) :
    cov2InChart (0 : RawCov2 M) c x = 0 := rfl

@[simp] theorem cov2FromCoordinates_zero :
    cov2FromCoordinates (fun (_ : M) (_ : FourSpace) => (0 : Mat4)) = 0 := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear]

@[simp] theorem deltaStar_zero (g : RawCov2 M) : deltaStar g 0 = 0 := by
  have hz : deltaStarInChart g 0 = fun _ _ => (0 : Mat4) := by
    funext c x i j
    simp [deltaStarInChart, nablaCovectorInChart, coordDeriv]
  rw [deltaStar, hz, cov2FromCoordinates_zero]

@[simp] theorem cov2VariationDerivative_zero (t : ℝ) :
    cov2VariationDerivative (fun _ => (0 : RawCov2 M)) t = 0 := by
  simp only [cov2VariationDerivative, cov2InChart_zero, deriv_const]
  exact cov2FromCoordinates_zero

@[simp] theorem deltaStarMetricVariation_zero (z u : RawCov2 M) :
    deltaStarMetricVariation z u 0 = 0 := by
  simp [deltaStarMetricVariation]

theorem dangerous_term_zero_of_cancellation (rho : CircleAction M)
    (ghat z u : RawCov2 M)
    (hc : covectorPiPerp rho (bianchi ghat (z - ghat)) = 0) :
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0 := by
  rw [hc, deltaStarMetricVariation_zero]

theorem covectorHaarIntegrable_of_invariant (rho : CircleAction M) (eta : RawCovector M)
    (heta : IsInvariantCovector rho eta) : CovectorHaarIntegrable rho eta := by
  intro c x _ i
  unfold IsInvariantCovector at heta
  simp only [heta]
  exact MeasureTheory.integrable_const _

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

theorem cov2ContDiff_sub (u v : RawCov2 M) (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v) :
    Cov2ContDiff 1 (u - v) := by
  intro c
  change ContDiffOn ℝ 1 (fun x => cov2InChart u c x - cov2InChart v c x)
    (chartAt FourSpace c).target
  exact (hu c).sub (hv c)

theorem invariantCov2_sub (rho : CircleAction M) (u v : RawCov2 M)
    (hu : IsInvariantCov2 rho u) (hv : IsInvariantCov2 rho v) :
    IsInvariantCov2 rho (u - v) := by
  intro t
  have hsub : actionPullbackCov2 rho t (u - v) =
      actionPullbackCov2 rho t u - actionPullbackCov2 rho t v := by
    ext p w z
    rfl
  rw [hsub, hu t, hv t]

end K24.Global.BianchiInvariance
end
end ProductStandalonePart10

/- Checked source module: ClosureBasics. -/
section ProductStandalonePart11
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
namespace K24.Global.BianchiInvariance
open LieNaturality BianchiNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem bianchi_eval_canonical (g u : RawCov2 M) (hDu : Cov2ContDiff 1 u)
    (p : M) (v : TangentSpace I4 p) :
    bianchi g u p v = bianchiForm g u p (chartAt FourSpace p p)
      (mfderiv I4 I4 (chartAt FourSpace p) p v) := by
  rw [bianchiForm_eq g u p _ (cov2_differentiableAt u hDu p _ (mem_chart_target FourSpace p))]
  rfl

theorem cov2ContDiff_one_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff 1 g := by
  intro c
  exact (cov2ContDiff_of_metricAdmissible C b g hg c).of_le
    (by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) b.order_ge_two))

end K24.Global.BianchiInvariance
end
end ProductStandalonePart11

/- Checked source module: ActionInvariance. -/
section ProductStandalonePart12
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.BianchiInvariance
open LieNaturality BianchiNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem bianchi_invariant (rho : CircleAction M) (g u : RawCov2 M)
    (hg : IsMetric g) (hDg : Cov2ContDiff 1 g) (hDu : Cov2ContDiff 1 u)
    (hig : IsInvariantCov2 rho g) (hiu : IsInvariantCov2 rho u) :
    IsInvariantCovector rho (bianchi g u) := by
  intro t
  ext p v
  change bianchi g u (rho.act t p) (mfderiv I4 I4 (rho.act t) p v) = bianchi g u p v
  have hx := mem_chart_target FourSpace p
  have hp := mem_chart_source FourSpace p
  have hq := mem_chart_source FourSpace (rho.act t p)
  have hd : rho.act t ((chartAt FourSpace p).symm (chartAt FourSpace p p)) ∈
      (chartAt FourSpace (rho.act t p)).source := by
    rw [(chartAt FourSpace p).left_inv hp]
    exact hq
  have hy : actionInCharts rho t p (rho.act t p) (chartAt FourSpace p p) ∈
      (chartAt FourSpace (rho.act t p)).target := (chartAt FourSpace (rho.act t p)).map_source hd
  have hG := actionInCharts_form_eventually rho t g p (rho.act t p) (chartAt FourSpace p p) hx hd
  have hU := actionInCharts_form_eventually rho t u p (rho.act t p) (chartAt FourSpace p p) hx hd
  rw [hig t] at hG
  rw [hiu t] at hU
  have hB := bianchiForm_natural_local g u hg hDg hDu p (rho.act t p)
    (actionInCharts rho t p (rho.act t p)) (chartAt FourSpace p p) hx hy
    ((actionInCharts_smooth rho t p (rho.act t p) (chartAt FourSpace p p) hx hd).of_le (by decide))
    hG hU (mfderiv I4 I4 (chartAt FourSpace p) p v)
  rw [actionInCharts_comp_chart_differential rho t p (rho.act t p) p hp hq v] at hB
  simp only [bianchi_eval_canonical g u hDu]
  simpa only [actionInCharts, Function.comp_apply, (chartAt FourSpace p).left_inv hp] using hB.symm

theorem invariant_center_cancellation (rho : CircleAction M) (ghat z : RawCov2 M)
    (hghat : IsMetric ghat) (hDghat : Cov2ContDiff 1 ghat) (hDz : Cov2ContDiff 1 z)
    (highat : IsInvariantCov2 rho ghat) (hiz : IsInvariantCov2 rho z) :
    covectorPiPerp rho (bianchi ghat (z - ghat)) = 0 := by
  exact covectorPiPerp_of_invariant rho _
    (bianchi_invariant rho ghat (z - ghat) hghat hDghat
      (cov2ContDiff_sub z ghat hDz hDghat) highat
      (invariantCov2_sub rho z ghat hiz highat))

theorem invariant_center_cancellation_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (rho : CircleAction M) (ghat z : RawCov2 M)
    (hghat : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (highat : IsInvariantCov2 rho ghat) (hiz : IsInvariantCov2 rho z) :
    covectorPiPerp rho (bianchi ghat (z - ghat)) = 0 :=
  invariant_center_cancellation rho ghat z hghat.metric
    (cov2ContDiff_one_of_metricAdmissible C b ghat hghat)
    (cov2ContDiff_one_of_metricAdmissible C b z hz) highat hiz

end K24.Global.BianchiInvariance
end
end ProductStandalonePart12

/- Checked source module: BianchiLocalRegularity. -/
section ProductStandalonePart13
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
namespace K24.Global.GeometricRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem coordDeriv_contDiffAt (k : ℕ) (f : FourSpace → ℝ) (x : FourSpace)
    (hf : ContDiffAt ℝ (k + 1) f x) (a : Fin 4) :
    ContDiffAt ℝ k (coordDeriv f a) x := by
  exact (hf.fderiv_right (m := k) (by simp)).clm_apply contDiffAt_const

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
end ProductStandalonePart13

/- Checked source module: HaarContinuity. -/
section ProductStandalonePart14
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
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
end ProductStandalonePart14

/- Checked source module: CanonicalBianchi. -/
section ProductStandalonePart15
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
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

end K24.Global.GeometricRegularity
end
end ProductStandalonePart15

/- Checked source module: ExactAlgebra. -/
section ProductStandalonePart16

/-!
Exact operator algebra for the literal frozen K24 definitions.
No target file with admitted theorems is imported.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
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

#print axioms K24.Global.Research20261024.deltaStar_sub
#print axioms K24.Global.Research20261024.gaugedLinearization_difference
#print axioms K24.Global.Research20261024.dangerous_term_zero_of_cancellation
#print axioms K24.Global.Research20261024.lieTensor_sub
#print axioms K24.Global.Research20261024.bianchi_sub
#print axioms K24.Global.Research20261024.actualMetricVector_difference
#print axioms K24.Global.Research20261024.projected_center_vector_difference
#print axioms K24.Global.Research20261024.projected_actual_vector_difference
#print axioms K24.Global.Research20261024.dangerous_term_zero_of_invariant

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

#print axioms K24.Global.tensor_defect_identity_of_regular_bianchi
#print axioms K24.Global.projected_actual_vector_defect_identity
end
end ProductStandalonePart16

/- Checked source module: AffineAlgebra. -/
section ProductStandalonePart17
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter MeasureTheory
namespace K24.Global.BianchiAffine
open Research20261024
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

@[simp] theorem cov2InChart_smul (t : ℝ) (u : RawCov2 M) (c : M) (x : FourSpace) :
    cov2InChart (t • u) c x = t • cov2InChart u c x := rfl

@[simp] theorem covectorInChart_smul (t : ℝ) (eta : RawCovector M) (c : M) (x : FourSpace) :
    covectorInChart (t • eta) c x = t • covectorInChart eta c x := rfl

theorem coordDeriv_smul (t : ℝ) (f : FourSpace → ℝ) (i : Fin 4) (x : FourSpace) :
    coordDeriv (fun y => t * f y) i x = t * coordDeriv f i x := by
  change fderiv ℝ (t • f) x (basisVector i) = _
  rw [fderiv_const_smul_field]
  rfl

theorem coordDeriv_const_smul (t : ℝ) (f : FourSpace → ℝ) (i : Fin 4) (x : FourSpace) :
    coordDeriv (t • f) i x = t * coordDeriv f i x :=
  coordDeriv_smul t f i x

theorem covectorFromCoordinates_smul (t : ℝ) (a : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (t • a) = t • covectorFromCoordinates a := by
  ext p v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    Finset.mul_sum, mul_assoc]

theorem metricTraceInChart_smul (g u : RawCov2 M) (t : ℝ) (c : M) :
    metricTraceInChart g (t • u) c = t • metricTraceInChart g u c := by
  funext x
  simp only [metricTraceInChart, cov2InChart_smul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem nablaTensorInChart_smul (g u : RawCov2 M) (t : ℝ) (c : M) (x : FourSpace)
    (a b d : Fin 4) :
    nablaTensorInChart g (t • u) c x a b d = t * nablaTensorInChart g u c x a b d := by
  simp only [nablaTensorInChart, cov2InChart_smul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, coordDeriv_smul, coordDeriv_const_smul]
  simp only [mul_sub, Finset.mul_sum]
  have hs (A B : Fin 4 → ℝ) : (∑ p, A p * (t * B p)) = ∑ p, t * (A p * B p) := by
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hs, hs]

theorem bianchi_smul (g u : RawCov2 M) (t : ℝ) : bianchi g (t • u) = t • bianchi g u := by
  have hlocal : bianchiInChart g (t • u) = t • bianchiInChart g u := by
    funext c x j
    simp only [bianchiInChart, nablaTensorInChart_smul, metricTraceInChart_smul,
      Pi.smul_apply, smul_eq_mul, coordDeriv_smul, coordDeriv_const_smul]
    rw [show (∑ a : Fin 4, ∑ b : Fin 4, inverseMetricInChart g c x a b *
        (t * nablaTensorInChart g u c x a b j)) =
        t * (∑ a : Fin 4, ∑ b : Fin 4, inverseMetricInChart g c x a b *
          nablaTensorInChart g u c x a b j) by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring]
    ring
  unfold bianchi
  rw [hlocal, covectorFromCoordinates_smul]

theorem cov2ContDiff_smul (t : ℝ) (u : RawCov2 M) (hu : Cov2ContDiff 1 u) :
    Cov2ContDiff 1 (t • u) := by
  intro c
  change ContDiffOn ℝ 1 (fun x => t • cov2InChart u c x) _
  exact (hu c).const_smul t

theorem cov2ContDiff_add (u v : RawCov2 M) (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v) :
    Cov2ContDiff 1 (u + v) := by
  intro c
  change ContDiffOn ℝ 1 (fun x => cov2InChart u c x + cov2InChart v c x) _
  exact (hu c).add (hv c)

theorem bianchi_add_smul (g u v : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v) (t : ℝ) :
    bianchi g (u + t • v) = bianchi g u + t • bianchi g v := by
  have htv := cov2ContDiff_smul t v hv
  have h := Research20261024.bianchi_sub g (u + t • v) (t • v)
    (cov2ContDiff_add u (t • v) hu htv) htv
    (fun c x hx => IdentityProof.differentiableAt_inverseMetric g hg c x hx
      (BianchiInvariance.cov2_differentiableAt g hDg c x hx))
  rw [show u + t • v - t • v = u by abel, bianchi_smul] at h
  exact sub_eq_iff_eq_add.mp h.symm

end K24.Global.BianchiAffine
end
end ProductStandalonePart17

/- Checked source module: ProjectionAlgebra. -/
section ProductStandalonePart18
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise
open MeasureTheory
namespace K24.Global.BianchiAffine
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem actionPullbackCovector_smul (rho : CircleAction M) (s : Circle) (t : ℝ)
    (eta : RawCovector M) :
    actionPullbackCovector rho s (t • eta) = t • actionPullbackCovector rho s eta := by
  ext p v
  rfl

theorem covectorPi0_smul (rho : CircleAction M) (t : ℝ) (eta : RawCovector M) :
    covectorPi0 rho (t • eta) = t • covectorPi0 rho eta := by
  unfold covectorPi0
  rw [← covectorFromCoordinates_smul]
  congr 1
  funext c x i
  simp only [actionPullbackCovector_smul, covectorInChart_smul, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul t _

theorem covectorPiPerp_smul (rho : CircleAction M) (t : ℝ) (eta : RawCovector M) :
    covectorPiPerp rho (t • eta) = t • covectorPiPerp rho eta := by
  unfold covectorPiPerp
  rw [covectorPi0_smul, smul_sub]

theorem covectorHaarIntegrable_smul (rho : CircleAction M) (t : ℝ) (eta : RawCovector M)
    (h : CovectorHaarIntegrable rho eta) : CovectorHaarIntegrable rho (t • eta) := by
  intro c x hx i
  simp only [actionPullbackCovector_smul, covectorInChart_smul, Pi.smul_apply, smul_eq_mul]
  exact (h c x hx i).const_mul t

theorem covectorPiPerp_add (rho : CircleAction M) (eta theta : RawCovector M)
    (heta : CovectorHaarIntegrable rho eta) (htheta : CovectorHaarIntegrable rho theta) :
    covectorPiPerp rho (eta + theta) = covectorPiPerp rho eta + covectorPiPerp rho theta := by
  have h := Research20261024.covectorPiPerp_sub rho eta ((-1 : ℝ) • theta) heta
    (covectorHaarIntegrable_smul rho (-1) theta htheta)
  rw [covectorPiPerp_smul] at h
  have hs (a b : RawCovector M) : a - (-1 : ℝ) • b = a + b := by
    ext p v
    change a p v - (-1) * b p v = a p v + b p v
    ring
  simpa only [hs] using h

theorem covectorPiPerp_add_smul (rho : CircleAction M) (eta theta : RawCovector M)
    (heta : CovectorHaarIntegrable rho eta) (htheta : CovectorHaarIntegrable rho theta) (t : ℝ) :
    covectorPiPerp rho (eta + t • theta) =
      covectorPiPerp rho eta + t • covectorPiPerp rho theta := by
  rw [covectorPiPerp_add rho eta (t • theta) heta (covectorHaarIntegrable_smul rho t theta htheta),
    covectorPiPerp_smul]

end K24.Global.BianchiAffine
end
end ProductStandalonePart18

/- Checked source module: CurveIdentity. -/
section ProductStandalonePart19
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff NNReal Matrix.Norms.Elementwise
namespace K24.Global.BianchiAffine
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem projected_curve_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (rho : CircleAction M) (ghat z u : RawCov2 M)
    (hghat : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (highat : IsInvariantCov2 rho ghat) (hiz : IsInvariantCov2 rho z)
    (hu : C.Cov2Holder 2 b.exponent.value u) (t : ℝ) :
    covectorPiPerp rho (bianchi ghat ((z + t • u) - ghat)) =
      t • covectorPiPerp rho (bianchi ghat u) := by
  have hDghat := BianchiInvariance.cov2ContDiff_one_of_metricAdmissible C b ghat hghat
  have hDz := BianchiInvariance.cov2ContDiff_one_of_metricAdmissible C b z hz
  have hDu : Cov2ContDiff 1 u := fun c =>
    (cov2ContDiff_of_cov2Holder C 2 b.exponent.value u hu c).of_le (by decide)
  have hDa := BianchiInvariance.cov2ContDiff_sub z ghat hDz hDghat
  have hHa := GeometricRegularity.bianchi_haarIntegrable rho ghat (z - ghat)
    hghat.metric hDghat hDa
  have hHu := GeometricRegularity.bianchi_haarIntegrable rho ghat u hghat.metric hDghat hDu
  rw [show (z + t • u) - ghat = (z - ghat) + t • u by abel,
    bianchi_add_smul ghat (z - ghat) u hghat.metric hDghat hDa hDu t,
    covectorPiPerp_add_smul rho (bianchi ghat (z - ghat)) (bianchi ghat u) hHa hHu t,
    BianchiInvariance.invariant_center_cancellation_of_metricAdmissible C b rho ghat z
      hghat hz highat hiz, zero_add]

end K24.Global.BianchiAffine
end
end ProductStandalonePart19

/- Checked source module: JetCalculus. -/
section ProductStandalonePart20

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
end ProductStandalonePart20

/- Checked source module: ChristoffelVariation. -/
section ProductStandalonePart21

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
end ProductStandalonePart21

/- Checked source module: Solution. -/
section ProductStandalonePart22

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
end
end ProductStandalonePart22

/- Checked source module: ActualVariation. -/
section ProductStandalonePart23

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.AffineMetricVariation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem reconstructed_parameter_smooth
    (A : ℝ → M → FourSpace → Mat4) (t₀ : ℝ)
    (hA : ∀ (p : M) (i j : Fin 4),
      ContDiffAt ℝ ∞ (fun t => A t p (chartAt FourSpace p p) i j) t₀)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t => cov2InChart (cov2FromCoordinates (A t)) c x i j) t₀ := by
  let p := (chartAt FourSpace c).symm x
  let v := mfderiv I4 I4 (chartAt FourSpace p) p
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
  let w := mfderiv I4 I4 (chartAt FourSpace p) p
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))
  change ContDiffAt ℝ ∞
    (fun t => matrixToBilinear (A t p (chartAt FourSpace p p)) v w) t₀
  simp only [CoverRegularityProof.matrixToBilinear_apply]
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_const.mul (hA p a b)).mul contDiffAt_const

variable [IsManifold I4 ∞ M]

theorem actual_einsteinResidual_parameter_smooth
    (z u : RawCov2 M) (hz : IsMetric z)
    (hDz : Cov2ContDiff 2 z) (hDu : Cov2ContDiff 2 u)
    (lam : ℝ) (c : M) (x : FourSpace) (i j : Fin 4) :
    ContDiffAt ℝ ∞
      (fun t : ℝ => cov2InChart (einsteinResidual lam (z + t • u)) c x i j) 0 := by
  have hR : ContDiffAt ℝ ∞
      (fun t : ℝ => cov2InChart (ricci (z + t • u)) c x i j) 0 := by
    apply reconstructed_parameter_smooth
    intro p a b
    have hp := (chartAt FourSpace p).map_source (mem_chart_source FourSpace p)
    exact affine_ricci_smooth z u p (chartAt FourSpace p p)
      ((hDz p _ hp).contDiffAt ((chartAt FourSpace p).open_target.mem_nhds hp))
      ((hDu p _ hp).contDiffAt ((chartAt FourSpace p).open_target.mem_nhds hp))
      (isUnit_iff_ne_zero.mp
        (PrincipalSymbolRegularity.cov2InChart_isUnit_det z hz p _ hp)) a b
  have hA : ContDiffAt ℝ ∞ (fun t : ℝ => cov2InChart (z + t • u) c x i j) 0 := by
    simp only [cov2InChart_affine, affineCoefficients]
    fun_prop
  exact hR.sub (contDiffAt_const.mul hA)

theorem deltaStarInChart_parameter_smooth (z u : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace)
    (hDz : ContDiffAt ℝ 2 (cov2InChart z c) x)
    (hDu : ContDiffAt ℝ 2 (cov2InChart u c) x)
    (hne : (cov2InChart z c x).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun t : ℝ => deltaStarInChart (z + t • u) eta c x i j) 0 := by
  have hN (a b : Fin 4) : ContDiffAt ℝ ∞
      (fun t : ℝ => nablaCovectorInChart (z + t • u) eta c x a b) 0 := by
    apply contDiffAt_const.sub
    apply ContDiffAt.sum
    intro p _
    exact (affine_christoffel_smooth z u c x hDz hDu hne p a b).mul contDiffAt_const
  exact contDiffAt_const.mul ((hN i j).add (hN j i))

theorem actual_deltaStar_parameter_smooth
    (z u : RawCov2 M) (eta : RawCovector M) (hz : IsMetric z)
    (hDz : Cov2ContDiff 2 z) (hDu : Cov2ContDiff 2 u)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    ContDiffAt ℝ ∞
      (fun t : ℝ => cov2InChart (deltaStar (z + t • u) eta) c x i j) 0 := by
  apply reconstructed_parameter_smooth
  intro p a b
  have hp := (chartAt FourSpace p).map_source (mem_chart_source FourSpace p)
  exact deltaStarInChart_parameter_smooth z u eta p (chartAt FourSpace p p)
    ((hDz p _ hp).contDiffAt ((chartAt FourSpace p).open_target.mem_nhds hp))
    ((hDu p _ hp).contDiffAt ((chartAt FourSpace p).open_target.mem_nhds hp))
    (isUnit_iff_ne_zero.mp
      (PrincipalSymbolRegularity.cov2InChart_isUnit_det z hz p _ hp)) a b

end K24.Global.AffineMetricVariation
end
end ProductStandalonePart23

/- Checked source module: ProductRuleCalculus. -/
section ProductStandalonePart24

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.AffineMetricVariation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem cov2FromCoordinates_add (A B : M → FourSpace → Mat4) :
    cov2FromCoordinates (fun c x => A c x + B c x) =
      cov2FromCoordinates A + cov2FromCoordinates B := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem cov2FromCoordinates_smul (A : M → FourSpace → Mat4) (t : ℝ) :
    cov2FromCoordinates (fun c x => t • A c x) = t • cov2FromCoordinates A := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem coordDeriv_const_mul_unconditional (f : FourSpace → ℝ) (t : ℝ)
    (x : FourSpace) (i : Fin 4) :
    coordDeriv (fun y => t * f y) i x = t * coordDeriv f i x := by
  change fderiv ℝ (t • f) x (basisVector i) = _
  rw [fderiv_const_smul_field]
  rfl

theorem deltaStar_smul (g : RawCov2 M) (eta : RawCovector M) (t : ℝ) :
    deltaStar g (t • eta) = t • deltaStar g eta := by
  have hcoeff : deltaStarInChart g (t • eta) =
      fun c x => t • deltaStarInChart g eta c x := by
    funext c x i j
    change deltaStarInChart g (t • eta) c x i j = t * deltaStarInChart g eta c x i j
    have hC (y : FourSpace) (a : Fin 4) : covectorInChart (t • eta) c y a =
        t * covectorInChart eta c y a := rfl
    have hN (a b : Fin 4) : nablaCovectorInChart g (t • eta) c x a b =
        t * nablaCovectorInChart g eta c x a b := by
      have hs : (∑ p, christoffelInChart g c x p a b * (t * covectorInChart eta c x p)) =
          t * ∑ p, christoffelInChart g c x p a b * covectorInChart eta c x p := by
        simp only [Finset.mul_sum, mul_left_comm]
      simp only [nablaCovectorInChart, hC, coordDeriv_const_mul_unconditional, hs]
      ring
    simp only [deltaStarInChart, hN]
    ring
  rw [deltaStar, hcoeff]
  exact cov2FromCoordinates_smul (deltaStarInChart g eta) t

theorem affine_tensor_zero (z u : RawCov2 M) : z + (0 : ℝ) • u = z := by
  ext p v w
  simp

theorem cov2VariationDerivative_add (F G : ℝ → RawCov2 M) (t : ℝ)
    (hF : ∀ c x i j, DifferentiableAt ℝ (fun s => cov2InChart (F s) c x i j) t)
    (hG : ∀ c x i j, DifferentiableAt ℝ (fun s => cov2InChart (G s) c x i j) t) :
    cov2VariationDerivative (fun s => F s + G s) t =
      cov2VariationDerivative F t + cov2VariationDerivative G t := by
  unfold cov2VariationDerivative
  rw [← cov2FromCoordinates_add]
  congr 1
  funext c x i j
  change deriv (fun s => cov2InChart (F s) c x i j + cov2InChart (G s) c x i j) t = _
  exact deriv_add (hF c x i j) (hG c x i j)

variable [IsManifold I4 ∞ M]

theorem cov2FromCoordinates_recover (g : RawCov2 M) :
    cov2FromCoordinates (cov2InChart g) = g := by
  funext p
  exact cov2_chart_recovery g p p (mem_chart_source FourSpace p)

theorem cov2VariationDerivative_mul_parameter (F : ℝ → RawCov2 M)
    (hF : ∀ c x i j, DifferentiableAt ℝ (fun s => cov2InChart (F s) c x i j) 0) :
    cov2VariationDerivative (fun s => s • F s) 0 = F 0 := by
  unfold cov2VariationDerivative
  rw [← cov2FromCoordinates_recover (F 0)]
  congr 1
  funext c x i j
  change deriv (fun s : ℝ => s * cov2InChart (F s) c x i j) 0 = _
  have hd := ((hasDerivAt_id (0 : ℝ)).mul (hF c x i j).hasDerivAt).deriv
  change deriv (fun s : ℝ => s * cov2InChart (F s) c x i j) 0 = _ at hd
  simpa only [id_eq, one_mul, zero_mul, add_zero] using hd

/-- This reduction supplies its own actual coefficient differentiability proofs.
    The remaining hypothesis is the separately proved projected Bianchi curve. -/
theorem partialGauge_product_rule_of_projected_curve
    (rho : CircleAction M) (lam : ℝ) (ghat z u : RawCov2 M)
    (hz : IsMetric z) (hDz : Cov2ContDiff 2 z) (hDu : Cov2ContDiff 2 u)
    (hcurve : ∀ t : ℝ,
      covectorPiPerp rho (bianchi ghat ((z + t • u) - ghat)) =
        t • covectorPiPerp rho (bianchi ghat u)) :
    partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u := by
  let eta := covectorPiPerp rho (bianchi ghat u)
  let F : ℝ → RawCov2 M := fun t => einsteinResidual lam (z + t • u)
  let G : ℝ → RawCov2 M := fun t => deltaStar (z + t • u) eta
  have hF (c : M) (x : FourSpace) (i j : Fin 4) :
      DifferentiableAt ℝ (fun t => cov2InChart (F t) c x i j) 0 :=
    (actual_einsteinResidual_parameter_smooth z u hz hDz hDu lam c x i j).differentiableAt
      (by simp)
  have hG (c : M) (x : FourSpace) (i j : Fin 4) :
      DifferentiableAt ℝ (fun t => cov2InChart (G t) c x i j) 0 :=
    (actual_deltaStar_parameter_smooth z u eta hz hDz hDu c x i j).differentiableAt (by simp)
  have hscaled (c : M) (x : FourSpace) (i j : Fin 4) :
      DifferentiableAt ℝ (fun t => cov2InChart (t • G t) c x i j) 0 :=
    differentiableAt_id.mul (hG c x i j)
  have hnonlinear : (fun t : ℝ => partialGauge rho lam ghat (z + t • u)) =
      fun t => F t + t • G t := by
    funext t
    rw [partialGauge, hcurve, deltaStar_smul]
  have hcancel : covectorPiPerp rho (bianchi ghat (z - ghat)) = 0 := by
    have h := hcurve 0
    rw [affine_tensor_zero] at h
    simpa only [zero_smul] using h
  have hmetric := BianchiInvariance.dangerous_term_zero_of_cancellation rho ghat z u hcancel
  rw [partialGaugeVariation, hnonlinear,
    cov2VariationDerivative_add F (fun t => t • G t) 0 hF hscaled,
    cov2VariationDerivative_mul_parameter G hG]
  change einsteinLinearization lam z u + deltaStar (z + (0 : ℝ) • u) eta = _
  rw [affine_tensor_zero, partialGaugeProductRule, hmetric]
  ext p v w
  change einsteinLinearization lam z u p v w + deltaStar z eta p v w =
    (einsteinLinearization lam z u p v w + 0) + deltaStar z eta p v w
  ring

end K24.Global.AffineMetricVariation
end
end ProductStandalonePart24

/- Checked source module: ProductRule. -/
section ProductStandalonePart25

set_option autoImplicit false
open scoped Manifold ContDiff NNReal Matrix.Norms.Elementwise

namespace K24.Global.AffineMetricVariation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem product_rule_of_metricAdmissible
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (rho : CircleAction M) (lam : ℝ) (ghat z u : RawCov2 M)
    (hghat : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (highat : IsInvariantCov2 rho ghat) (hiz : IsInvariantCov2 rho z)
    (hu : C.Cov2Holder 2 b.exponent.value u) :
    partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u := by
  have hDz : Cov2ContDiff 2 z := fun c =>
    (cov2ContDiff_of_metricAdmissible C b z hz c).of_le
      (by exact_mod_cast b.order_ge_two)
  have hDu := cov2ContDiff_of_cov2Holder C 2 b.exponent.value u hu
  exact partialGauge_product_rule_of_projected_curve rho lam ghat z u hz.metric hDz hDu
    (BianchiAffine.projected_curve_of_metricAdmissible C b rho ghat z u hghat hz highat hiz hu)

end K24.Global.AffineMetricVariation

universe u
open K24.Global

theorem product_rule_solution :
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
          ∀ u ∈ tensorHolderSpace C 2 metricBounds.exponent.value,
            partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u := by
  intro coverBounds metricBounds H hH M _ _ _ _ _ C hC rho hrho
    lam ghat z g hghat hz hg highat hiz u hu
  exact AffineMetricVariation.product_rule_of_metricAdmissible C metricBounds rho lam
    ghat z u hghat hz highat hiz hu.2
end ProductStandalonePart25

section ProductRuleExport

open scoped Manifold ContDiff NNReal
open K24.Global
universe u

theorem solution :
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
        ∀ u ∈ tensorHolderSpace C 2 metricBounds.exponent.value,
          partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u := product_rule_solution

end ProductRuleExport

set_option pp.coercions false
