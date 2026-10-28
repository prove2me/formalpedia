-- Prove2me | solution 1 for K24.Global.ricci_chart_and_action_naturality
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:59:03.302891+00:00
-- url     : https://prove2.me/submissions/772dbc9e-b8cc-4c59-8152-084ba1daa681

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false

/- Source module: Infrastructure. -/
section RicciStandalonePart0
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
end RicciStandalonePart0

/- Source module: Connection. -/
section RicciStandalonePart1
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
end RicciStandalonePart1

/- Source module: Contraction. -/
section RicciStandalonePart2
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
end RicciStandalonePart2

/- Source module: Regularity. -/
section RicciStandalonePart3

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
end RicciStandalonePart3

/- Source module: ActionDefinitions. -/
section RicciStandalonePart4
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace K24.Global.BianchiInvariance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
def actionInCharts (rho : CircleAction M) (t : Circle) (c d : M) : FourSpace → FourSpace :=
  (chartAt FourSpace d) ∘ (rho.act t) ∘ (chartAt FourSpace c).symm
end K24.Global.BianchiInvariance
end
end RicciStandalonePart4

/- Source module: ActionCoordinates. -/
section RicciStandalonePart5
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
end RicciStandalonePart5

/- Source module: MetricTransform. -/
section RicciStandalonePart6
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
end
end RicciStandalonePart6

/- Source module: CurvatureTransport. -/
section RicciStandalonePart7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology
open Filter

namespace K24.Global.RicciNaturality
open LieNaturality BianchiNaturality

def curvatureOf (A : FourSpace → Gamma) (x v w t : FourSpace) : FourSpace :=
  fderiv ℝ A x v w t - fderiv ℝ A x w v t +
    A x v (A x w t) - A x w (A x v t)

theorem fderiv_gamma_apply (A : FourSpace → Gamma)
    (U V : FourSpace → FourSpace) (x r : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hU : DifferentiableAt ℝ U x)
    (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => A y (U y) (V y)) x r =
      fderiv ℝ A x r (U x) (V x) + A x (fderiv ℝ U x r) (V x) +
        A x (U x) (fderiv ℝ V x r) := by
  rw [fderiv_clm_apply (hA.clm_apply hU) hV, fderiv_clm_apply hA hU]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

theorem fderiv_gamma_const (A : FourSpace → Gamma) (x r v w : FourSpace)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => A y v w) x r = fderiv ℝ A x r v w := by
  rw [fderiv_gamma_apply A (fun _ => v) (fun _ => w) x r hA
    (differentiableAt_const _) (differentiableAt_const _)]
  simp

theorem connection_relation_derivative
    (A B : FourSpace → Gamma) (F : FourSpace → FourSpace) (x r v w : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B (F x))
    (hF : ContDiffAt ℝ 3 F x)
    (he : ∀ᶠ y in 𝓝 x, ∀ v w : FourSpace,
      fderiv ℝ F y (A y v w) =
        B (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) +
          fderiv ℝ (fderiv ℝ F) y v w) :
    fderiv ℝ (fderiv ℝ F) x r (A x v w) +
        fderiv ℝ F x (fderiv ℝ A x r v w) =
      fderiv ℝ B (F x) (fderiv ℝ F x r) (fderiv ℝ F x v) (fderiv ℝ F x w) +
        B (F x) (fderiv ℝ (fderiv ℝ F) x r v) (fderiv ℝ F x w) +
        B (F x) (fderiv ℝ F x v) (fderiv ℝ (fderiv ℝ F) x r w) +
        fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x r v w := by
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF2 := hF.fderiv_right (m := 2) (by norm_num)
  have hDF := hDF2.differentiableAt (by norm_num)
  have hDDF := (hDF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : (fun y => fderiv ℝ F y (A y v w)) =ᶠ[𝓝 x]
      (fun y => B (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) +
        fderiv ℝ (fderiv ℝ F) y v w) := he.mono (fun y hy => hy v w)
  have h := congrArg (fun D : FourSpace →L[ℝ] FourSpace => D r) (hev.fderiv_eq (𝕜 := ℝ))
  have hBF : DifferentiableAt ℝ (fun y => B (F y)) x :=
    DifferentiableAt.comp (g := B) (f := F) x hB hF1
  have hAvw := (hA.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)
  have hBFF : DifferentiableAt ℝ
      (fun y => B (F y) (fderiv ℝ F y v) (fderiv ℝ F y w)) x := ((hB.comp x hF1).clm_apply
    (hDF.clm_apply (differentiableAt_const v))).clm_apply
    (hDF.clm_apply (differentiableAt_const w))
  have hHvw := (hDDF.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)
  rw [fderiv_clm_apply hDF hAvw, fderiv_fun_add hBFF hHvw] at h
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at h
  rw [fderiv_gamma_const A x r v w hA,
    fderiv_gamma_apply (fun y => B (F y)) (fun y => fderiv ℝ F y v)
      (fun y => fderiv ℝ F y w) x r hBF
      (hDF.clm_apply (differentiableAt_const v))
      (hDF.clm_apply (differentiableAt_const w)),
    fderiv_fun_comp (g := B) (f := F) x hB hF1,
    fderiv_derivative_apply F x r v hDF,
    fderiv_derivative_apply F x r w hDF,
    fderiv_gamma_const (fderiv ℝ (fderiv ℝ F)) x r v w hDDF] at h
  simpa only [ContinuousLinearMap.comp_apply, add_comm] using h

theorem curvatureOf_natural
    (A B : FourSpace → Gamma) (F : FourSpace → FourSpace) (x v w t : FourSpace)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B (F x))
    (hF : ContDiffAt ℝ 3 F x)
    (he : ∀ᶠ y in 𝓝 x, ∀ v w : FourSpace,
      fderiv ℝ F y (A y v w) =
        B (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) +
          fderiv ℝ (fderiv ℝ F) y v w) :
    fderiv ℝ F x (curvatureOf A x v w t) =
      curvatureOf B (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x t) := by
  have hv := connection_relation_derivative A B F x v w t hA hB hF he
  have hw := connection_relation_derivative A B F x w v t hA hB hF he
  have hs := (hF.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).isSymmSndFDerivAt (by norm_num)
  have hthird := (hF.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num)
  have hpoint := he.self_of_nhds
  unfold curvatureOf
  simp only [map_sub, map_add]
  rw [hpoint v (A x w t), hpoint w (A x v t), hpoint w t, hpoint v t]
  simp only [map_add]
  rw [hs.eq w v] at hw
  have hthird' := congrArg (fun D : FourSpace →L[ℝ] FourSpace => D t) (hthird.eq w v)
  rw [hthird'] at hw
  linear_combination (norm := abel) hv - hw

end K24.Global.RicciNaturality
end
end RicciStandalonePart7

/- Source module: MetricTransport. -/
section RicciStandalonePart8

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise
open Filter

namespace K24.Global.RicciNaturality
open LieNaturality BianchiNaturality BianchiInvariance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metric_differentiableAt (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    DifferentiableAt ℝ (cov2InChart g c) x :=
  ((hg c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt
    (by norm_num)

theorem gammaForm_differentiableAt (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    DifferentiableAt ℝ (gammaForm g c) x := by
  have hC := PrincipalSymbolRegularity.christoffel_differentiableAt g hg c x hx
    ((hDg c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx))
  have he : gammaForm g c = fun y => ∑ i : Fin 4, ∑ j : Fin 4, ∑ p : Fin 4,
      christoffelInChart g c y p i j •
        (coordProj i).smulRight ((coordProj j).smulRight (basisVector p)) := by
    ext y v w k
    simp [gammaForm, ContinuousLinearMap.smulRight_apply, Finset.sum_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [he]
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun i y => ∑ j : Fin 4, ∑ p : Fin 4, christoffelInChart g c y p i j •
      (coordProj i).smulRight ((coordProj j).smulRight (basisVector p)))
  intro i _
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun j y => ∑ p : Fin 4, christoffelInChart g c y p i j •
      (coordProj i).smulRight ((coordProj j).smulRight (basisVector p)))
  intro j _
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun p y => christoffelInChart g c y p i j •
      (coordProj i).smulRight ((coordProj j).smulRight (basisVector p)))
  intro p _
  let T : ℝ →L[ℝ] Gamma := ContinuousLinearMap.toSpanSingleton ℝ
    ((coordProj i).smulRight ((coordProj j).smulRight (basisVector p)))
  exact DifferentiableAt.comp (g := T) (f := fun y => christoffelInChart g c y p i j) x
    (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := ℝ) (F := Gamma) T) (hC p i j)

theorem gammaForm_natural_metrics (g h : RawCov2 M) (hg : IsMetric g) (hh : IsMetric h)
    (hDg : Cov2ContDiff 2 g) (hDh : Cov2ContDiff 2 h)
    (c d : M) (F : FourSpace → FourSpace) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hy : F x ∈ (chartAt FourSpace d).target) (hF : ContDiffAt ℝ 2 F x)
    (hJ : Function.Bijective (fderiv ℝ F x))
    (hG : formInChart g c =ᶠ[𝓝 x]
      (fun y => bilinearPullback (formInChart h d (F y)) (fderiv ℝ F y)))
    (v w : FourSpace) :
    fderiv ℝ F x (gammaForm g c x v w) =
      gammaForm h d (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) +
      fderiv ℝ (fderiv ℝ F) x v w :=
  DeltaStarNaturality.gammaForm_natural_between g h hg hh c d F x hx hy
    (metric_differentiableAt g hDg c x hx) (metric_differentiableAt h hDh d (F x) hy)
    hF hJ hG v w

theorem curvatureOf_chart_natural (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (v w t : FourSpace) :
    fderiv ℝ (chartTransition c d) x (curvatureOf (gammaForm g c) x v w t) =
      curvatureOf (gammaForm g d) (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v)
        (fderiv ℝ (chartTransition c d) x w)
        (fderiv ℝ (chartTransition c d) x t) := by
  have hDg1 : Cov2ContDiff 1 g := fun c => (hDg c).of_le (by norm_num)
  apply curvatureOf_natural _ _ _ x v w t
    (gammaForm_differentiableAt g hg hDg c x hx)
    (gammaForm_differentiableAt g hg hDg d _ ((chartAt FourSpace d).map_source hd))
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
  filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
  exact fun v w => gammaForm_natural g hg hDg1 c d y hy.1 hy.2 v w

end K24.Global.RicciNaturality
end
end RicciStandalonePart8

/- Source module: CurvatureTrace. -/
section RicciStandalonePart9

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise
open Filter Matrix

namespace K24.Global.RicciNaturality
open LieNaturality BianchiNaturality BianchiContraction

def curvatureLinear (A : FourSpace → Gamma) (x v t : FourSpace) :
    FourSpace →L[ℝ] FourSpace :=
  (ContinuousLinearMap.apply ℝ FourSpace t).comp
      ((ContinuousLinearMap.apply ℝ (FourSpace →L[ℝ] FourSpace) v).comp (fderiv ℝ A x)) -
    (ContinuousLinearMap.apply ℝ FourSpace t).comp (fderiv ℝ A x v) +
    (ContinuousLinearMap.apply ℝ FourSpace (A x v t)).comp (A x) -
    (A x v).comp ((ContinuousLinearMap.apply ℝ FourSpace t).comp (A x))

theorem curvatureLinear_apply (A : FourSpace → Gamma) (x v t w : FourSpace) :
    curvatureLinear A x v t w = curvatureOf A x w v t := rfl

def ricciOf (A : FourSpace → Gamma) (x v t : FourSpace) : ℝ :=
  (matrixOf (curvatureLinear A x v t)).trace

theorem ricciOf_eq_sum (A : FourSpace → Gamma) (x v t : FourSpace) :
    ricciOf A x v t = ∑ k : Fin 4, curvatureOf A x (basisVector k) v t k := rfl

theorem matrixOf_comp (J K : FourSpace →L[ℝ] FourSpace) :
    matrixOf (J.comp K) = matrixOf J * matrixOf K := by
  ext i j
  change J (K (basisVector j)) i = ∑ k, J (basisVector k) i * K (basisVector j) k
  have he := congrArg (fun v : FourSpace => J v i) (sum_basisVector (K (basisVector j)))
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm] using he.symm

theorem matrixOf_id : matrixOf (ContinuousLinearMap.id ℝ FourSpace) = 1 := by
  ext i j
  simp [matrixOf, basisVector, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem matrixOf_isUnit_of_bijective (J : FourSpace →L[ℝ] FourSpace)
    (hJ : Function.Bijective J) : IsUnit (matrixOf J).det := by
  let e := ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hJ.1) (LinearMap.range_eq_top.mpr hJ.2)
  have he : J.comp (e.symm : FourSpace →L[ℝ] FourSpace) =
      ContinuousLinearMap.id ℝ FourSpace := by
    apply ContinuousLinearMap.ext
    intro v
    exact e.apply_symm_apply v
  have hm := congrArg matrixOf he
  rw [matrixOf_comp, matrixOf_id] at hm
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_one] at hd
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

theorem ricciOf_natural (A B : FourSpace → Gamma) (x y : FourSpace)
    (J : FourSpace →L[ℝ] FourSpace) (hJ : Function.Bijective J)
    (hR : ∀ v w t : FourSpace, J (curvatureOf A x v w t) =
      curvatureOf B y (J v) (J w) (J t)) (v t : FourSpace) :
    ricciOf A x v t = ricciOf B y (J v) (J t) := by
  have he : J.comp (curvatureLinear A x v t) =
      (curvatureLinear B y (J v) (J t)).comp J := by
    apply ContinuousLinearMap.ext
    intro w
    exact hR w v t
  have hm := congrArg matrixOf he
  rw [matrixOf_comp, matrixOf_comp] at hm
  have hinv := matrixOf_isUnit_of_bijective J hJ
  have hh : matrixOf (curvatureLinear B y (J v) (J t)) =
      matrixOf J * matrixOf (curvatureLinear A x v t) * (matrixOf J)⁻¹ := by
    rw [hm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv, Matrix.mul_one]
  unfold ricciOf
  rw [hh, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mul]

theorem curvatureOf_expand (A : FourSpace → Gamma) (x v w t : FourSpace) :
    curvatureOf A x v w t =
      ∑ i : Fin 4, ∑ j : Fin 4, (w i * t j) •
        curvatureOf A x v (basisVector i) (basisVector j) := by
  conv_lhs => rw [← sum_basisVector w, ← sum_basisVector t]
  simp only [curvatureOf, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    smul_sub, smul_add, Finset.smul_sum, smul_smul]
  refine congrArg₂ (fun a b : FourSpace => a - b)
    (congrArg₂ (fun a b : FourSpace => a + b)
      (congrArg₂ (fun a b : FourSpace => a - b) ?_ ?_) ?_) ?_
  all_goals rw [Finset.sum_comm]; simp only [mul_comm]

theorem ricciOf_expand (A : FourSpace → Gamma) (x v t : FourSpace) :
    ricciOf A x v t = ∑ i : Fin 4, ∑ j : Fin 4,
      v i * (ricciOf A x (basisVector i) (basisVector j) * t j) := by
  have he (k : Fin 4) := curvatureOf_expand A x (basisVector k) v t
  simp only [ricciOf_eq_sum, he, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end K24.Global.RicciNaturality
end
end RicciStandalonePart9

/- Source module: ActionMetric. -/
section RicciStandalonePart10

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise
open Filter

namespace K24.Global.RicciNaturality
open LieNaturality BianchiNaturality BianchiInvariance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem actionPullback_isMetric (rho : CircleAction M) (t : Circle)
    (q : RawCov2 M) (hq : IsMetric q) : IsMetric (actionPullbackCov2 rho t q) := by
  constructor
  · intro p v w
    exact hq.1 _ _ _
  · intro p v hv
    apply hq.2
    intro hzero
    apply hv
    apply (action_derivative_bijective rho t p).1
    exact hzero.trans (map_zero _).symm

theorem actionPullback_cov2ContDiff_two (rho : CircleAction M) (t : Circle)
    (q : RawCov2 M) (hq : Cov2ContDiff 2 q) :
    Cov2ContDiff 2 (actionPullbackCov2 rho t q) := by
  intro c x hx
  let d := rho.act t ((chartAt FourSpace c).symm x)
  have hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source :=
    mem_chart_source FourSpace d
  let F := actionInCharts rho t c d
  have hy : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hF : ContDiffAt ℝ ∞ F x := actionInCharts_smooth rho t c d x hx hd
  have hA : ContDiffAt ℝ 2 (cov2InChart q d) (F x) :=
    (hq d).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hy)
  have hpull := CoverRegularityProof.contDiffAt_pullbackCoefficients (cov2InChart q d) F x 2 hA hF
  have he : cov2InChart (actionPullbackCov2 rho t q) c =ᶠ[𝓝 x]
      CoverRegularityProof.pullbackCoefficients (cov2InChart q d) F := by
    filter_upwards [actionInCharts_form_eventually rho t q c d x hx hd] with y hy
    ext i j
    have h := congrArg (fun Q : Form => Q (basisVector i) (basisVector j)) hy
    simpa only [formInChart, Function.comp_apply, matrixToForm_basis,
      bilinearPullback_apply, matrixToForm_apply, CoverRegularityProof.pullbackCoefficients] using h
  exact (hpull.congr_of_eventuallyEq he).contDiffWithinAt

theorem curvatureOf_action_natural (rho : CircleAction M) (t : Circle)
    (q : RawCov2 M) (hq : IsMetric q) (hDq : Cov2ContDiff 2 q)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source)
    (v w s : FourSpace) :
    fderiv ℝ (actionInCharts rho t c d) x
        (curvatureOf (gammaForm (actionPullbackCov2 rho t q) c) x v w s) =
      curvatureOf (gammaForm q d) (actionInCharts rho t c d x)
        (fderiv ℝ (actionInCharts rho t c d) x v)
        (fderiv ℝ (actionInCharts rho t c d) x w)
        (fderiv ℝ (actionInCharts rho t c d) x s) := by
  have hqp := actionPullback_isMetric rho t q hq
  have hDqp := actionPullback_cov2ContDiff_two rho t q hDq
  apply curvatureOf_natural _ _ _ x v w s
    (gammaForm_differentiableAt _ hqp hDqp c x hx)
    (gammaForm_differentiableAt q hq hDq d _ ((chartAt FourSpace d).map_source hd))
    ((actionInCharts_smooth rho t c d x hx hd).of_le (by decide))
  filter_upwards [actionInCharts_overlap_eventually rho t c d x hx hd] with y hy
  intro v w
  exact gammaForm_natural_metrics _ q hqp hq hDqp hDq c d
    (actionInCharts rho t c d) y hy.1 ((chartAt FourSpace d).map_source hy.2)
    ((actionInCharts_smooth rho t c d y hy.1 hy.2).of_le (by decide))
    (actionInCharts_derivative_bijective rho t c d y hy.1 hy.2)
    (actionInCharts_form_eventually rho t q c d y hy.1 hy.2) v w

end K24.Global.RicciNaturality
end
end RicciStandalonePart10

/- Source module: RicciCoordinates. -/
section RicciStandalonePart11

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise
open Filter

namespace K24.Global.RicciNaturality
open LieNaturality BianchiNaturality BianchiContraction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem gammaForm_component (g : RawCov2 M) (c : M) (x : FourSpace)
    (i j k : Fin 4) :
    gammaForm g c x (basisVector i) (basisVector j) k = christoffelInChart g c x k i j := by
  rw [gammaForm_basis]
  simp [WithLp.ofLp_sum, WithLp.ofLp_smul, basisVector, Pi.single_apply, eq_comm]

theorem gammaForm_derivative_component (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j k l : Fin 4) :
    fderiv ℝ (gammaForm g c) x (basisVector i) (basisVector j) (basisVector k) l =
      coordDeriv (fun y => christoffelInChart g c y l j k) i x := by
  have hG := gammaForm_differentiableAt g hg hDg c x hx
  have hGjk := (hG.clm_apply (differentiableAt_const (basisVector j))).clm_apply
    (differentiableAt_const (basisVector k))
  have hcomp := (coordProj l).hasFDerivAt.comp x hGjk.hasFDerivAt
  have he : (fun y => coordProj l (gammaForm g c y (basisVector j) (basisVector k))) =
      (fun y => christoffelInChart g c y l j k) := by
    funext y
    exact gammaForm_component g c y j k l
  change HasFDerivAt (fun y => coordProj l (gammaForm g c y (basisVector j) (basisVector k))) _ x at hcomp
  rw [he] at hcomp
  unfold coordDeriv
  rw [hcomp.fderiv]
  change _ = (fderiv ℝ (fun y => gammaForm g c y (basisVector j) (basisVector k)) x
    (basisVector i)) l
  rw [fderiv_gamma_const _ x _ _ _ hG]

theorem curvatureOf_component (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j k l : Fin 4) :
    curvatureOf (gammaForm g c) x (basisVector i) (basisVector j) (basisVector k) l =
      curvatureInChart g c x l i j k := by
  simp only [curvatureOf, WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply,
    gammaForm_derivative_component g hg hDg c x hx]
  rw [gammaForm_basis g c x j k, gammaForm_basis g c x i k]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gammaForm_component, curvatureInChart]
  rw [Finset.sum_sub_distrib]
  simp only [mul_comm]
  ring

theorem ricciOf_basis (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ricciOf (gammaForm g c) x (basisVector i) (basisVector j) = ricciInChart g c x i j := by
  simp only [ricciOf_eq_sum, ricciInChart, curvatureOf_component g hg hDg c x hx]

theorem ricciOf_form (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (v w : FourSpace) :
    ricciOf (gammaForm g c) x v w = matrixToBilinear (ricciInChart g c x) v w := by
  rw [ricciOf_expand, BianchiContraction.matrixToBilinear_apply]
  simp only [ricciOf_basis g hg hDg c x hx]

theorem ricciInChart_natural (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    matrixToBilinear (ricciInChart g c x) =
      bilinearPullback (matrixToBilinear (ricciInChart g d (chartTransition c d x)))
        (fderiv ℝ (chartTransition c d) x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [bilinearPullback_apply, ← ricciOf_form g hg hDg c x hx,
    ← ricciOf_form g hg hDg d (chartTransition c d x) ((chartAt FourSpace d).map_source hd)]
  exact ricciOf_natural _ _ _ _ _ (chartTransition_derivative_bijective c d x hx hd)
    (curvatureOf_chart_natural g hg hDg c d x hx hd) v w

theorem ricci_chart_recovery (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (ricci g) c x i j = ricciInChart g c x i j := by
  let p := (chartAt FourSpace c).symm x
  have hp : p ∈ (chartAt FourSpace p).source := mem_chart_source FourSpace p
  have hn := congrArg (fun A : Form => A (basisVector i) (basisVector j))
    (ricciInChart_natural g hg hDg c p x hx hp)
  rw [matrixToForm_basis] at hn
  rw [bilinearPullback_apply, chartTransition_derivative c p x hx hp] at hn
  exact hn.symm

end K24.Global.RicciNaturality
end
end RicciStandalonePart11

/- Source module: RicciAction. -/
section RicciStandalonePart12

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise
open Filter

namespace K24.Global.RicciNaturality
open LieNaturality BianchiNaturality BianchiInvariance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem ricciInChart_action_natural (rho : CircleAction M) (t : Circle)
    (q : RawCov2 M) (hq : IsMetric q) (hDq : Cov2ContDiff 2 q)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : rho.act t ((chartAt FourSpace c).symm x) ∈ (chartAt FourSpace d).source) :
    matrixToBilinear (ricciInChart (actionPullbackCov2 rho t q) c x) =
      bilinearPullback (matrixToBilinear (ricciInChart q d (actionInCharts rho t c d x)))
        (fderiv ℝ (actionInCharts rho t c d) x) := by
  have hqp := actionPullback_isMetric rho t q hq
  have hDqp := actionPullback_cov2ContDiff_two rho t q hDq
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [bilinearPullback_apply, ← ricciOf_form _ hqp hDqp c x hx,
    ← ricciOf_form q hq hDq d (actionInCharts rho t c d x) ((chartAt FourSpace d).map_source hd)]
  exact ricciOf_natural _ _ _ _ _ (actionInCharts_derivative_bijective rho t c d x hx hd)
    (curvatureOf_action_natural rho t q hq hDq c d x hx hd) v w

theorem ricci_action_natural (rho : CircleAction M) (t : Circle)
    (q : RawCov2 M) (hq : IsMetric q) (hDq : Cov2ContDiff 2 q) :
    ricci (actionPullbackCov2 rho t q) = actionPullbackCov2 rho t (ricci q) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  let d := rho.act t p
  let x := chartAt FourSpace p p
  have hx : x ∈ (chartAt FourSpace p).target := mem_chart_target FourSpace p
  have hp : p ∈ (chartAt FourSpace p).source := mem_chart_source FourSpace p
  have hd : rho.act t ((chartAt FourSpace p).symm x) ∈ (chartAt FourSpace d).source := by
    dsimp [x]
    rw [(chartAt FourSpace p).left_inv hp]
    exact mem_chart_source FourSpace d
  have hF : actionInCharts rho t p d x = chartAt FourSpace d d := by
    dsimp [actionInCharts, x]
    rw [(chartAt FourSpace p).left_inv hp]
  have he := congrArg (fun A : Form => A
      (mfderiv I4 I4 (chartAt FourSpace p) p v)
      (mfderiv I4 I4 (chartAt FourSpace p) p w))
    (ricciInChart_action_natural rho t q hq hDq p d x hx hd)
  rw [bilinearPullback_apply,
    actionInCharts_comp_chart_differential rho t p d p hp (mem_chart_source FourSpace d),
    actionInCharts_comp_chart_differential rho t p d p hp (mem_chart_source FourSpace d), hF] at he
  exact he

end K24.Global.RicciNaturality
end
end RicciStandalonePart12

/- Source module: ModularSolution. -/
section RicciStandalonePart13

set_option autoImplicit false
open scoped Manifold ContDiff

universe u
open K24.Global

theorem solution :
    (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
      ∀ (q : RawCov2 M), IsMetric q → Cov2ContDiff 2 q →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ i j : Fin 4, cov2InChart (ricci q) c x i j = ricciInChart q c x i j) ∧
    (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
      ∀ (q : RawCov2 M), IsMetric q → Cov2ContDiff 2 q →
        ∀ (rho : CircleAction M) (t : Circle),
          ricci (actionPullbackCov2 rho t q) = actionPullbackCov2 rho t (ricci q)) := by
  constructor
  · intro M _ _ _ q hq hDq c x hx i j
    exact RicciNaturality.ricci_chart_recovery q hq hDq c x hx i j
  · intro M _ _ _ q hq hDq rho t
    exact RicciNaturality.ricci_action_natural rho t q hq hDq
end RicciStandalonePart13
