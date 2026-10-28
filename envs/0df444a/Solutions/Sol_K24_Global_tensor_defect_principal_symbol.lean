-- Prove2me | solution 1 for K24.Global.tensor_defect_principal_symbol
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:27:48.17895+00:00
-- url     : https://prove2.me/submissions/37792c2e-463d-4341-8594-2028a002529a

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false

/- Checked source module: Infrastructure. -/
section K24StandalonePart0
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
end K24StandalonePart0

/- Checked source module: Connection. -/
section K24StandalonePart1
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
end K24StandalonePart1

/- Checked source module: Covariant. -/
section K24StandalonePart2
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
end K24StandalonePart2

/- Checked source module: TraceBasics. -/
section K24StandalonePart3
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
end K24StandalonePart3

/- Checked source module: Contraction. -/
section K24StandalonePart4
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
end K24StandalonePart4

/- Checked source module: BianchiRecovery. -/
section K24StandalonePart5
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
end K24StandalonePart5

/- Checked source module: Regularity. -/
section K24StandalonePart6

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
end K24StandalonePart6

/- Checked source module: Solution. -/
section K24StandalonePart7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.PrincipalSymbolProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem matrixToBilinear_basis (a : Mat4) (i j : Fin 4) :
    matrixToBilinear a (basisVector i) (basisVector j) = a i j := by
  simp [matrixToBilinear, coordProj, basisVector]

theorem cov2FromChartAt_coefficients (c : M) (A : M → Mat4)
    (y : FourSpace) (hy : y ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (fun p => cov2FromChartAt c p (A p)) c y i j =
      A ((chartAt FourSpace c).symm y) i j := by
  have hd (v : FourSpace) :
      mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm y)
        (mfderiv I4 I4 (chartAt FourSpace c).symm y v) = v :=
    congrArg (fun D => D v)
      ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hy)
  unfold cov2InChart cov2FromChartAt
  change matrixToBilinear (A ((chartAt FourSpace c).symm y))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm y)
      (mfderiv I4 I4 (chartAt FourSpace c).symm y (basisVector i)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm y)
      (mfderiv I4 I4 (chartAt FourSpace c).symm y (basisVector j))) = _
  rw [hd, hd]
  exact matrixToBilinear_basis _ i j

def jetLinear (x : FourSpace) (xi : Fin 4 → ℝ) (y : FourSpace) : ℝ :=
  coefficientsToCovector xi (y - x)

def jetQuadratic (x : FourSpace) (xi : Fin 4 → ℝ) (y : FourSpace) : ℝ :=
  (1 / 2 : ℝ) * jetLinear x xi y ^ 2

theorem jetLinear_sum (x y : FourSpace) (xi : Fin 4 → ℝ) :
    jetLinear x xi y = ∑ a : Fin 4, xi a * (y a - x a) := by
  simp [jetLinear, coefficientsToCovector, coordProj]

theorem coefficientsToCovector_basis (xi : Fin 4 → ℝ) (i : Fin 4) :
    coefficientsToCovector xi (basisVector i) = xi i := by
  simp [coefficientsToCovector, coordProj, basisVector]

theorem jetLinear_hasFDerivAt (x y : FourSpace) (xi : Fin 4 → ℝ) :
    HasFDerivAt (jetLinear x xi) (coefficientsToCovector xi) y := by
  change HasFDerivAt ((coefficientsToCovector xi) ∘ (fun z : FourSpace => z - x)) _ y
  convert (coefficientsToCovector xi).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub_const x) using 1 <;> rfl

theorem jetQuadratic_hasFDerivAt (x y : FourSpace) (xi : Fin 4 → ℝ) :
    HasFDerivAt (jetQuadratic x xi)
      (jetLinear x xi y • coefficientsToCovector xi) y := by
  have h := ((jetLinear_hasFDerivAt x y xi).pow 2).const_mul (1 / 2 : ℝ)
  convert h using 1 <;> first | rfl | simp [jetQuadratic, smul_smul]

theorem jetQuadratic_contDiff (x : FourSpace) (xi : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (jetQuadratic x xi) := by
  unfold jetQuadratic jetLinear
  fun_prop

theorem quadraticJetTensor_coefficients (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (quadraticJetTensor c x xi a) c y i j =
      jetQuadratic x xi y * a i j := by
  unfold quadraticJetTensor
  rw [cov2FromChartAt_coefficients c _ y hy]
  rw [(chartAt FourSpace c).right_inv hy]
  rw [jetQuadratic, jetLinear_sum]

theorem quadraticJetTensor_coefficients_eventually (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    (fun w => cov2InChart (quadraticJetTensor c x xi a) c w i j) =ᶠ[𝓝 y]
      (fun w => jetQuadratic x xi w * a i j) := by
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hy] with w hw
  exact quadraticJetTensor_coefficients c x w xi a hw i j

theorem quadraticJetTensor_coordDeriv (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target) (k i j : Fin 4) :
    coordDeriv (fun w => cov2InChart (quadraticJetTensor c x xi a) c w i j) k y =
      jetLinear x xi y * xi k * a i j := by
  unfold coordDeriv
  rw [(quadraticJetTensor_coefficients_eventually c x y xi a hy i j).fderiv_eq]
  rw [((jetQuadratic_hasFDerivAt x y xi).mul_const (a i j)).fderiv]
  simp [coefficientsToCovector_basis, mul_comm, mul_left_comm, mul_assoc]

theorem quadraticJetTensor_second_coordDeriv (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target) (l k i j : Fin 4) :
    coordDeriv (fun w =>
      coordDeriv (fun v => cov2InChart (quadraticJetTensor c x xi a) c v i j) k w) l y =
      xi l * xi k * a i j := by
  have he : (fun w =>
      coordDeriv (fun v => cov2InChart (quadraticJetTensor c x xi a) c v i j) k w) =ᶠ[𝓝 y]
      (fun w => jetLinear x xi w * xi k * a i j) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hy] with w hw
    exact quadraticJetTensor_coordDeriv c x w xi a hw k i j
  change fderiv ℝ _ y (basisVector l) = _
  rw [he.fderiv_eq]
  rw [(((jetLinear_hasFDerivAt x y xi).mul_const (xi k)).mul_const (a i j)).fderiv]
  simp [coefficientsToCovector_basis, mul_comm, mul_left_comm, mul_assoc]

theorem quadraticJetTensor_zero (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    cov2InChart (quadraticJetTensor c x xi a) c x i j = 0 := by
  rw [quadraticJetTensor_coefficients c x x xi a hx]
  simp [jetQuadratic, jetLinear]

theorem quadraticJetTensor_first_zero (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target) (k i j : Fin 4) :
    coordDeriv (fun w => cov2InChart (quadraticJetTensor c x xi a) c w i j) k x = 0 := by
  rw [quadraticJetTensor_coordDeriv c x x xi a hx]
  simp [jetLinear]


theorem coordDeriv_mul (f h : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (k : Fin 4) :
    coordDeriv (fun y => f y * h y) k x =
      coordDeriv f k x * h x + f x * coordDeriv h k x := by
  unfold coordDeriv
  rw [fderiv_fun_mul hf hh]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem coordDeriv_sum (f : Fin 4 → FourSpace → ℝ) (x : FourSpace)
    (hf : ∀ a, DifferentiableAt ℝ (f a) x) (k : Fin 4) :
    coordDeriv (fun y => ∑ a, f a y) k x = ∑ a, coordDeriv (f a) k x := by
  unfold coordDeriv
  rw [fderiv_fun_sum (fun a _ => hf a)]
  simp only [_root_.sum_apply]

theorem quadraticJetTensor_contDiffAt (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => cov2InChart (quadraticJetTensor c x xi a) c w i j) y := by
  exact ((jetQuadratic_contDiff x xi).contDiffAt.mul contDiffAt_const).congr_of_eventuallyEq
    (quadraticJetTensor_coefficients_eventually c x y xi a hy i j)

theorem quadraticJetTensor_coordDeriv_differentiableAt (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target) (k i j : Fin 4) :
    DifferentiableAt ℝ
      (coordDeriv (fun w => cov2InChart (quadraticJetTensor c x xi a) c w i j) k) y := by
  have h : ContDiffAt ℝ 2
      (fun w => cov2InChart (quadraticJetTensor c x xi a) c w i j) y :=
    (quadraticJetTensor_contDiffAt c x y xi a hy i j).of_le (by decide)
  exact ((h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num)

theorem quadraticJetTensor_nabla_zero (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target) (k i j : Fin 4) :
    nablaTensorInChart g (quadraticJetTensor c x xi a) c x k i j = 0 := by
  simp only [nablaTensorInChart, quadraticJetTensor_zero c x xi a hx,
    quadraticJetTensor_first_zero c x xi a hx, mul_zero, Finset.sum_const_zero, sub_zero]

theorem quadraticJetTensor_nabla_differentiableAt (g : RawCov2 M) (c : M)
    (x y : FourSpace) (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target)
    (hG : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart g c w p k i) y)
    (k i j : Fin 4) :
    DifferentiableAt ℝ
      (fun w => nablaTensorInChart g (quadraticJetTensor c x xi a) c w k i j) y := by
  have hU (i j : Fin 4) :=
    (quadraticJetTensor_contDiffAt c x y xi a hy i j).differentiableAt (by simp)
  exact ((quadraticJetTensor_coordDeriv_differentiableAt c x y xi a hy k i j).sub
    (DifferentiableAt.fun_sum (fun p _ => (hG p k i).mul (hU p j)))).sub
    (DifferentiableAt.fun_sum (fun p _ => (hG p k j).mul (hU i p)))

theorem quadraticJetTensor_nabla_first (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hG : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart g c w p k i) x)
    (l k i j : Fin 4) :
    coordDeriv
      (fun w => nablaTensorInChart g (quadraticJetTensor c x xi a) c w k i j) l x =
      xi l * xi k * a i j := by
  have hU (i j : Fin 4) :=
    (quadraticJetTensor_contDiffAt c x x xi a hx i j).differentiableAt (by simp)
  have hprod (p k i b d : Fin 4) := (hG p k i).mul (hU b d)
  have hsum₁ := DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => hprod p k i p j)
  have hsum₂ := DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => hprod p k j i p)
  change fderiv ℝ (fun w =>
    coordDeriv (fun v => cov2InChart (quadraticJetTensor c x xi a) c v i j) k w -
      (∑ p, christoffelInChart g c w p k i * cov2InChart (quadraticJetTensor c x xi a) c w p j) -
      (∑ p, christoffelInChart g c w p k j * cov2InChart (quadraticJetTensor c x xi a) c w i p))
    x (basisVector l) = _
  erw [fderiv_fun_sub ((quadraticJetTensor_coordDeriv_differentiableAt c x x xi a hx k i j).sub hsum₁) hsum₂,
    fderiv_fun_sub (quadraticJetTensor_coordDeriv_differentiableAt c x x xi a hx k i j) hsum₁]
  change coordDeriv _ l x - coordDeriv _ l x - coordDeriv _ l x = _
  rw [quadraticJetTensor_second_coordDeriv c x x xi a hx,
    coordDeriv_sum _ x (fun p => hprod p k i p j),
    coordDeriv_sum _ x (fun p => hprod p k j i p)]
  have hz (p k b d e : Fin 4) : coordDeriv (fun w =>
      christoffelInChart g c w p k b * cov2InChart (quadraticJetTensor c x xi a) c w d e) l x = 0 := by
    rw [coordDeriv_mul _ _ x (hG p k b) (hU d e),
      quadraticJetTensor_zero c x xi a hx,
      quadraticJetTensor_first_zero c x xi a hx]
    ring
  have hz₁ : (∑ p, coordDeriv (fun w => christoffelInChart g c w p k i *
      cov2InChart (quadraticJetTensor c x xi a) c w p j) l x) = 0 :=
    Finset.sum_eq_zero (fun p _ => hz p k i p j)
  have hz₂ : (∑ p, coordDeriv (fun w => christoffelInChart g c w p k j *
      cov2InChart (quadraticJetTensor c x xi a) c w i p) l x) = 0 :=
    Finset.sum_eq_zero (fun p _ => hz p k j i p)
  erw [hz₁, hz₂]
  ring


theorem coordDeriv_jetLinear (x y : FourSpace) (xi : Fin 4 → ℝ) (j : Fin 4) :
    coordDeriv (jetLinear x xi) j y = xi j := by
  unfold coordDeriv
  rw [(jetLinear_hasFDerivAt x y xi).fderiv, coefficientsToCovector_basis]

theorem coordDeriv_jetQuadratic (x y : FourSpace) (xi : Fin 4 → ℝ) (j : Fin 4) :
    coordDeriv (jetQuadratic x xi) j y = jetLinear x xi y * xi j := by
  unfold coordDeriv
  rw [(jetQuadratic_hasFDerivAt x y xi).fderiv]
  simp [coefficientsToCovector_basis]

theorem coordDeriv_mul_jetQuadratic (x y : FourSpace) (xi : Fin 4 → ℝ)
    (T : FourSpace → ℝ) (hT : DifferentiableAt ℝ T y) (j : Fin 4) :
    coordDeriv (fun w => jetQuadratic x xi w * T w) j y =
      jetLinear x xi y * xi j * T y + jetQuadratic x xi y * coordDeriv T j y := by
  rw [coordDeriv_mul _ _ y (jetQuadratic_hasFDerivAt x y xi).differentiableAt hT,
    coordDeriv_jetQuadratic]

theorem second_coordDeriv_mul_jetQuadratic (x : FourSpace) (xi : Fin 4 → ℝ)
    (T : FourSpace → ℝ) (hT : ContDiffAt ℝ 2 T x) (k j : Fin 4) :
    coordDeriv (coordDeriv (fun w => jetQuadratic x xi w * T w) j) k x =
      xi k * xi j * T x := by
  have hT1 := hT.differentiableAt (by norm_num)
  have hDT : DifferentiableAt ℝ (coordDeriv T j) x :=
    ((hT.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hq := (jetQuadratic_hasFDerivAt x x xi).differentiableAt
  have hl := (jetLinear_hasFDerivAt x x xi).differentiableAt
  have he : coordDeriv (fun w => jetQuadratic x xi w * T w) j =ᶠ[𝓝 x]
      (fun y => jetLinear x xi y * xi j * T y + jetQuadratic x xi y * coordDeriv T j y) := by
    filter_upwards [hT.eventually (by norm_num)] with y hy
    exact coordDeriv_mul_jetQuadratic x y xi T (hy.differentiableAt (by norm_num)) j
  change fderiv ℝ _ x (basisVector k) = _
  rw [he.fderiv_eq]
  erw [fderiv_fun_add ((hl.mul_const (xi j)).mul hT1) (hq.mul hDT)]
  change coordDeriv _ k x + coordDeriv _ k x = _
  erw [coordDeriv_mul _ _ x (hl.mul_const (xi j)) hT1,
    coordDeriv_mul _ _ x hq hDT,
    coordDeriv_jetQuadratic]
  have hlin : coordDeriv (fun y => jetLinear x xi y * xi j) k x = xi k * xi j := by
    unfold coordDeriv
    rw [((jetLinear_hasFDerivAt x x xi).mul_const (xi j)).fderiv]
    simp [coefficientsToCovector_basis, mul_comm]
  rw [hlin]
  simp [jetLinear, jetQuadratic]

theorem coordDeriv_eventuallyEq {f h : FourSpace → ℝ} {x : FourSpace}
    (he : f =ᶠ[𝓝 x] h) (j : Fin 4) :
    coordDeriv f j =ᶠ[𝓝 x] coordDeriv h j := by
  exact (he.fderiv (𝕜 := ℝ)).mono (fun y hy => congrArg (fun D : FourSpace →L[ℝ] ℝ => D (basisVector j)) hy)

theorem quadraticJetTensor_trace_eventually (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target) :
    metricTraceInChart g (quadraticJetTensor c x xi a) c =ᶠ[𝓝 x]
      (fun y => jetQuadratic x xi y * ∑ i, ∑ j, inverseMetricInChart g c y i j * a i j) := by
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
  simp only [metricTraceInChart, quadraticJetTensor_coefficients c x y xi a hy,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticJetTensor_trace_second (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hA : ContDiffAt ℝ 2 (inverseMetricInChart g c) x) (k j : Fin 4) :
    coordDeriv (coordDeriv (metricTraceInChart g (quadraticJetTensor c x xi a) c) j) k x =
      xi k * xi j * ∑ r, ∑ s, inverseMetricInChart g c x r s * a r s := by
  have hT : ContDiffAt ℝ 2 (fun y => ∑ i, ∑ j, inverseMetricInChart g c y i j * a i j) x := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j).mul contDiffAt_const
  have he := coordDeriv_eventuallyEq (quadraticJetTensor_trace_eventually g c x xi a hx) j
  change fderiv ℝ _ x (basisVector k) = _
  rw [he.fderiv_eq]
  exact second_coordDeriv_mul_jetQuadratic x xi _ hT k j


theorem quadraticJetTensor_trace_contDiffAt (g : RawCov2 M) (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target)
    (hA : ContDiffAt ℝ 2 (inverseMetricInChart g c) y) :
    ContDiffAt ℝ 2 (metricTraceInChart g (quadraticJetTensor c x xi a) c) y := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j).mul
    ((quadraticJetTensor_contDiffAt c x y xi a hy i j).of_le (by decide))

theorem quadraticJetTensor_trace_first_zero (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hA : DifferentiableAt ℝ (inverseMetricInChart g c) x) (j : Fin 4) :
    coordDeriv (metricTraceInChart g (quadraticJetTensor c x xi a) c) j x = 0 := by
  have hT : DifferentiableAt ℝ (fun y => ∑ i, ∑ j, inverseMetricInChart g c y i j * a i j) x := by
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.fun_sum
    intro j _
    exact (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j).mul_const _
  change fderiv ℝ _ x (basisVector j) = _
  rw [(quadraticJetTensor_trace_eventually g c x xi a hx).fderiv_eq]
  change coordDeriv _ j x = _
  rw [coordDeriv_mul_jetQuadratic x x xi _ hT]
  simp [jetQuadratic, jetLinear]

theorem quadraticJetTensor_bianchi_zero (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hA : DifferentiableAt ℝ (inverseMetricInChart g c) x) (j : Fin 4) :
    bianchiInChart g (quadraticJetTensor c x xi a) c x j = 0 := by
  simp only [bianchiInChart, quadraticJetTensor_nabla_zero g c x xi a hx,
    quadraticJetTensor_trace_first_zero g c x xi a hx hA,
    mul_zero, Finset.sum_const_zero, neg_zero, add_zero]

theorem quadraticJetTensor_bianchi_differentiableAt (g : RawCov2 M) (c : M)
    (x y : FourSpace) (xi : Fin 4 → ℝ) (a : Mat4)
    (hy : y ∈ (chartAt FourSpace c).target)
    (hA : ContDiffAt ℝ 2 (inverseMetricInChart g c) y)
    (hG : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart g c w p k i) y)
    (j : Fin 4) :
    DifferentiableAt ℝ (fun w => bianchiInChart g (quadraticJetTensor c x xi a) c w j) y := by
  have hA1 := hA.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ
      (fun w => ∑ i, ∑ b, inverseMetricInChart g c w i b *
        nablaTensorInChart g (quadraticJetTensor c x xi a) c w i b j) y := by
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.fun_sum
    intro b _
    exact (differentiableAt_pi.mp (differentiableAt_pi.mp hA1 i) b).mul
      (quadraticJetTensor_nabla_differentiableAt g c x y xi a hy hG i b j)
  have hT := quadraticJetTensor_trace_contDiffAt g c x y xi a hy hA
  exact hD.neg.add ((((hT.fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiffAt_const).differentiableAt (by norm_num)).const_mul _)

theorem quadraticJetTensor_bianchi_first (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hA : ContDiffAt ℝ 2 (inverseMetricInChart g c) x)
    (hG : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart g c w p k i) x)
    (k j : Fin 4) :
    coordDeriv (fun w => bianchiInChart g (quadraticJetTensor c x xi a) c w j) k x =
      xi k * (-(∑ r, ∑ s, inverseMetricInChart g c x r s * xi r * a s j) +
        (1 / 2 : ℝ) * ∑ r, ∑ s, inverseMetricInChart g c x r s * xi j * a r s) := by
  have hA1 := hA.differentiableAt (by norm_num)
  have hAe (r s : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hA1 r) s
  have hN (r s : Fin 4) := quadraticJetTensor_nabla_differentiableAt g c x x xi a hx hG r s j
  have hP (r s : Fin 4) := (hAe r s).mul (hN r s)
  have hS (r : Fin 4) := DifferentiableAt.fun_sum (u := Finset.univ) (fun s _ => hP r s)
  have hD := DifferentiableAt.fun_sum (u := Finset.univ) (fun r _ => hS r)
  have hT := quadraticJetTensor_trace_contDiffAt g c x x xi a hx hA
  have hDT : DifferentiableAt ℝ
      (coordDeriv (metricTraceInChart g (quadraticJetTensor c x xi a) c) j) x :=
    ((hT.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  change fderiv ℝ (fun w =>
    -(∑ r, ∑ s, inverseMetricInChart g c w r s *
      nablaTensorInChart g (quadraticJetTensor c x xi a) c w r s j) +
      (1 / 2 : ℝ) * coordDeriv (metricTraceInChart g (quadraticJetTensor c x xi a) c) j w)
    x (basisVector k) = _
  erw [fderiv_fun_add hD.neg (hDT.const_mul _), fderiv_neg,
    (hDT.hasFDerivAt.const_mul (1 / 2 : ℝ)).fderiv]
  change -coordDeriv _ k x + (1 / 2 : ℝ) * coordDeriv _ k x = _
  rw [coordDeriv_sum _ x hS, quadraticJetTensor_trace_second g c x xi a hx hA]
  have hrow (r : Fin 4) :
      coordDeriv (fun w => ∑ s, inverseMetricInChart g c w r s *
        nablaTensorInChart g (quadraticJetTensor c x xi a) c w r s j) k x =
        ∑ s, inverseMetricInChart g c x r s * (xi k * xi r * a s j) := by
    erw [coordDeriv_sum _ x (hP r)]
    apply Finset.sum_congr rfl
    intro s _
    erw [coordDeriv_mul _ _ x (hAe r s) (hN r s),
      quadraticJetTensor_nabla_zero g c x xi a hx,
      quadraticJetTensor_nabla_first g c x xi a hx hG]
    ring
  have hDval : (∑ r, coordDeriv (fun w => ∑ s, inverseMetricInChart g c w r s *
      nablaTensorInChart g (quadraticJetTensor c x xi a) c w r s j) k x) =
      ∑ r, ∑ s, inverseMetricInChart g c x r s * (xi k * xi r * a s j) :=
    Finset.sum_congr rfl (fun r _ => hrow r)
  erw [hDval]
  have hdalg : (∑ r, ∑ s, inverseMetricInChart g c x r s * (xi k * xi r * a s j)) =
      xi k * ∑ r, ∑ s, inverseMetricInChart g c x r s * xi r * a s j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have htalg : xi j * (∑ r, ∑ s, inverseMetricInChart g c x r s * a r s) =
      ∑ r, ∑ s, inverseMetricInChart g c x r s * xi j * a r s := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hdalg, mul_assoc (xi k) (xi j), htalg]
  ring

end K24.Global.PrincipalSymbolProof
end
end K24StandalonePart7

/- Checked source module: VanishingCovector. -/
section K24StandalonePart8
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter
namespace K24.Global.VanishingCovector
open LieNaturality
abbrev OneForm := FourSpace →L[ℝ] ℝ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def oneFormInChart (eta : RawCovector M) (c : M) (x : FourSpace) : OneForm :=
  coefficientsToCovector (covectorInChart eta c x)

theorem oneFormInChart_eq (eta : RawCovector M) (c : M) (x : FourSpace) :
    oneFormInChart eta c x = (eta ((chartAt FourSpace c).symm x)).comp
      (mfderiv I4 I4 (chartAt FourSpace c).symm x) :=
  coefficientsToCovector_recover ((eta ((chartAt FourSpace c).symm x)).comp
    (mfderiv I4 I4 (chartAt FourSpace c).symm x))

theorem oneForm_basis (eta : RawCovector M) (c : M) (x : FourSpace) (i : Fin 4) :
    oneFormInChart eta c x (basisVector i) = covectorInChart eta c x i := by
  simp [oneFormInChart, coefficientsToCovector, coordProj, basisVector]

theorem oneForm_differentiableAt (eta : RawCovector M) (c : M) (x : FourSpace)
    (h : DifferentiableAt ℝ (covectorInChart eta c) x) :
    DifferentiableAt ℝ (oneFormInChart eta c) x := by
  unfold oneFormInChart coefficientsToCovector
  apply DifferentiableAt.fun_sum
  intro i _
  let T : ℝ →L[ℝ] OneForm := ContinuousLinearMap.toSpanSingleton ℝ (coordProj i)
  exact DifferentiableAt.comp (g := T) (f := fun y => covectorInChart eta c y i) x
    (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := ℝ) (F := OneForm) T)
    (differentiableAt_pi.mp h i)

theorem oneForm_transition (eta : RawCovector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    oneFormInChart eta c x = (oneFormInChart eta d (chartTransition c d x)).comp
      (fderiv ℝ (chartTransition c d) x) := by
  rw [oneFormInChart_eq, oneFormInChart_eq]
  apply ContinuousLinearMap.ext
  intro v
  change eta ((chartAt FourSpace c).symm x) (mfderiv I4 I4 (chartAt FourSpace c).symm x v) =
    eta ((chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x)))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v))
  rw [chartTransition_inverse_differential c d x v hx hd,
    (chartAt FourSpace d).left_inv hd]

theorem oneForm_differentiableAt_transition (eta : RawCovector M) (c d : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (h : DifferentiableAt ℝ (oneFormInChart eta d) (chartTransition c d x)) :
    DifferentiableAt ℝ (oneFormInChart eta c) x := by
  have hF := chartTransition_smooth c d x hx hd
  have hDF : DifferentiableAt ℝ (fderiv ℝ (chartTransition c d)) x :=
    (hF.fderiv_right (m := 1) (by decide)).differentiableAt (by norm_num)
  have he : oneFormInChart eta c =ᶠ[𝓝 x]
      (fun y => (oneFormInChart eta d (chartTransition c d y)).comp
        (fderiv ℝ (chartTransition c d) y)) := by
    filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
    exact oneForm_transition eta c d y hy.1 hy.2
  exact ((h.comp x (hF.differentiableAt (by decide))).clm_comp hDF).congr_of_eventuallyEq he

theorem fderiv_covector_const (A : FourSpace → OneForm) (x v w : FourSpace)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => A y w) x v = fderiv ℝ A x v w := by
  rw [fderiv_clm_apply hA (differentiableAt_const _)]
  simp

theorem derivative_pullback_zero (A B : FourSpace → OneForm) (F : FourSpace → FourSpace)
    (x v w : FourSpace) (hA : DifferentiableAt ℝ A (F x))
    (hB : DifferentiableAt ℝ B x) (hF : ContDiffAt ℝ 2 F x)
    (hzero : A (F x) = 0)
    (he : B =ᶠ[𝓝 x] (fun y => (A (F y)).comp (fderiv ℝ F y))) :
    fderiv ℝ B x v w = fderiv ℝ A (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : (fun y => B y w) =ᶠ[𝓝 x] (fun y => A (F y) (fderiv ℝ F y w)) :=
    he.mono (fun y hy => congrArg (fun Q : OneForm => Q w) hy)
  have hd := congrArg (fun D : FourSpace →L[ℝ] ℝ => D v) (hev.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_covector_const B x v w hB] at hd
  have hDFeval : DifferentiableAt ℝ (fun y => fderiv ℝ F y w) x :=
    hDF.clm_apply (differentiableAt_const _)
  erw [fderiv_clm_apply (hA.comp x hF1) hDFeval,
    fderiv_fun_comp x hA hF1] at hd
  simpa only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply, hzero, zero_apply, zero_add] using hd

theorem oneForm_zero (eta : RawCovector M) (c : M) (x : FourSpace)
    (he : eta ((chartAt FourSpace c).symm x) = 0) : oneFormInChart eta c x = 0 := by
  rw [oneFormInChart_eq, he]
  ext v
  rfl

theorem oneForm_first_transition_zero (eta : RawCovector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hEta : DifferentiableAt ℝ (covectorInChart eta c) x)
    (hzero : eta ((chartAt FourSpace c).symm x) = 0) (v w : FourSpace) :
    fderiv ℝ (oneFormInChart eta c) x v w =
      fderiv ℝ (oneFormInChart eta d) (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) := by
  have hxd : chartTransition c d x ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hd
  have hc : (chartAt FourSpace d).symm (chartTransition c d x) ∈ (chartAt FourSpace c).source := by
    change (chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x)) ∈ _
    rw [(chartAt FourSpace d).left_inv hd]
    exact (chartAt FourSpace c).map_target hx
  have hinv : chartTransition d c (chartTransition c d x) = x := by
    change chartAt FourSpace c ((chartAt FourSpace d).symm
      ((chartAt FourSpace d) ((chartAt FourSpace c).symm x))) = x
    rw [(chartAt FourSpace d).left_inv hd, (chartAt FourSpace c).right_inv hx]
  have hEc := oneForm_differentiableAt eta c x hEta
  have hEd := oneForm_differentiableAt_transition eta d c _ hxd hc (hinv.symm ▸ hEc)
  apply derivative_pullback_zero _ _ _ x v w hEd hEc
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
  · apply oneForm_zero
    change eta ((chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x))) = 0
    rw [(chartAt FourSpace d).left_inv hd]
    exact hzero
  · filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
    exact oneForm_transition eta c d y hy.1 hy.2


def symDerivativeForm (A : FourSpace → OneForm) (x : FourSpace) : Form :=
  (1 / 2 : ℝ) • (fderiv ℝ A x + (fderiv ℝ A x).flip)

theorem symDerivativeForm_apply (A : FourSpace → OneForm) (x v w : FourSpace) :
    symDerivativeForm A x v w =
      (1 / 2 : ℝ) * (fderiv ℝ A x v w + fderiv ℝ A x w v) := rfl

theorem coordDeriv_oneForm (eta : RawCovector M) (c : M) (x : FourSpace)
    (h : DifferentiableAt ℝ (oneFormInChart eta c) x) (i j : Fin 4) :
    coordDeriv (fun y => covectorInChart eta c y j) i x =
      fderiv ℝ (oneFormInChart eta c) x (basisVector i) (basisVector j) := by
  have heq : (fun y => covectorInChart eta c y j) =
      (fun y => oneFormInChart eta c y (basisVector j)) := by
    funext y
    exact (oneForm_basis eta c y j).symm
  rw [heq]
  exact fderiv_covector_const _ x _ _ h

theorem deltaStar_form_zero (g : RawCov2 M) (eta : RawCovector M) (c : M)
    (x : FourSpace) (hEta : DifferentiableAt ℝ (oneFormInChart eta c) x)
    (hzero : eta ((chartAt FourSpace c).symm x) = 0) :
    matrixToBilinear (deltaStarInChart g eta c x) =
      symDerivativeForm (oneFormInChart eta c) x := by
  rw [← matrixToBilinear_recover (symDerivativeForm (oneFormInChart eta c) x)]
  congr 1
  funext i j
  have hz (k : Fin 4) : covectorInChart eta c x k = 0 := by
    unfold covectorInChart
    rw [hzero]
    rfl
  simp only [deltaStarInChart, nablaCovectorInChart, hz, mul_zero,
    Finset.sum_const_zero, sub_zero, coordDeriv_oneForm eta c x hEta,
    symDerivativeForm_apply]

theorem symDerivativeForm_transition_zero (eta : RawCovector M) (c d : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hEta : DifferentiableAt ℝ (covectorInChart eta c) x)
    (hzero : eta ((chartAt FourSpace c).symm x) = 0) :
    symDerivativeForm (oneFormInChart eta c) x =
      bilinearPullback (symDerivativeForm (oneFormInChart eta d) (chartTransition c d x))
        (fderiv ℝ (chartTransition c d) x) := by
  ext v w
  simp only [bilinearPullback_apply, symDerivativeForm_apply,
    oneForm_first_transition_zero eta c d x hx hd hEta hzero]

theorem deltaStar_chart_recovery_zero (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hEta : DifferentiableAt ℝ (covectorInChart eta c) x)
    (hzero : eta ((chartAt FourSpace c).symm x) = 0) (i j : Fin 4) :
    cov2InChart (deltaStar g eta) c x i j = deltaStarInChart g eta c x i j := by
  let p := (chartAt FourSpace c).symm x
  have hp : p ∈ (chartAt FourSpace p).source := mem_chart_source FourSpace p
  have hxp : chartTransition c p x ∈ (chartAt FourSpace p).target :=
    (chartAt FourSpace p).map_source hp
  have hc : (chartAt FourSpace p).symm (chartTransition c p x) ∈ (chartAt FourSpace c).source := by
    change (chartAt FourSpace p).symm ((chartAt FourSpace p) p) ∈ _
    rw [(chartAt FourSpace p).left_inv hp]
    exact (chartAt FourSpace c).map_target hx
  have hinv : chartTransition p c (chartTransition c p x) = x := by
    change chartAt FourSpace c ((chartAt FourSpace p).symm ((chartAt FourSpace p) p)) = x
    rw [(chartAt FourSpace p).left_inv hp]
    exact (chartAt FourSpace c).right_inv hx
  have hEc := oneForm_differentiableAt eta c x hEta
  have hEp := oneForm_differentiableAt_transition eta p c _ hxp hc (hinv.symm ▸ hEc)
  have hz : eta ((chartAt FourSpace p).symm (chartTransition c p x)) = 0 := by
    change eta ((chartAt FourSpace p).symm ((chartAt FourSpace p) p)) = 0
    rw [(chartAt FourSpace p).left_inv hp]
    exact hzero
  have hform := symDerivativeForm_transition_zero eta c p x hx hp hEta hzero
  have hvalues := congrArg (fun Q : Form => Q (basisVector i) (basisVector j)) hform
  have hDp (v : FourSpace) :
      fderiv ℝ (chartTransition c p) x v =
        mfderiv I4 I4 (chartAt FourSpace p) p
          (mfderiv I4 I4 (chartAt FourSpace c).symm x v) := by
    rw [chartTransition_derivative c p x hx hp]
    rfl
  change matrixToBilinear (deltaStarInChart g eta p (chartTransition c p x))
      (mfderiv I4 I4 (chartAt FourSpace p) p
        (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i)))
      (mfderiv I4 I4 (chartAt FourSpace p) p
        (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))) = _
  rw [deltaStar_form_zero g eta p _ hEp hz, ← hDp, ← hDp]
  have hcform := congrArg (fun Q : Form => Q (basisVector i) (basisVector j))
    (deltaStar_form_zero g eta c x hEc hzero)
  rw [matrixToForm_basis] at hcform
  exact hvalues.symm.trans hcform.symm

end K24.Global.VanishingCovector
end
end K24StandalonePart8

/- Checked source module: Assembly. -/
section K24StandalonePart9

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.PrincipalSymbolProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covector_zero_of_coefficients (eta : RawCovector M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hz : ∀ j, covectorInChart eta c x j = 0) :
    eta ((chartAt FourSpace c).symm x) = 0 := by
  have hr := covector_chart_recovery eta c ((chartAt FourSpace c).symm x)
    ((chartAt FourSpace c).map_target hx)
  rw [(chartAt FourSpace c).right_inv hx] at hr
  rw [← hr]
  have he : covectorInChart eta c x = 0 := funext hz
  simp [he, covectorFromChartAt, coefficientsToCovector]

theorem cov2ContDiff_two_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff 2 g := by
  intro c
  exact (cov2ContDiff_of_metricAdmissible C b g hg c).of_le
    (by exact_mod_cast b.order_ge_two)

theorem metricAdmissible_contDiffAt (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ 2 (cov2InChart g c) x :=
  (cov2ContDiff_two_of_metricAdmissible C b g hg c x hx).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)

theorem quadraticJetTensor_bianchi_difference_first (ghat z : RawCov2 M)
    (c : M) (x : FourSpace) (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hAg : ContDiffAt ℝ 2 (inverseMetricInChart ghat c) x)
    (hAz : ContDiffAt ℝ 2 (inverseMetricInChart z c) x)
    (hGg : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart ghat c w p k i) x)
    (hGz : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart z c w p k i) x)
    (k j : Fin 4) :
    coordDeriv (fun y => bianchiInChart ghat (quadraticJetTensor c x xi a) c y j -
      bianchiInChart z (quadraticJetTensor c x xi a) c y j) k x =
      xi k * bianchiDifferenceSymbol ghat z c x xi a j := by
  have hg := quadraticJetTensor_bianchi_differentiableAt ghat c x x xi a hx hAg hGg j
  have hz := quadraticJetTensor_bianchi_differentiableAt z c x x xi a hx hAz hGz j
  change fderiv ℝ _ x (basisVector k) = _
  rw [fderiv_fun_sub hg hz]
  change coordDeriv _ k x - coordDeriv _ k x = _
  rw [quadraticJetTensor_bianchi_first ghat c x xi a hx hAg hGg,
    quadraticJetTensor_bianchi_first z c x xi a hx hAz hGz]
  simp only [bianchiDifferenceSymbol, inverseDifferenceInChart, Matrix.sub_apply,
    sub_mul, Finset.sum_sub_distrib]
  ring

/-- The local differential calculation; its two hypotheses isolate the genuine
    chart recovery of Bianchi on the locally smooth quadratic test section. -/
theorem tensorDefectPrincipalSymbol_of_bianchi_eventually (ghat z : RawCov2 M)
    (c : M) (x : FourSpace) (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hAg : ContDiffAt ℝ 2 (inverseMetricInChart ghat c) x)
    (hAz : ContDiffAt ℝ 2 (inverseMetricInChart z c) x)
    (hGg : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart ghat c w p k i) x)
    (hGz : ∀ p k i, DifferentiableAt ℝ (fun w => christoffelInChart z c w p k i) x)
    (hrecg : covectorInChart (bianchi ghat (quadraticJetTensor c x xi a)) c =ᶠ[𝓝 x]
      fun y j => bianchiInChart ghat (quadraticJetTensor c x xi a) c y j)
    (hrecz : covectorInChart (bianchi z (quadraticJetTensor c x xi a)) c =ᶠ[𝓝 x]
      fun y j => bianchiInChart z (quadraticJetTensor c x xi a) c y j)
    (i j : Fin 4) :
    tensorDefectPrincipalSymbol ghat z c x xi a i j =
      tensorDefectSymbolFormula ghat z c x xi a i j := by
  let eta := bianchi ghat (quadraticJetTensor c x xi a) -
    bianchi z (quadraticJetTensor c x xi a)
  have he : covectorInChart eta c =ᶠ[𝓝 x] (fun y j =>
      bianchiInChart ghat (quadraticJetTensor c x xi a) c y j -
      bianchiInChart z (quadraticJetTensor c x xi a) c y j) := by
    filter_upwards [hrecg, hrecz] with y hg hz
    funext j
    change covectorInChart (bianchi ghat (quadraticJetTensor c x xi a)) c y j -
      covectorInChart (bianchi z (quadraticJetTensor c x xi a)) c y j = _
    rw [congrFun hg j, congrFun hz j]
  have hd (j : Fin 4) :=
    (quadraticJetTensor_bianchi_differentiableAt ghat c x x xi a hx hAg hGg j).sub
      (quadraticJetTensor_bianchi_differentiableAt z c x x xi a hx hAz hGz j)
  have hEta : DifferentiableAt ℝ (covectorInChart eta c) x :=
    (differentiableAt_pi.mpr hd).congr_of_eventuallyEq he
  have hzero : eta ((chartAt FourSpace c).symm x) = 0 := by
    apply covector_zero_of_coefficients eta c x hx
    intro j
    rw [congrFun he.self_of_nhds j]
    dsimp only
    rw [quadraticJetTensor_bianchi_zero ghat c x xi a hx
        (hAg.differentiableAt (by norm_num)),
      quadraticJetTensor_bianchi_zero z c x xi a hx
        (hAz.differentiableAt (by norm_num)), sub_self]
  have hfirst (k j : Fin 4) :
      coordDeriv (fun y => covectorInChart eta c y j) k x =
        xi k * bianchiDifferenceSymbol ghat z c x xi a j := by
    have he' : (fun y => covectorInChart eta c y j) =ᶠ[𝓝 x]
        (fun y => bianchiInChart ghat (quadraticJetTensor c x xi a) c y j -
          bianchiInChart z (quadraticJetTensor c x xi a) c y j) :=
      he.mono (fun y hy => congrFun hy j)
    change fderiv ℝ _ x (basisVector k) = _
    rw [he'.fderiv_eq]
    exact quadraticJetTensor_bianchi_difference_first ghat z c x xi a hx hAg hAz hGg hGz k j
  change cov2InChart (deltaStar z eta) c x i j = _
  rw [VanishingCovector.deltaStar_chart_recovery_zero z eta c x hx hEta hzero]
  have hzc (k : Fin 4) : covectorInChart eta c x k = 0 := by
    unfold covectorInChart
    rw [hzero]
    rfl
  simp only [deltaStarInChart, nablaCovectorInChart, hzc, mul_zero,
    Finset.sum_const_zero, sub_zero, hfirst, tensorDefectSymbolFormula]

end K24.Global.PrincipalSymbolProof
end
end K24StandalonePart9

/- Checked source module: Reduction. -/
section K24StandalonePart10

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.PrincipalSymbolProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- This is the remaining dependency, not an axiom or a proved naturality claim. -/
def BianchiLocalRecovery : Prop :=
  ∀ (g u : RawCov2 M), IsMetric g → Cov2ContDiff 1 g →
    ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ContDiffAt ℝ 1 (cov2InChart u c) x →
      ∀ j : Fin 4, covectorInChart (bianchi g u) c x j = bianchiInChart g u c x j

theorem quadraticJetTensor_contDiffAt_matrix (c : M) (x y : FourSpace)
    (xi : Fin 4 → ℝ) (a : Mat4) (hy : y ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (cov2InChart (quadraticJetTensor c x xi a) c) y := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact quadraticJetTensor_contDiffAt c x y xi a hy i j

theorem bianchi_quadraticJet_recovery_eventually (hB : BianchiLocalRecovery (M := M))
    (g : RawCov2 M) (hg : IsMetric g) (hDg : Cov2ContDiff 1 g)
    (c : M) (x : FourSpace) (xi : Fin 4 → ℝ) (a : Mat4)
    (hx : x ∈ (chartAt FourSpace c).target) :
    covectorInChart (bianchi g (quadraticJetTensor c x xi a)) c =ᶠ[𝓝 x]
      fun y j => bianchiInChart g (quadraticJetTensor c x xi a) c y j := by
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
  funext j
  exact hB g (quadraticJetTensor c x xi a) hg hDg c y hy
    ((quadraticJetTensor_contDiffAt_matrix c x y xi a hy).of_le (by decide)) j

/-- All original admissibility hypotheses are discharged here. The only remaining
    input is Bianchi local chart recovery, explicitly exposed as `hB`. -/
theorem tensorDefectPrincipalSymbol_of_bianchi_local_recovery
    (hB : BianchiLocalRecovery (M := M))
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (ghat z : RawCov2 M)
    (hg : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (xi : Fin 4 → ℝ) (a : Mat4) (i j : Fin 4) :
    tensorDefectPrincipalSymbol ghat z c x xi a i j =
      tensorDefectSymbolFormula ghat z c x xi a i j := by
  have hg2 := metricAdmissible_contDiffAt C b ghat hg c x hx
  have hz2 := metricAdmissible_contDiffAt C b z hz c x hx
  have hgc : Cov2ContDiff 1 ghat := fun c =>
    (cov2ContDiff_two_of_metricAdmissible C b ghat hg c).of_le (by norm_num)
  have hzc : Cov2ContDiff 1 z := fun c =>
    (cov2ContDiff_two_of_metricAdmissible C b z hz c).of_le (by norm_num)
  exact tensorDefectPrincipalSymbol_of_bianchi_eventually ghat z c x xi a hx
    (PrincipalSymbolRegularity.contDiffAt_inverseMetric ghat hg.metric c x hx 2 hg2)
    (PrincipalSymbolRegularity.contDiffAt_inverseMetric z hz.metric c x hx 2 hz2)
    (PrincipalSymbolRegularity.christoffel_differentiableAt ghat hg.metric c x hx hg2)
    (PrincipalSymbolRegularity.christoffel_differentiableAt z hz.metric c x hx hz2)
    (bianchi_quadraticJet_recovery_eventually hB ghat hg.metric hgc c x xi a hx)
    (bianchi_quadraticJet_recovery_eventually hB z hz.metric hzc c x xi a hx) i j

end K24.Global.PrincipalSymbolProof
end
end K24StandalonePart10

/- Checked source module: PrincipalSymbol. -/
section K24StandalonePart11

set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global.PrincipalSymbolProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem principal_symbol_identity
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (ghat z : RawCov2 M)
    (hg : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (xi : Fin 4 → ℝ) (a : Mat4) (i j : Fin 4) :
    tensorDefectPrincipalSymbol ghat z c x xi a i j =
      tensorDefectSymbolFormula ghat z c x xi a i j :=
  tensorDefectPrincipalSymbol_of_bianchi_local_recovery
    BianchiNaturality.bianchi_chart_recovery C b ghat z hg hz c x hx xi a i j

end K24.Global.PrincipalSymbolProof

universe u
open K24.Global

theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M],
      ∀ (C : BoundedLocalCover M) (metricBounds : MetricCoefficientNumerics)
        (ghat z : RawCov2 M),
        MetricAdmissible C metricBounds ghat →
        MetricAdmissible C metricBounds z →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ (xi : Fin 4 → ℝ) (a : Mat4) (i j : Fin 4),
            tensorDefectPrincipalSymbol ghat z c x xi a i j =
              tensorDefectSymbolFormula ghat z c x xi a i j := by
  intro M _ _ _ C b ghat z hg hz c x hx xi a i j
  exact PrincipalSymbolProof.principal_symbol_identity C b ghat z hg hz c x hx xi a i j
end K24StandalonePart11
