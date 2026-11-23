-- Prove2me | solution 1 for NoHair.static_quotient_einstein_scalar_equations
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:58:20.351401+00:00
-- url     : https://prove2.me/submissions/40a4371d-bb6b-4222-93cd-ee74aa3ad5b8

import Theorems.Thm_NoHair_spatial_conformal_ricci_three
import Theorems.Thm_NoHair_spatial_conformal_connection
import Theorems.Thm_NoHair_spatial_laplacian_in_divergence_form
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private lemma pd_local {f g : X → ℝ} {x:X} (h : f=ᶠ[𝓝 x]g) (i:I) : spatialADMPartial i f x=spatialADMPartial i g x :=
  congrArg (fun L : X →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) h.fderiv_eq
private lemma pd_mul {f g : X → ℝ} {x : X} (df : DifferentiableAt ℝ f x) (dg : DifferentiableAt ℝ g x) (i : I) :
    spatialADMPartial i (fun y => f y*g y) x = spatialADMPartial i f x*g x + f x*spatialADMPartial i g x := by
  have v := (df.hasFDerivAt.mul dg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y*g y) x = _ at v
  unfold spatialADMPartial
  rw [v]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring
private lemma pd_log {N : X → ℝ} {x:X} (d : DifferentiableAt ℝ N x) (pn : N x ≠ 0) (i:I) :
    spatialADMPartial i (fun y => Real.log (N y)) x=(N x)⁻¹*spatialADMPartial i N x := by
  unfold spatialADMPartial
  rw [(d.hasFDerivAt.log pn).fderiv,ContinuousLinearMap.smul_apply,smul_eq_mul]

theorem solution (W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hW : IsOpen W) (sn : ContDiffOn ℝ ∞ N W) (sh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W)
    (positive : ∀ x ∈ W, 0 < N x ∧ (h x).PosDef)
    (equations : ∀ x ∈ W,
      (∀ i j : Fin 3, staticSpatialHessian N h i j x = N x * spatialRicciTensor h x i j) ∧
      (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x) = 0) :
    let γ : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := fun y => N y^2 • h y
    let u := fun y => Real.log (N y)
    ∀ x ∈ W, (∀ i j : Fin 3, spatialRicciTensor γ x i j = 2*spatialADMPartial i u x*spatialADMPartial j u x) ∧
      (∑ i : Fin 3, spatialADMPartial i (fun y => Real.sqrt (γ y).det * staticRaisedGradient u γ i y) x) = 0 := by
  let p:=fun z : X => Real.sqrt |N z|
  let u:=fun z : X => Real.log (N z)
  let γ : X → Mat :=fun z => N z^2 • h z
  have near {x:X} (hx : x∈W) : ∀ᶠ y in 𝓝 x, y∈W := hW.mem_nhds hx
  have pn {x:X} (hx : x∈W) := (positive x hx).1
  have pp {x:X} (hx : x∈W) : 0<p x := Real.sqrt_pos_of_pos (abs_pos.mpr (pn hx).ne')
  have hp {x:X} (hx : x∈W) : p x^2=N x := (Real.sq_sqrt (abs_nonneg (N x))).trans (abs_of_pos (pn hx))
  have pw (x:X) : p x^4=N x^2 := by
    calc
      p x^4=(p x^2)^2 := by ring
      _=|N x|^2 := by rw [show p x^2=|N x| from Real.sq_sqrt (abs_nonneg _)]
      _=N x^2 := sq_abs _
  have gp : γ=fun y => p y^4 • h y := funext fun y => by rw [pw]
  have sp : ContDiffOn ℝ ∞ p W := (sn.sqrt (fun y hy => (pn hy).ne')).congr
    (fun y hy => by simp [p,abs_of_pos (pn hy)])
  have dp {x:X} (hx : x∈W) := (sp.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have dn {x:X} (hx : x∈W) := (sn.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have dN {x:X} (hx : x∈W) (i:I) : spatialADMPartial i N x=2*p x*spatialADMPartial i p x := by
    have same : N =ᶠ[𝓝 x] (fun y => p y*p y) := (near hx).mono (fun y hy => (hp hy).symm.trans (pow_two (p y)))
    rw [pd_local same,pd_mul (dp hx) (dp hx)]
    ring
  have hes {x:X} (hx : x∈W) (i j:I) : staticSpatialHessian N h i j x =
      2*p x*staticSpatialHessian p h i j x+2*spatialADMPartial i p x*spatialADMPartial j p x := by
    have same : spatialADMPartial j N =ᶠ[𝓝 x] (fun y => 2*(p y*spatialADMPartial j p y)) :=
      (near hx).mono (fun y hy => (dN hy j).trans (mul_assoc _ _ _))
    have dj : DifferentiableAt ℝ (spatialADMPartial j p) x :=
      (((sp.contDiffAt (hW.mem_nhds hx)).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have dd : spatialADMPartial i (spatialADMPartial j N) x=2*(spatialADMPartial i p x*spatialADMPartial j p x + p x * spatialADMPartial i (spatialADMPartial j p) x) := by
      rw [pd_local same,pd_mul (f:=fun _:X => (2:ℝ)) (g:=fun y => p y*spatialADMPartial j p y) (differentiableAt_const (2:ℝ)) ((dp hx).mul dj),pd_mul (dp hx) dj]
      simp [spatialADMPartial]
    unfold staticSpatialHessian
    rw [dd]
    simp_rw [dN hx]
    simp only [Fin.sum_univ_three]
    ring
  have hinv {x:X} (hx : x∈W) : (γ x)⁻¹ = (N x^2)⁻¹ • (h x)⁻¹ := by
    have hi := (spatial_conformal_connection p h W hW sp sh (fun y hy => (positive y hy).2) x hx (pp hx).ne').1
    simpa only [pw,γ] using hi
  have dens {x:X} (hx : x∈W) (i:I) : Real.sqrt (γ x).det * staticRaisedGradient u γ i x =
      Real.sqrt (h x).det * staticRaisedGradient N h i x := by
    have deteq : Real.sqrt (γ x).det = (N x)^3 * Real.sqrt (h x).det := by
      change Real.sqrt ((N x^2 • h x : Mat).det)=_
      rw [Matrix.det_smul,Fintype.card_fin,show (N x^2)^3=((N x)^3)^2 by ring,
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_pos (pn hx) 3).le]
    rw [deteq]
    unfold staticRaisedGradient
    rw [hinv hx]
    simp only [u,Matrix.smul_apply,smul_eq_mul,pd_log (dn hx) (pn hx).ne',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [(pn hx).ne'] <;> ring
  change ∀ x ∈ W, (∀ i j : I, spatialRicciTensor γ x i j=2*spatialADMPartial i u x*spatialADMPartial j u x) ∧
    (∑ i : I, spatialADMPartial i (fun y => Real.sqrt (γ y).det*staticRaisedGradient u γ i y) x)=0
  intro x hx
  constructor
  · intro i j
    let H:=fun a b => staticSpatialHessian p h a b x
    let T:=∑ a : I,∑ b : I,(h x)⁻¹ a b*H a b
    have tr : T= -staticLapseGradientSq p h x/p x := by
      apply (eq_div_iff (pp hx).ne').2
      have eq := (equations x hx).2
      simp_rw [hes hx] at eq
      dsimp only [T,H,staticLapseGradientSq,staticRaisedGradient]
      simp only [Fin.sum_univ_three] at eq ⊢
      linear_combination eq/2
    have ri : spatialRicciTensor h x i j=(2*p x*H i j+2*spatialADMPartial i p x*spatialADMPartial j p x)/(p x)^2 := by
      apply (eq_div_iff (pow_ne_zero 2 (pp hx).ne')).2
      rw [hp hx,mul_comm,←(equations x hx).1 i j,hes hx] <;> rfl
    change spatialRicciTensor γ x i j = 2*spatialADMPartial i u x*spatialADMPartial j u x
    rw [gp,spatial_conformal_ricci_three p h W hW sp sh (fun z hz => (positive z hz).2) x hx (pp hx).ne' i j,ri]
    change _-(2/p x)*h x i j*T+_ -_ = _
    rw [tr]
    dsimp only [u,H]
    rw [pd_log (dn hx) (pn hx).ne' i,pd_log (dn hx) (pn hx).ne' j,dN hx i,dN hx j,←hp hx]
    field_simp [(pp hx).ne'] <;> ring
  · have base:=spatial_laplacian_in_divergence_form N h W hW sn sh (fun z hz => (positive z hz).2) x hx
    rw [(equations x hx).2,mul_zero] at base
    rw [←base]
    apply Finset.sum_congr rfl
    intro i _
    exact pd_local ((near hx).mono (fun z hz => dens hz i)) i
