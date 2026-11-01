-- Prove2me | solution 1 for MaxValSens.Wolfe.theorem_3_3_kkt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:34:47.817774+00:00
-- url     : https://prove2.me/submissions/0901a9d2-c401-4c36-940a-b1356a5349d6

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe.KKTAux

/-- injections of the three blocks into `ℝⁿ × ℝᵐ × ℝ^q` -/
noncomputable def Jx (n m q : ℕ) : E n →L[ℝ] E n × E m × (Fin q → ℝ) :=
  ContinuousLinearMap.inl ℝ (E n) (E m × (Fin q → ℝ))

noncomputable def Jy (n m q : ℕ) : E m →L[ℝ] E n × E m × (Fin q → ℝ) :=
  (0 : E m →L[ℝ] E n).prod ((ContinuousLinearMap.id ℝ (E m)).prod 0)

noncomputable def Jl (n m q : ℕ) : (Fin q → ℝ) →L[ℝ] E n × E m × (Fin q → ℝ) :=
  (0 : (Fin q → ℝ) →L[ℝ] E n).prod ((0 : (Fin q → ℝ) →L[ℝ] E m).prod
    (ContinuousLinearMap.id ℝ (Fin q → ℝ)))

lemma decomp {n m q : ℕ} (dz : E n × E m × (Fin q → ℝ)) :
    dz = Jx n m q dz.1 + Jy n m q dz.2.1 + Jl n m q dz.2.2 := by
  obtain ⟨a, b, c⟩ := dz
  simp [Jx, Jy, Jl]

lemma hasFDerivAt_Jx {n m q : ℕ} (x : E n) (y : E m) (l : Fin q → ℝ) :
    HasFDerivAt (fun x' : E n => ((x', y, l) : E n × E m × (Fin q → ℝ))) (Jx n m q) x :=
  hasFDerivAt_prodMk_left (𝕜 := ℝ) x ((y, l) : E m × (Fin q → ℝ))

lemma hasFDerivAt_Jy {n m q : ℕ} (x : E n) (y : E m) (l : Fin q → ℝ) :
    HasFDerivAt (fun y' : E m => ((x, y', l) : E n × E m × (Fin q → ℝ))) (Jy n m q) y :=
  (hasFDerivAt_const x y).prodMk ((hasFDerivAt_id y).prodMk (hasFDerivAt_const l y))

lemma hasFDerivAt_Jl {n m q : ℕ} (x : E n) (y : E m) (l : Fin q → ℝ) :
    HasFDerivAt (fun l' : Fin q → ℝ => ((x, y, l') : E n × E m × (Fin q → ℝ))) (Jl n m q) l :=
  (hasFDerivAt_const x l).prodMk ((hasFDerivAt_const y l).prodMk (hasFDerivAt_id l))

variable {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)

/-- the Lagrangian as a function of `z = (x, y, λ)` -/
noncomputable def Phi (z : E n × E m × (Fin q → ℝ)) : ℝ := Lag 1 f g z.1 z.2.1 z.2.2

/-- `h(z) = ∇_y L(z)` -/
noncomputable def hfun (z : E n × E m × (Fin q → ℝ)) : E m := gradY 1 f g z.1 z.2.1 z.2.2

variable {f g}

lemma Phi_contDiff (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) :
    ContDiff ℝ 2 (Phi f g) := by
  unfold Phi Lag
  have h1 : ContDiff ℝ 2 (fun z : E n × E m × (Fin q → ℝ) => (z.1, z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  apply ContDiff.sub
  · exact contDiff_const.mul (hf.comp h1)
  · apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_snd)).mul ((hg i).comp h1)

lemma hfun_eq (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (z : E n × E m × (Fin q → ℝ)) :
    hfun f g z = (InnerProductSpace.toDual ℝ (E m)).symm ((fderiv ℝ (Phi f g) z).comp (Jy n m q)) := by
  obtain ⟨x, y, l⟩ := z
  unfold hfun gradY gradient
  congr 1
  have hd : DifferentiableAt ℝ (Phi f g) (x, y, l) :=
    ((Phi_contDiff hf hg).differentiable (by norm_num)).differentiableAt
  exact (hd.hasFDerivAt.comp y (hasFDerivAt_Jy x y l)).fderiv

lemma gradX_eq (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) :
    gradX f g x y l = (InnerProductSpace.toDual ℝ (E n)).symm
      ((fderiv ℝ (Phi f g) (x, y, l)).comp (Jx n m q)) := by
  unfold gradX gradient
  congr 1
  have hd : DifferentiableAt ℝ (Phi f g) (x, y, l) :=
    ((Phi_contDiff hf hg).differentiable (by norm_num)).differentiableAt
  exact (hd.hasFDerivAt.comp x (hasFDerivAt_Jx x y l)).fderiv

lemma Phi_lam (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (dl : Fin q → ℝ) :
    fderiv ℝ (Phi f g) (x, y, l) (Jl n m q dl) = -∑ i, dl i * g i x y := by
  have hd : DifferentiableAt ℝ (Phi f g) (x, y, l) :=
    ((Phi_contDiff hf hg).differentiable (by norm_num)).differentiableAt
  have h1 := hd.hasFDerivAt.comp l (hasFDerivAt_Jl x y l)
  let ℓ : (Fin q → ℝ) →L[ℝ] ℝ := -(∑ i, g i x y • ContinuousLinearMap.proj i)
  have h2 : HasFDerivAt (fun l' : Fin q → ℝ => Phi f g (x, y, l')) ℓ l := by
    have : (fun l' : Fin q → ℝ => Phi f g (x, y, l')) = fun l' => 1 * f x y + ℓ l' := by
      funext l'
      simp only [Phi, Lag, ℓ, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul]
      rw [sub_eq_add_neg]
      congr 2
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    exact (ℓ.hasFDerivAt).const_add _
  have := h1.unique h2
  have h3 := congrArg (fun L => L dl) this
  simp only [ContinuousLinearMap.comp_apply] at h3
  rw [h3]
  simp [ℓ, mul_comm]

/-- (F1) -/
lemma F1 (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (dz : E n × E m × (Fin q → ℝ)) :
    fderiv ℝ (Phi f g) (x, y, l) dz = ⟪gradX f g x y l, dz.1⟫_ℝ + ⟪hfun f g (x, y, l), dz.2.1⟫_ℝ
      - ∑ i, dz.2.2 i * g i x y := by
  conv_lhs => rw [decomp dz]
  rw [map_add, map_add, Phi_lam hf hg, gradX_eq hf hg, hfun_eq hf hg,
    InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.comp_apply]
  ring

lemma hfun_differentiable (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) :
    Differentiable ℝ (hfun f g) := by
  rw [show hfun f g = fun z => (InnerProductSpace.toDual ℝ (E m)).symm
    ((fderiv ℝ (Phi f g) z).comp (Jy n m q)) from funext (hfun_eq hf hg)]
  have h1 : Differentiable ℝ (fderiv ℝ (Phi f g)) :=
    ((Phi_contDiff hf hg).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  intro z
  exact (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.differentiableAt.comp z
    ((h1 z).clm_comp (differentiableAt_const _))

lemma s_eq (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (μ : E m) :
    (fun z => ⟪hfun f g z, μ⟫_ℝ) = fun z => fderiv ℝ (Phi f g) z (Jy n m q μ) := by
  funext z
  rw [hfun_eq hf hg, InnerProductSpace.toDual_symm_apply]
  rfl

lemma s_hasFDerivAt (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (μ : E m)
    (z : E n × E m × (Fin q → ℝ)) :
    HasFDerivAt (fun z => ⟪hfun f g z, μ⟫_ℝ)
      ((ContinuousLinearMap.apply ℝ ℝ (Jy n m q μ)).comp (fderiv ℝ (fderiv ℝ (Phi f g)) z)) z := by
  rw [s_eq hf hg]
  have h1 : Differentiable ℝ (fderiv ℝ (Phi f g)) :=
    ((Phi_contDiff hf hg).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (Jy n m q μ)).hasFDerivAt.comp z (h1 z).hasFDerivAt

lemma Dh_core (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (μ : E m)
    (z dz : E n × E m × (Fin q → ℝ)) :
    ⟪fderiv ℝ (hfun f g) z dz, μ⟫_ℝ = fderiv ℝ (fderiv ℝ (Phi f g)) z dz (Jy n m q μ) := by
  have h1 : HasFDerivAt (fun z => ⟪hfun f g z, μ⟫_ℝ)
      ((innerSL ℝ μ).comp (fderiv ℝ (hfun f g) z)) z := by
    have := (innerSL ℝ μ).hasFDerivAt.comp z (hfun_differentiable hf hg z).hasFDerivAt
    have e : (fun z => ⟪hfun f g z, μ⟫_ℝ) = (innerSL ℝ μ) ∘ hfun f g := by
      funext z; simp [real_inner_comm]
    rw [e]; exact this
  have := congrArg (fun L => L dz) (h1.unique (s_hasFDerivAt hf hg μ z))
  simpa [real_inner_comm] using this

lemma hessXY_inner (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (μ : E m) (dx : E n) :
    ⟪hessXY f g x y l μ, dx⟫_ℝ =
      fderiv ℝ (fderiv ℝ (Phi f g)) (x, y, l) (Jx n m q dx) (Jy n m q μ) := by
  unfold hessXY gradient
  rw [InnerProductSpace.toDual_symm_apply]
  have h := (s_hasFDerivAt hf hg μ (x, y, l)).comp x (hasFDerivAt_Jx x y l)
  have e : (fun x' => ⟪gradY 1 f g x' y l, μ⟫_ℝ) =
      (fun z => ⟪hfun f g z, μ⟫_ℝ) ∘ (fun x' : E n => ((x', y, l) : E n × E m × (Fin q → ℝ))) :=
    rfl
  rw [e, h.fderiv]
  rfl

lemma hessYY_eq (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (μ : E m) :
    hessYY f g x y l μ = fderiv ℝ (hfun f g) (x, y, l) (Jy n m q μ) := by
  unfold hessYY
  have h := (hfun_differentiable hf hg (x, y, l)).hasFDerivAt.comp y (hasFDerivAt_Jy x y l)
  have e : (fun y' => gradY 1 f g x y' l) =
      hfun f g ∘ (fun y' : E m => ((x, y', l) : E n × E m × (Fin q → ℝ))) := rfl
  rw [e, h.fderiv]
  rfl

lemma hessYY_inner (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (μ : E m) (dy : E m) :
    ⟪hessYY f g x y l μ, dy⟫_ℝ =
      fderiv ℝ (fderiv ℝ (Phi f g)) (x, y, l) (Jy n m q dy) (Jy n m q μ) := by
  rw [hessYY_eq hf hg, Dh_core hf hg]
  have hsymm := ((Phi_contDiff hf hg).contDiffAt (x := (x, y, l))).isSymmSndFDerivAt
    (by simp [minSmoothness_of_isRCLikeNormedField])
  exact hsymm _ _

lemma gradY_eq' (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2))
    (x : E n) (y : E m) (lam : Fin q → ℝ) :
    gradY 1 f g x y lam = gradient (f x) y - ∑ i, lam i • gradient (g i x) y := by
  have dfx : Differentiable ℝ (f x) := fun y' =>
    ((hf.differentiable (by norm_num)) (x, y')).comp y'
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y').differentiableAt
  have dgx : ∀ i, Differentiable ℝ (g i x) := fun i y' =>
    (((hg i).differentiable (by norm_num)) (x, y')).comp y'
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y').differentiableAt
  unfold gradY Lag gradient
  simp only [one_mul]
  rw [fderiv_fun_sub (dfx y) (DifferentiableAt.fun_sum fun i _ => (dgx i y).const_mul _)]
  rw [fderiv_fun_sum (fun i _ => (dgx i y).const_mul _)]
  rw [Finset.sum_congr rfl fun i _ => fderiv_const_mul (dgx i y) (lam i)]
  simp only [map_sub, map_sum, map_smul]

lemma lam_inner (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (μ : E m) (dl : Fin q → ℝ) :
    fderiv ℝ (fderiv ℝ (Phi f g)) (x, y, l) (Jl n m q dl) (Jy n m q μ) =
      -∑ i, dl i * dgY g i x y μ := by
  have h1 := (s_hasFDerivAt hf hg μ (x, y, l)).comp l (hasFDerivAt_Jl x y l)
  let ℓ : (Fin q → ℝ) →L[ℝ] ℝ := -(∑ i, dgY g i x y μ • ContinuousLinearMap.proj i)
  have h2 : HasFDerivAt ((fun z => ⟪hfun f g z, μ⟫_ℝ) ∘
      (fun l' : Fin q → ℝ => ((x, y, l') : E n × E m × (Fin q → ℝ)))) ℓ l := by
    have : ((fun z => ⟪hfun f g z, μ⟫_ℝ) ∘
        (fun l' : Fin q → ℝ => ((x, y, l') : E n × E m × (Fin q → ℝ)))) =
        fun l' => ⟪gradient (f x) y, μ⟫_ℝ + ℓ l' := by
      funext l'
      simp only [Function.comp_apply, hfun]
      rw [gradY_eq' hf hg, inner_sub_left, sum_inner]
      simp only [inner_smul_left, ℓ, dgY, gradient, InnerProductSpace.toDual_symm_apply]
      simp [sub_eq_add_neg, mul_comm]
    rw [this]
    exact (ℓ.hasFDerivAt).const_add _
  have h3 := congrArg (fun L => L dl) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h3
  rw [h3]
  simp [ℓ, mul_comm]

/-- (F2) -/
lemma F2 (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (x : E n) (y : E m)
    (l : Fin q → ℝ) (μ : E m) (dz : E n × E m × (Fin q → ℝ)) :
    ⟪fderiv ℝ (hfun f g) (x, y, l) dz, μ⟫_ℝ = ⟪hessXY f g x y l μ, dz.1⟫_ℝ +
      ⟪hessYY f g x y l μ, dz.2.1⟫_ℝ - ∑ i, dz.2.2 i * dgY g i x y μ := by
  rw [Dh_core hf hg, hessXY_inner hf hg, hessYY_inner hf hg]
  conv_lhs => rw [decomp dz]
  rw [map_add, map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    lam_inner hf hg]
  ring

lemma hessXY_clm (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2))
    (x : E n) (y : E m) (l : Fin q → ℝ) :
    ∃ T : E m →L[ℝ] E n, ∀ u, hessXY f g x y l u = T u := by
  have hG : ∀ x', gradY 1 f g x' y l =
      (InnerProductSpace.toDual ℝ (E m)).symm ((fderiv ℝ (Phi f g) (x', y, l)).comp (Jy n m q)) :=
    fun x' => hfun_eq hf hg (x', y, l)
  have hGd : DifferentiableAt ℝ (fun x' => gradY 1 f g x' y l) x := by
    rw [show (fun x' => gradY 1 f g x' y l) = fun x' =>
      (InnerProductSpace.toDual ℝ (E m)).symm ((fderiv ℝ (Phi f g) (x', y, l)).comp (Jy n m q))
      from funext hG]
    have h1 : Differentiable ℝ (fderiv ℝ (Phi f g)) :=
      ((Phi_contDiff hf hg).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have h2 : DifferentiableAt ℝ (fun x' : E n => ((x', y, l) : E n × E m × (Fin q → ℝ))) x :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ (fun x' : E n => (fderiv ℝ (Phi f g) (x', y, l)).comp (Jy n m q)) x :=
      ((h1 _).comp x h2).clm_comp (differentiableAt_const _)
    exact (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.differentiableAt.comp x h3
  set D := fderiv ℝ (fun x' => gradY 1 f g x' y l) x with hD
  refine ⟨ContinuousLinearMap.adjoint D, fun u => ?_⟩
  unfold hessXY gradient
  have hu : HasFDerivAt (fun x' => ⟪gradY 1 f g x' y l, u⟫_ℝ) ((innerSL ℝ u).comp D) x := by
    have := (innerSL ℝ u).hasFDerivAt.comp x hGd.hasFDerivAt
    have hfun' : (fun x' => ⟪gradY 1 f g x' y l, u⟫_ℝ) =
        (innerSL ℝ u) ∘ (fun x' => gradY 1 f g x' y l) := by
      funext x'
      simp [real_inner_comm]
    rw [hfun']
    exact this
  rw [hu.fderiv]
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.adjoint_inner_left]
  simp

/-- Exact penalization under the local error bound (Clarke). -/
lemma penalty (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2))
    (xbar : E n) (ybar : E m) (lambar : Fin q → ℝ) (ξ : E n) (ε : ℝ) (hε : 0 < ε)
    (hmin : IsLocalMinOn
      (fun z : E n × E m × (Fin q → ℝ) =>
        Lag 1 f g z.1 z.2.1 z.2.2 - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖)
      (Sys311 f g) (xbar, ybar, lambar))
    (hCQ : LocalErrorBound311 f g (xbar, ybar, lambar)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ z in 𝓝 ((xbar, ybar, lambar) : E n × E m × (Fin q → ℝ)),
      Phi f g (xbar, ybar, lambar) ≤
        Phi f g z - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖ +
          c * (‖hfun f g z‖ + ∑ i, max (-(z.2.2 i)) 0) := by
  obtain ⟨hz0, κ, hκ, hEB⟩ := hCQ
  set zb : E n × E m × (Fin q → ℝ) := (xbar, ybar, lambar) with hzb
  set φ : E n × E m × (Fin q → ℝ) → ℝ :=
    fun z => Phi f g z - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖ with hφ
  have hSc : IsClosed (Sys311 f g) := by
    have e : Sys311 f g = {z | hfun f g z = 0} ∩ ⋂ i, {z : E n × E m × (Fin q → ℝ) | 0 ≤ z.2.2 i} := by
      ext z; simp [Sys311, hfun]
    rw [e]
    exact (isClosed_eq (hfun_differentiable hf hg).continuous continuous_const).inter
      (isClosed_iInter fun i => isClosed_le continuous_const
        ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))
  obtain ⟨K, t, ht, hLip⟩ := ((Phi_contDiff hf hg).contDiffAt (x := zb)).of_le
    (by norm_num) |>.exists_lipschitzOnWith
  obtain ⟨ρ2, hρ2, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hmin' : ∀ᶠ z in 𝓝 zb, z ∈ Sys311 f g → φ zb ≤ φ z := eventually_nhdsWithin_iff.mp hmin
  obtain ⟨ρ1, hρ1, hm1⟩ := Metric.eventually_nhds_iff.mp hmin'
  obtain ⟨ρ3, hρ3, hm3⟩ := Metric.eventually_nhds_iff.mp hEB
  set L : ℝ := (K : ℝ) + ‖ξ‖ + ε with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨L * κ, mul_nonneg hL0 hκ.le, ?_⟩
  rw [Metric.eventually_nhds_iff]
  refine ⟨min (min (ρ1 / 2) (ρ2 / 2)) ρ3, by positivity, fun z hz => ?_⟩
  have hz1 : dist z zb < ρ1 / 2 := lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_left _ _))
  have hz2 : dist z zb < ρ2 / 2 := lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _))
  have hz3 : dist z zb < ρ3 := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨s, hsS, hs⟩ := hSc.exists_infDist_eq_dist ⟨zb, hz0⟩ z
  have hd : Metric.infDist z (Sys311 f g) ≤ dist z zb := Metric.infDist_le_dist_of_mem hz0
  have hsz : dist s zb < ρ1 ∧ dist s zb < ρ2 := by
    have := dist_triangle s z zb
    rw [dist_comm s z, ← hs] at this
    constructor <;> linarith
  have hφs : φ zb ≤ φ s := hm1 hsz.1 hsS
  have hzt : z ∈ t := hball (by rw [Metric.mem_ball]; linarith)
  have hst : s ∈ t := hball (by rw [Metric.mem_ball]; exact hsz.2)
  have hLz := hLip.dist_le_mul z hzt s hst
  rw [Real.dist_eq] at hLz
  have hEBz := hm3 hz3
  have hfst : ‖z.1 - s.1‖ ≤ dist z s := by
    rw [dist_eq_norm]
    exact norm_fst_le (z - s)
  have hin : ⟪ξ, z.1 - xbar⟫_ℝ - ⟪ξ, s.1 - xbar⟫_ℝ ≤ ‖ξ‖ * dist z s := by
    rw [← inner_sub_right]
    have : z.1 - xbar - (s.1 - xbar) = z.1 - s.1 := by abel
    rw [this]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hfst (norm_nonneg _))
  have hnorm : ‖s.1 - xbar‖ - ‖z.1 - xbar‖ ≤ dist z s := by
    have := norm_sub_norm_le (s.1 - xbar) (z.1 - xbar)
    have e : s.1 - xbar - (z.1 - xbar) = -(z.1 - s.1) := by abel
    rw [e, norm_neg] at this
    linarith
  have habs := le_abs_self (Phi f g s - Phi f g z)
  rw [abs_sub_comm] at habs
  have hφφ : φ s - φ z ≤ L * dist z s := by
    simp only [hφ, hL]
    nlinarith [hLz, hin, hnorm, habs, hε.le]
  have hzs : dist z s = Metric.infDist z (Sys311 f g) := hs.symm
  have hfinal : φ zb ≤ φ z + L * (κ * (‖gradY 1 f g z.1 z.2.1 z.2.2‖ +
      ∑ i, max (-(z.2.2 i)) 0)) := by
    have := mul_le_mul_of_nonneg_left hEBz hL0
    rw [← hzs] at this
    linarith
  have hφzb : φ zb = Phi f g zb := by simp [hφ, hzb]
  rw [hφzb] at hfinal
  simp only [hφ] at hfinal
  simp only [hfun]
  linarith [hfinal]

lemma directional (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2))
    (xbar : E n) (ybar : E m) (lambar : Fin q → ℝ) (ξ : E n) (ε c : ℝ)
    (hlam0 : ∀ i, 0 ≤ lambar i) (hh0 : hfun f g (xbar, ybar, lambar) = 0)
    (hpen : ∀ᶠ z in 𝓝 ((xbar, ybar, lambar) : E n × E m × (Fin q → ℝ)),
      Phi f g (xbar, ybar, lambar) ≤
        Phi f g z - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖ +
          c * (‖hfun f g z‖ + ∑ i, max (-(z.2.2 i)) 0))
    (dz : E n × E m × (Fin q → ℝ)) :
    0 ≤ fderiv ℝ (Phi f g) (xbar, ybar, lambar) dz - ⟪ξ, dz.1⟫_ℝ + ε * ‖dz.1‖ +
      c * (‖fderiv ℝ (hfun f g) (xbar, ybar, lambar) dz‖ +
        ∑ i, (if lambar i = 0 then max (-(dz.2.2 i)) 0 else 0)) := by
  set zb : E n × E m × (Fin q → ℝ) := (xbar, ybar, lambar) with hzb
  let line : ℝ → E n × E m × (Fin q → ℝ) := fun t => zb + t • dz
  have hline : HasDerivAt line dz 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const dz).const_add zb
    rw [one_smul] at h
    exact h
  have hline0 : line 0 = zb := by simp [line]
  have hP : HasDerivAt (Phi f g ∘ line) (fderiv ℝ (Phi f g) zb dz) 0 :=
    (((Phi_contDiff hf hg).differentiable (by norm_num)) zb).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hline hline0.symm
  have hH : HasDerivAt (hfun f g ∘ line) (fderiv ℝ (hfun f g) zb dz) 0 :=
    ((hfun_differentiable hf hg) zb).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hline0.symm
  have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => Set.mem_compl_singleton_iff.mpr (ne_of_gt ht))
  have T1 := (hasDerivAt_iff_tendsto_slope_zero.mp hP).mono_left hmono
  have T2 := ((hasDerivAt_iff_tendsto_slope_zero.mp hH).mono_left hmono).norm
  have T3 : ∀ i, Tendsto (fun t : ℝ => t⁻¹ * max (-(lambar i + t * dz.2.2 i)) 0) (𝓝[>] 0)
      (𝓝 (if lambar i = 0 then max (-(dz.2.2 i)) 0 else 0)) := by
    intro i
    split_ifs with h0
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [h0, zero_add, show -(t * dz.2.2 i) = t * (-(dz.2.2 i)) by ring,
        show (0 : ℝ) = t * 0 by ring, ← mul_max_of_nonneg _ _ ht'.le, ← mul_assoc,
        inv_mul_cancel₀ ht'.ne', one_mul, mul_zero]
    · have hpos : 0 < lambar i := lt_of_le_of_ne (hlam0 i) (Ne.symm h0)
      apply tendsto_const_nhds.congr'
      have hc : Continuous (fun t : ℝ => lambar i + t * dz.2.2 i) := by fun_prop
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < lambar i + t * dz.2.2 i := by
        have := hc.tendsto 0
        simp only [zero_mul, add_zero] at this
        exact this (Ioi_mem_nhds hpos)
      filter_upwards [nhdsWithin_le_nhds hev] with t ht
      rw [max_eq_right (by linarith), mul_zero]
  have hT := ((T1.sub (tendsto_const_nhds (x := ⟪ξ, dz.1⟫_ℝ))).add
    (tendsto_const_nhds (x := ε * ‖dz.1‖))).add
    ((tendsto_const_nhds (x := c)).mul (T2.add (tendsto_finset_sum Finset.univ fun i _ => T3 i)))
  apply ge_of_tendsto hT
  have hlc : Tendsto line (𝓝 0) (𝓝 zb) := by
    have := hline.continuousAt.tendsto
    rwa [hline0] at this
  filter_upwards [nhdsWithin_le_nhds (hlc.eventually hpen), self_mem_nhdsWithin] with t ht htpos
  have ht' : (0 : ℝ) < t := htpos
  simp only [Function.comp_apply, zero_add, hline0, hh0, sub_zero, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos ht']
  have e1 : (line t).1 - xbar = t • dz.1 := by simp [line, hzb]
  have e2 : ∀ i, (line t).2.2 i = lambar i + t * dz.2.2 i := by intro i; simp [line, hzb]
  rw [e1, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht'] at ht
  simp only [e2] at ht
  have key : 0 ≤ t * (t⁻¹ * (Phi f g (line t) - Phi f g zb) - ⟪ξ, dz.1⟫_ℝ + ε * ‖dz.1‖ +
      c * (t⁻¹ * ‖hfun f g (line t)‖ + ∑ i, t⁻¹ * max (-(lambar i + t * dz.2.2 i)) 0)) := by
    rw [← Finset.mul_sum]
    have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht'.ne'
    have : t * (t⁻¹ * (Phi f g (line t) - Phi f g zb) - ⟪ξ, dz.1⟫_ℝ + ε * ‖dz.1‖ +
        c * (t⁻¹ * ‖hfun f g (line t)‖ + t⁻¹ * ∑ i, max (-(lambar i + t * dz.2.2 i)) 0)) =
        (t * t⁻¹) * (Phi f g (line t) - Phi f g zb) - t * ⟪ξ, dz.1⟫_ℝ + ε * (t * ‖dz.1‖) +
        c * ((t * t⁻¹) * ‖hfun f g (line t)‖ + (t * t⁻¹) * ∑ i, max (-(lambar i + t * dz.2.2 i)) 0) := by
      ring
    rw [this, h1]
    linarith
  exact (mul_nonneg_iff_of_pos_left ht').mp key

end MaxValSens.Wolfe.KKTAux

open MaxValSens.Wolfe MaxValSens.Wolfe.KKTAux

theorem solution {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (xbar : E n) (ybar : E m) (lambar : Fin q → ℝ) (ξ : E n) (ε : ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (hε : 0 < ε)
    (hmin : IsLocalMinOn
      (fun z : E n × E m × (Fin q → ℝ) =>
        Lag 1 f g z.1 z.2.1 z.2.2 - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖)
      (Sys311 f g) (xbar, ybar, lambar))
    (hCQ : LocalErrorBound311 f g (xbar, ybar, lambar)) :
    ∃ u ∈ Xi 1 f g xbar ybar lambar,
      ‖ξ - (gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u)‖ ≤ ε := by
  have hz0 := hCQ.1
  have hh0 : hfun f g (xbar, ybar, lambar) = 0 := hz0.1
  have hlam0 : ∀ i, 0 ≤ lambar i := hz0.2
  obtain ⟨c, hc0, hpen⟩ := penalty hf hg xbar ybar lambar ξ ε hε hmin hCQ
  have hσ := directional hf hg xbar ybar lambar ξ ε c hlam0 hh0 hpen
  obtain ⟨T, hT⟩ := hessXY_clm hf hg xbar ybar lambar
  set H : E m →L[ℝ] E m := fderiv ℝ (fun y' => gradY 1 f g xbar y' lambar) ybar with hH
  have hHe : ∀ μ, hessYY f g xbar ybar lambar μ = H μ := fun μ => rfl
  set Dg : Fin q → E m →L[ℝ] ℝ := fun i => fderiv ℝ (g i xbar) ybar with hDgdef
  have hDg : ∀ i μ, dgY g i xbar ybar μ = Dg i μ := fun i μ => rfl
  let k0 : E n × E m × (Fin q → ℝ) :=
    (gradX f g xbar ybar lambar - ξ, 0, fun i => -g i xbar ybar)
  let p1 : (E n × E m × (Fin q → ℝ)) →L[ℝ] E n := ContinuousLinearMap.fst ℝ (E n) (E m × (Fin q → ℝ))
  let p2 : (E n × E m × (Fin q → ℝ)) →L[ℝ] E m :=
    (ContinuousLinearMap.fst ℝ (E m) (Fin q → ℝ)).comp (ContinuousLinearMap.snd ℝ (E n) _)
  let p3 : (E n × E m × (Fin q → ℝ)) →L[ℝ] (Fin q → ℝ) :=
    (ContinuousLinearMap.snd ℝ (E m) (Fin q → ℝ)).comp (ContinuousLinearMap.snd ℝ (E n) _)
  let Lk : (E n × E m × (Fin q → ℝ)) →L[ℝ] (E n × E m × (Fin q → ℝ)) :=
    (ε • p1 + (c • T).comp p2).prod (((c • H).comp p2).prod
      (ContinuousLinearMap.pi fun i => (-c) • ((Dg i).comp p2) +
        (-c) • ((ContinuousLinearMap.proj i).comp p3)))
  have hk1 : ∀ p : E n × E m × (Fin q → ℝ),
      (k0 + Lk p).1 = gradX f g xbar ybar lambar - ξ + ε • p.1 + c • T p.2.1 := by
    intro p; simp [k0, Lk, p1, p2]; abel
  have hk2 : ∀ p : E n × E m × (Fin q → ℝ), (k0 + Lk p).2.1 = c • H p.2.1 := by
    intro p; simp [k0, Lk, p2]
  have hk3 : ∀ (p : E n × E m × (Fin q → ℝ)) i,
      (k0 + Lk p).2.2 i = -g i xbar ybar - c * Dg i p.2.1 - c * p.2.2 i := by
    intro p i; simp [k0, Lk, p2, p3]; ring
  let Nset : Set (Fin q → ℝ) := {ν | ∀ i, 0 ≤ ν i ∧ ν i ≤ 1 ∧ lambar i * ν i = 0}
  have hNconv : Convex ℝ Nset := by
    intro a ha b hb s t hs ht hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨a1, a2, a3⟩ := ha i
    obtain ⟨b1, b2, b3⟩ := hb i
    refine ⟨by positivity, by nlinarith, by linear_combination s * a3 + t * b3⟩
  have hNcl : IsClosed Nset := by
    have e : Nset = ⋂ i, ({ν : Fin q → ℝ | 0 ≤ ν i} ∩ ({ν | ν i ≤ 1} ∩ {ν | lambar i * ν i = 0})) := by
      ext ν; simp [Nset, Set.mem_iInter]
    rw [e]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (continuous_apply i)).inter
      ((isClosed_le (continuous_apply i) continuous_const).inter
        (isClosed_eq (continuous_const.mul (continuous_apply i)) continuous_const))
  have hNcomp : IsCompact Nset := by
    apply Metric.isCompact_of_isClosed_isBounded hNcl
    apply (Metric.isBounded_closedBall (x := (0 : Fin q → ℝ)) (r := 1)).subset
    intro ν hν
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨a1, a2, -⟩ := hν i
    constructor <;> linarith
  let Pset : Set (E n × E m × (Fin q → ℝ)) :=
    Metric.closedBall 0 1 ×ˢ (Metric.closedBall 0 1 ×ˢ Nset)
  have hPconv : Convex ℝ Pset := (convex_closedBall 0 1).prod ((convex_closedBall 0 1).prod hNconv)
  have hPcomp : IsCompact Pset :=
    (isCompact_closedBall 0 1).prod ((isCompact_closedBall 0 1).prod hNcomp)
  let K : Set (E n × E m × (Fin q → ℝ)) := (fun w => k0 + w) '' (Lk '' Pset)
  have hKconv : Convex ℝ K := (hPconv.linear_image Lk.toLinearMap).translate k0
  have hKcomp : IsCompact K := (hPcomp.image Lk.continuous).image (continuous_const.add continuous_id)
  have claim : ∃ p ∈ Pset, k0 + Lk p = 0 := by
    by_contra hno
    push_neg at hno
    have h0K : (0 : E n × E m × (Fin q → ℝ)) ∉ K := by
      rintro ⟨w, ⟨p, hp, rfl⟩, h⟩
      exact hno p hp h
    obtain ⟨φ, u, v, hφK, huv, hφ0⟩ := geometric_hahn_banach_compact_closed hKconv hKcomp
      (convex_singleton 0) isClosed_singleton (Set.disjoint_singleton_right.mpr h0K)
    have hv0 : v < 0 := by simpa using hφ0 0 rfl
    let dx : E n := (InnerProductSpace.toDual ℝ (E n)).symm (φ.comp (Jx n m q))
    let dy : E m := (InnerProductSpace.toDual ℝ (E m)).symm (φ.comp (Jy n m q))
    let dl : Fin q → ℝ := fun i => φ (Jl n m q (fun j => if i = j then 1 else 0))
    have hpair : ∀ a : E n × E m × (Fin q → ℝ),
        φ a = ⟪dx, a.1⟫_ℝ + ⟪dy, a.2.1⟫_ℝ + ∑ i, dl i * a.2.2 i := by
      intro a
      conv_lhs => rw [decomp a]
      rw [map_add, map_add]
      simp only [dx, dy, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply]
      congr 1
      have := (φ.comp (Jl n m q)).toLinearMap.pi_apply_eq_sum_univ a.2.2
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, smul_eq_mul] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    let dz : E n × E m × (Fin q → ℝ) := (dx, dy, dl)
    have hs := hσ dz
    set w := fderiv ℝ (hfun f g) (xbar, ybar, lambar) dz with hw
    let bst : E n := ‖dx‖⁻¹ • dx
    let μst : E m := ‖w‖⁻¹ • w
    let νst : Fin q → ℝ := fun i => if lambar i = 0 ∧ dl i < 0 then 1 else 0
    have hnorm1 : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (a : X), ‖‖a‖⁻¹ • a‖ ≤ 1 := by
      intro X _ _ a
      rw [norm_smul, norm_inv, norm_norm]
      rcases eq_or_ne ‖a‖ 0 with h | h
      · simp [h]
      · rw [inv_mul_cancel₀ h]
    have hpst : ((bst, μst, νst) : E n × E m × (Fin q → ℝ)) ∈ Pset := by
      refine ⟨mem_closedBall_zero_iff.mpr (hnorm1 dx), mem_closedBall_zero_iff.mpr (hnorm1 w),
        fun i => ?_⟩
      simp only [νst]
      split_ifs with h
      · exact ⟨zero_le_one, le_rfl, by rw [h.1]; ring⟩
      · exact ⟨le_rfl, zero_le_one, by ring⟩
    have hb : ⟪dx, bst⟫_ℝ = ‖dx‖ := by
      simp only [bst, inner_smul_right, real_inner_self_eq_norm_sq]
      rcases eq_or_ne ‖dx‖ 0 with h | h
      · simp [h]
      · field_simp
    have hμ : ⟪w, μst⟫_ℝ = ‖w‖ := by
      simp only [μst, inner_smul_right, real_inner_self_eq_norm_sq]
      rcases eq_or_ne ‖w‖ 0 with h | h
      · simp [h]
      · field_simp
    have hν : ∀ i, -(dl i * νst i) = (if lambar i = 0 then max (-(dz.2.2 i)) 0 else 0) := by
      intro i
      show -(dl i * νst i) = (if lambar i = 0 then max (-(dl i)) 0 else 0)
      by_cases h0 : lambar i = 0
      · rw [if_pos h0]
        by_cases hd : dl i < 0
        · rw [show νst i = 1 from if_pos ⟨h0, hd⟩, max_eq_left (by linarith)]; ring
        · rw [show νst i = 0 from if_neg (fun h => hd h.2), max_eq_right (by linarith)]; ring
      · rw [if_neg h0, show νst i = 0 from if_neg (fun h => h0 h.1)]; ring
    have hF1 := F1 hf hg xbar ybar lambar dz
    have hF2 := F2 hf hg xbar ybar lambar μst dz
    rw [hh0, inner_zero_left, ← hw, hμ, hT, hHe] at *
    have hval : φ (k0 + Lk (bst, μst, νst)) = ⟪dx, gradX f g xbar ybar lambar⟫_ℝ - ⟪dx, ξ⟫_ℝ +
        ε * ‖dx‖ + c * (⟪dx, T μst⟫_ℝ + ⟪dy, H μst⟫_ℝ) +
        ∑ i, dl i * (-g i xbar ybar - c * Dg i μst - c * νst i) := by
      have hb2 : ‖dx‖⁻¹ * ‖dx‖ ^ 2 = ‖dx‖ := by
        rcases eq_or_ne ‖dx‖ 0 with h | h
        · simp [h]
        · field_simp
      rw [hpair, hk1, hk2]
      simp only [hk3, inner_add_right, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq, bst]
      rw [hb2]
      ring
    have eS : ∑ i, dl i * (-g i xbar ybar - c * Dg i μst - c * νst i) =
        -(∑ i, dz.2.2 i * g i xbar ybar) - c * ∑ i, dz.2.2 i * dgY g i xbar ybar μst +
          c * ∑ i, (if lambar i = 0 then max (-(dz.2.2 i)) 0 else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hν i]
      simp only [dz, hDg]
      ring
    have hlt : φ (k0 + Lk (bst, μst, νst)) < u :=
      hφK _ ⟨Lk (bst, μst, νst), ⟨_, hpst, rfl⟩, rfl⟩
    have e1 : ⟪dx, gradX f g xbar ybar lambar⟫_ℝ = ⟪gradX f g xbar ybar lambar, dz.1⟫_ℝ :=
      real_inner_comm _ _
    have e2 : ⟪dx, ξ⟫_ℝ = ⟪ξ, dz.1⟫_ℝ := real_inner_comm _ _
    have e3 : ⟪dx, T μst⟫_ℝ = ⟪T μst, dz.1⟫_ℝ := real_inner_comm _ _
    have e4 : ⟪dy, H μst⟫_ℝ = ⟪H μst, dz.2.1⟫_ℝ := real_inner_comm _ _
    have e5 : ‖dx‖ = ‖dz.1‖ := rfl
    rw [hval, eS, e1, e2, e3, e4, e5] at hlt
    rw [hF1] at hs
    have hcw : c * ‖w‖ = c * (⟪T μst, dz.1⟫_ℝ + ⟪H μst, dz.2.1⟫_ℝ -
        ∑ i, dz.2.2 i * dgY g i xbar ybar μst) := by rw [← hF2]
    nlinarith [hcw]
  obtain ⟨⟨b, μ, ν⟩, ⟨hb, hμ, hν⟩, hk⟩ := claim
  have hk1' : gradX f g xbar ybar lambar - ξ + ε • b + c • T μ = 0 := by
    rw [← hk1 (b, μ, ν), hk]; rfl
  have hk2' : c • H μ = 0 := by rw [← hk2 (b, μ, ν), hk]; rfl
  have hk3' : ∀ i, -g i xbar ybar - c * Dg i μ - c * ν i = 0 := by
    intro i; rw [← hk3 (b, μ, ν) i, hk]; rfl
  refine ⟨c • μ, ⟨?_, fun i => ?_⟩, ?_⟩
  · rw [hHe, map_smul]; exact hk2'
  · rw [hDg, map_smul, smul_eq_mul]
    obtain ⟨n1, -, n3⟩ := hν i
    have := hk3' i
    refine ⟨hlam0 i, ?_, ?_⟩
    · nlinarith [mul_nonneg hc0 n1]
    · have e : -(c * Dg i μ) - 1 * g i xbar ybar = c * ν i := by linarith
      rw [e]; linear_combination c * n3
  · rw [hT, map_smul]
    have e : ξ - (gradX f g xbar ybar lambar + c • T μ) =
        ε • b - (gradX f g xbar ybar lambar - ξ + ε • b + c • T μ) := by abel
    rw [e, hk1', sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have := mem_closedBall_zero_iff.mp hb
    nlinarith [norm_nonneg b]
