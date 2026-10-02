-- Prove2me | solution 1 for LindgrenPriceDynamics.price_velocity_hicksian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:57:43.405824+00:00
-- url     : https://prove2.me/submissions/1abd8a7f-7f8f-40bd-8b6f-1cdec4a09372

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

open LindgrenPriceDynamics in
theorem solution {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (he : ∀ j, Differentiable ℝ (e j))
    (h : Fin n → (Fin l → ℝ) → Fin l → ℝ)
    (hShephard : ∀ j p i, h j p i = pricePartial (e j) p i)
    (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 2 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ t p, timePartial J t p =
      dot (priceGrad (J t) p) (priceGrad (J t) p) / (2 * m) - aggregateExpenditure lam e p) :
    ∀ t p i,
      m * timePartial (fun τ q => optimalVelocity m J τ q i) t p
        + (1 / 2) * m * pricePartial
            (fun q => dot (optimalVelocity m J t q) (optimalVelocity m J t q)) p i
        = ∑ j, lam j * h j p i := by
  intro t p i
  have hm0 : m ≠ 0 := ne_of_gt hm
  set F : ℝ × (Fin l → ℝ) → ℝ := fun x => J x.1 x.2 with hF
  set D := fderiv ℝ F with hDdef
  set D2 := fderiv ℝ D with hD2def
  have hFd : Differentiable ℝ F := hJ.differentiable (by norm_num)
  have hDc : ContDiff ℝ 1 D := hJ.fderiv_right (m := 1) (by norm_num)
  have hDd : Differentiable ℝ D := hDc.differentiable (by norm_num)
  have hFD : ∀ x, HasFDerivAt F (D x) x := fun x => (hFd x).hasFDerivAt
  have hDD : ∀ x, HasFDerivAt D (D2 x) x := fun x => (hDd x).hasFDerivAt
  -- derivative of y ↦ D y w
  have hDw : ∀ x (w : ℝ × (Fin l → ℝ)),
      HasFDerivAt (fun y => D y w) ((D2 x).flip w) x := by
    intro x w
    have := (hDD x).clm_apply (hasFDerivAt_const w x)
    simpa using this
  have hinr : ∀ (τ : ℝ) (q : Fin l → ℝ), HasFDerivAt (fun q : Fin l → ℝ => (τ, q))
      (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ)) q := fun τ q =>
    (hasFDerivAt_const τ q).prodMk (hasFDerivAt_id q)
  have hinl : ∀ (τ : ℝ) (q : Fin l → ℝ), HasDerivAt (fun τ : ℝ => (τ, q))
      ((1 : ℝ), (0 : Fin l → ℝ)) τ := fun τ q =>
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ q)
  -- price partials of J via D
  have hPP : ∀ τ q k, pricePartial (J τ) q k = D (τ, q) ((0 : ℝ), Pi.single k 1) := by
    intro τ q k
    have hq : HasFDerivAt (J τ) ((D (τ, q)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ))) q :=
      (hFD (τ, q)).comp q (hinr τ q)
    unfold pricePartial
    rw [hq.fderiv]
    simp
  -- time partials of J via D
  have hTP : ∀ τ q, timePartial J τ q = D (τ, q) ((1 : ℝ), (0 : Fin l → ℝ)) := by
    intro τ q
    have ht := (hFD (τ, q)).comp_hasDerivAt τ (hinl τ q)
    exact ht.deriv
  set ei : ℝ × (Fin l → ℝ) := ((0 : ℝ), Pi.single i 1) with hei
  set e0 : ℝ × (Fin l → ℝ) := ((1 : ℝ), (0 : Fin l → ℝ)) with he0
  -- term 1
  have hT1 : timePartial (fun τ q => optimalVelocity m J τ q i) t p
      = -(1 / m) * D2 (t, p) e0 ei := by
    unfold timePartial
    have hfun : (fun τ => optimalVelocity m J τ p i) = fun τ => -(1 / m) * D (τ, p) ei := by
      funext τ; simp only [optimalVelocity]; rw [hPP]
    rw [hfun]
    have h1' := (hDw (t, p) ei).comp_hasDerivAt t (hinl t p)
    have h1 : HasDerivAt (fun τ => D (τ, p) ei) ((D2 (t, p)).flip ei e0) t := h1'
    rw [(h1.const_mul (-(1 / m))).deriv]
    simp
  -- G
  set G : (Fin l → ℝ) → ℝ := fun q => dot (priceGrad (J t) q) (priceGrad (J t) q) with hG
  have hGd : DifferentiableAt ℝ G p := by
    have hGeq : G = fun q => ∑ k, D (t, q) ((0 : ℝ), Pi.single k 1) * D (t, q) ((0 : ℝ), Pi.single k 1) := by
      funext q; simp only [hG, dot, priceGrad, hPP]
    rw [hGeq]
    have hk : ∀ k : Fin l, DifferentiableAt ℝ (fun q => D (t, q) ((0 : ℝ), Pi.single k 1)) p :=
      fun k => ((hDw (t, p) _).comp p (hinr t p)).differentiableAt
    exact DifferentiableAt.fun_sum (fun k _ => (hk k).mul (hk k))
  set G' := fderiv ℝ G p with hG'
  have hGh : HasFDerivAt G G' p := hGd.hasFDerivAt
  -- E
  set E : (Fin l → ℝ) → ℝ := aggregateExpenditure lam e with hE
  have hEh : HasFDerivAt E (∑ j, lam j • fderiv ℝ (e j) p) p := by
    have : E = fun q => ∑ j, lam j * e j q := by
      funext q; simp [hE, aggregateExpenditure]
    rw [this]
    have := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((he j p).hasFDerivAt.const_mul (lam j)))
    simpa using this
  have hEi : (∑ j, lam j • fderiv ℝ (e j) p) (Pi.single i 1) = ∑ j, lam j * h j p i := by
    simp [hShephard, pricePartial]
  -- differentiate HJB
  have hHJBfun : (fun q => D (t, q) e0) = fun q => G q / (2 * m) - E q := by
    funext q; rw [← hTP, hHJB]
  have hL : HasFDerivAt (fun q => D (t, q) e0) (((D2 (t, p)).flip e0).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ))) p :=
    (hDw (t, p) e0).comp p (hinr t p)
  have hR : HasFDerivAt (fun q => G q / (2 * m) - E q)
      ((1 / (2 * m)) • G' - ∑ j, lam j • fderiv ℝ (e j) p) p := by
    have := (hGh.const_mul (1 / (2 * m))).sub hEh
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [hHJBfun] at hL
  have hEq := hL.unique hR
  have hEqi := congrArg (fun L => L (Pi.single i 1)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hEqi
  rw [hEi] at hEqi
  -- symmetry
  have hsym : D2 (t, p) e0 ei = D2 (t, p) ei e0 :=
    (hJ.contDiffAt.isSymmSndFDerivAt (by simp)) e0 ei
  -- term 2
  have hT2 : pricePartial (fun q => dot (optimalVelocity m J t q) (optimalVelocity m J t q)) p i
      = (1 / m ^ 2) * G' (Pi.single i 1) := by
    have hfun : (fun q => dot (optimalVelocity m J t q) (optimalVelocity m J t q))
        = fun q => (1 / m ^ 2) * G q := by
      funext q
      simp only [hG, dot, optimalVelocity, priceGrad, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      field_simp
    rw [hfun]
    unfold pricePartial
    rw [(hGh.const_mul (1 / m ^ 2)).fderiv]
    simp
  rw [hT1, hT2, hsym]
  have : D2 (t, p) ei e0 = (1 / (2 * m)) * G' (Pi.single i 1) - ∑ j, lam j * h j p i := by
    rw [← hEqi]
  rw [this]
  field_simp
  ring
