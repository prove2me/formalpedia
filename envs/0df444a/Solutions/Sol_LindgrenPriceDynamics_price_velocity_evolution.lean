-- Prove2me | solution 1 for LindgrenPriceDynamics.price_velocity_evolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:13:38.729735+00:00
-- url     : https://prove2.me/submissions/00d18a0b-3357-4093-9f9b-7e85596c7dd9

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

open LindgrenPriceDynamics in
theorem solution {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 2 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ t p, timePartial J t p =
      dot (priceGrad (J t) p) (priceGrad (J t) p) / (2 * m) - aggregateExpenditure lam e p) :
    ∀ t p i,
      m * timePartial (fun τ q => optimalVelocity m J τ q i) t p
        + (1 / 2) * m * pricePartial
            (fun q => dot (optimalVelocity m J t q) (optimalVelocity m J t q)) p i
        = pricePartial (aggregateExpenditure lam e) p i := by
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
  -- E is forced by the HJB
  have hEfun : aggregateExpenditure lam e = fun q => G q / (2 * m) - D (t, q) e0 := by
    funext q
    have := hHJB t q
    rw [hTP] at this
    simp only [hG]
    linarith
  have hL : HasFDerivAt (fun q => D (t, q) e0) (((D2 (t, p)).flip e0).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ))) p :=
    (hDw (t, p) e0).comp p (hinr t p)
  have hR : HasFDerivAt (fun q => G q / (2 * m) - D (t, q) e0)
      ((1 / (2 * m)) • G' - ((D2 (t, p)).flip e0).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin l → ℝ))) p := by
    have := (hGh.const_mul (1 / (2 * m))).sub hL
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]
    ring
  have hEi : pricePartial (aggregateExpenditure lam e) p i
      = (1 / (2 * m)) * G' (Pi.single i 1) - D2 (t, p) ei e0 := by
    unfold pricePartial
    rw [hEfun, hR.fderiv]
    simp [ei]
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
  rw [hT1, hT2, hsym, hEi]
  field_simp
  ring
