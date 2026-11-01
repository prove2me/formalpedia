-- Prove2me | solution 1 for MaxValSens.Wolfe.theorem_3_3_multiplier_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:13:32.464654+00:00
-- url     : https://prove2.me/submissions/d74fa0f1-3616-4602-9558-374d8ebb01ed

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

open MaxValSens.Wolfe

private lemma gradYpart_eq {n m : ℕ} (F : E n × E m → ℝ) (hF : ContDiff ℝ 2 F)
    (x : E n) (y : E m) :
    gradient (fun y' => F (x, y')) y = (InnerProductSpace.toDual ℝ (E m)).symm
      ((fderiv ℝ F (x, y)).comp (ContinuousLinearMap.inr ℝ (E n) (E m))) := by
  unfold gradient
  congr 1
  have hd : DifferentiableAt ℝ F (x, y) := (hF.differentiable (by norm_num)).differentiableAt
  exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)).fderiv

private lemma gradYpart_cont {n m : ℕ} (F : E n × E m → ℝ) (hF : ContDiff ℝ 2 F) :
    Continuous (fun p : E n × E m => gradient (fun y' => F (p.1, y')) p.2) := by
  have : (fun p : E n × E m => gradient (fun y' => F (p.1, y')) p.2) =
      fun p => (InnerProductSpace.toDual ℝ (E m)).symm
        ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ (E n) (E m))) := by
    funext p
    exact gradYpart_eq F hF p.1 p.2
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E m)).symm.continuous.comp
    ((hF.continuous_fderiv (by norm_num)).clm_comp continuous_const)

private lemma gradY_eq {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
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

theorem solution {n m q : ℕ} (f : E n → E m → ℝ)
    (g : Fin q → E n → E m → ℝ) (xbar : E n) (ytil : E m)
    (hS : Standing f g xbar) (hytil : ytil ∈ S f g xbar) (hPCQ : StableParamCQ f g xbar ytil)
    (xs : ℕ → E n) (ys : ℕ → E m) (hx : Tendsto xs atTop (𝓝 xbar))
    (hy : Tendsto ys atTop (𝓝 ytil)) (hys : ∀ k, ys k ∈ S f g (xs k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ lams : ℕ → Fin q → ℝ,
      (∀ k, lams k ∈ SigmaM 1 f g (xs (φ k)) (ys (φ k))) ∧
      ∃ lamtil ∈ SigmaM 1 f g xbar ytil, Tendsto lams atTop (𝓝 lamtil) := by
  have hpair : Tendsto (fun k => (xs k, ys k)) atTop (𝓝 (xbar, ytil)) := hx.prodMk_nhds hy
  -- each `ys k` is a global, hence local, maximizer of `f (xs k)` on the feasible set
  have hloc : ∀ k, IsLocalMaxOn (f (xs k)) (feas g (xs k)) (ys k) := by
    intro k
    apply IsMaxOn.localize
    intro y hy'
    show f (xs k) y ≤ f (xs k) (ys k)
    have h1 : ((f (xs k) y : ℝ) : EReal) ≤ V f g (xs k) := by
      unfold V
      exact le_iSup₂ (f := fun y (_ : y ∈ feas g (xs k)) => ((f (xs k) y : ℝ) : EReal)) y hy'
    rw [← (hys k).2] at h1
    exact EReal.coe_le_coe_iff.mp h1
  obtain ⟨N, hN⟩ := (hpair.eventually hPCQ.1).exists_forall_of_atTop
  have hne : ∀ k, (Mpar g (gradient (f (xs (k + N))) (ys (k + N))) (xs (k + N))
      (ys (k + N))).Nonempty := fun k =>
    hN (k + N) (by omega) (hys (k + N)).1 (hloc (k + N))
  have hGc := gradYpart_cont (fun p : E n × E m => f p.1 p.2) hS.1
  have hβ : Tendsto (fun k => gradient (f (xs (k + N))) (ys (k + N))) atTop
      (𝓝 (gradient (f xbar) ytil)) := by
    have := (hGc.tendsto (xbar, ytil)).comp ((tendsto_add_atTop_iff_nat N).mpr hpair)
    exact this
  obtain ⟨lams, hlams, φ, hφ, lim, hlim, hconv⟩ :=
    hPCQ.2 (fun k => gradient (f (xs (k + N))) (ys (k + N))) (fun k => xs (k + N))
      (fun k => ys (k + N)) (gradient (f xbar) ytil) hβ
      ((tendsto_add_atTop_iff_nat N).mpr hx) ((tendsto_add_atTop_iff_nat N).mpr hy) hne
  have toSigma : ∀ (x : E n) (y : E m) (l : Fin q → ℝ),
      l ∈ Mpar g (gradient (f x) y) x y → l ∈ SigmaM 1 f g x y := by
    intro x y l hl
    refine ⟨?_, hl.2⟩
    rw [gradY_eq f g hS.1 hS.2.1, hl.1, sub_self]
  refine ⟨fun k => φ k + N, fun a b hab => by simpa using hφ hab, lams ∘ φ,
    fun k => toSigma _ _ _ (hlams (φ k)), lim, toSigma _ _ _ hlim, hconv⟩
