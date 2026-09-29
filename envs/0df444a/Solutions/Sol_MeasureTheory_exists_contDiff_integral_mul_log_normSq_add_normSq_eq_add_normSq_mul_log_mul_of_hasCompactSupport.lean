-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/badf08f3-91fa-5289-aad7-0cc4227157f9

import Mathlib
import Theorems.Thm_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
import Theorems.Thm_MeasureTheory_contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff Real

namespace P2mD0Complex

section ParamIntegral

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

noncomputable def dX {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : X × ℝ → F) : X × ℝ → (X →L[ℝ] F) :=
  fun p => (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ X ℝ)

theorem contDiff_dX {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : X × ℝ → F} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (dX Φ) :=
  (hΦ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem hasFDerivAt_dX {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : X × ℝ → F} (hΦ : ContDiff ℝ ∞ Φ) (x : X) (t : ℝ) :
    HasFDerivAt (fun y => Φ (y, t)) (dX Φ (x, t)) x :=
  ((hΦ.differentiable (by simp)) (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)

theorem hasFDerivAt_integral_smul {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (w : ℝ → ℝ) (a b : ℝ) (hw : IntervalIntegrable w volume a b)
    (Φ : X × ℝ → F) (hΦ : ContDiff ℝ ∞ Φ) (x₀ : X) :
    HasFDerivAt (fun x => ∫ t in a..b, w t • Φ (x, t))
      (∫ t in a..b, w t • dX Φ (x₀, t)) x₀ := by
  have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (contDiff_dX hΦ).continuous.continuousOn
  have hcontΦ : Continuous Φ := hΦ.continuous
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F' := fun x t => w t • dX Φ (x, t)) (bound := fun t => ‖w t‖ * C)
    (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      hw.def'.aestronglyMeasurable.smul
        ((hcontΦ.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
  · exact hw.smul_continuousOn (hcontΦ.comp (Continuous.prodMk_right x₀)).continuousOn
  · exact hw.def'.aestronglyMeasurable.smul
      (((contDiff_dX hΦ).continuous.comp (Continuous.prodMk_right x₀)).aestronglyMeasurable)
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hC (x, t) ⟨Metric.ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩) (norm_nonneg _)
  · exact hw.norm.mul_const C
  · exact Eventually.of_forall fun t _ x _ => (hasFDerivAt_dX hΦ x t).const_smul (w t)

theorem contDiff_integral_smul_nat (w : ℝ → ℝ) (a b : ℝ) (hw : IntervalIntegrable w volume a b) :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (Φ : X × ℝ → F), ContDiff ℝ ∞ Φ →
        ContDiff ℝ n (fun x => ∫ t in a..b, w t • Φ (x, t)) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ Φ hΦ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_integral_smul w a b hw Φ hΦ x).continuousAt
  | succ n ih =>
    intro F _ _ _ Φ hΦ
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun x => ∫ t in a..b, w t • dX Φ (x, t), ih (dX Φ) (contDiff_dX hΦ),
      fun x => hasFDerivAt_integral_smul w a b hw Φ hΦ x⟩

theorem contDiff_integral_smul {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (w : ℝ → ℝ) (a b : ℝ) (hw : IntervalIntegrable w volume a b)
    (Φ : X × ℝ → F) (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, w t • Φ (x, t)) :=
  contDiff_infty.2 fun n => contDiff_integral_smul_nat w a b hw n Φ hΦ

theorem contDiff_integral {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (a b : ℝ) (Φ : X × ℝ → F) (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, Φ (x, t)) := by
  simpa using contDiff_integral_smul (fun _ => (1 : ℝ)) a b _root_.intervalIntegrable_const Φ hΦ

end ParamIntegral

section EvenSqrt

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def Hs (E : Type u) : Set (E × ℝ) := {q : E × ℝ | 0 ≤ q.2}

noncomputable def dρ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × ℝ → F) : E × ℝ → F :=
  fun p => fderiv ℝ f p ((0 : E), (1 : ℝ))

theorem contDiff_dρ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dρ f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_parity {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (σ : ℝ)
    (hσ : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = σ • f (e, ρ)) (e : E) (ρ : ℝ) (v : E) (τ : ℝ) :
    fderiv ℝ f (e, -ρ) (v, -τ) = σ • fderiv ℝ f (e, ρ) (v, τ) := by
  let N : E × ℝ →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).prod (-(ContinuousLinearMap.snd ℝ E ℝ))
  have hNap : ∀ (e : E) (ρ : ℝ), N (e, ρ) = (e, -ρ) := fun e ρ => by simp [N]
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have h1 : HasFDerivAt (f ∘ N) ((fderiv ℝ f (e, -ρ)).comp N) (e, ρ) := by
    have := (hdiff (N (e, ρ))).hasFDerivAt
    rw [hNap] at this
    exact this.comp (e, ρ) N.hasFDerivAt
  have h2 : HasFDerivAt (f ∘ N) (σ • fderiv ℝ f (e, ρ)) (e, ρ) := by
    have hfun : (f ∘ N) = fun p => σ • f p := by
      funext p
      rcases p with ⟨e', ρ'⟩
      simp [Function.comp, hNap, hσ]
    rw [hfun]
    exact (hdiff (e, ρ)).hasFDerivAt.const_smul σ
  have h3 := h1.unique h2
  have := congrArg (fun T : E × ℝ →L[ℝ] F => T (v, τ)) h3
  simpa [hNap] using this

theorem dρ_neg_of_even {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (e : E) (ρ : ℝ) :
    dρ f (e, -ρ) = -dρ f (e, ρ) := by
  have h := fderiv_parity hf 1 (fun e ρ => by rw [hev, one_smul]) e ρ 0 (-1)
  simp only [neg_neg, one_smul] at h
  unfold dρ
  rw [h]
  have : ((0 : E), (-1 : ℝ)) = -((0 : E), (1 : ℝ)) := by simp
  rw [this, map_neg]

theorem dρ_neg_of_odd {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = -f (e, ρ)) (e : E) (ρ : ℝ) :
    dρ f (e, -ρ) = dρ f (e, ρ) := by
  have h := fderiv_parity hf (-1) (fun e ρ => by rw [hodd, neg_one_smul]) e ρ 0 (-1)
  simp only [neg_neg, neg_one_smul] at h
  unfold dρ
  rw [h]
  have : ((0 : E), (-1 : ℝ)) = -((0 : E), (1 : ℝ)) := by simp
  rw [this, map_neg, neg_neg]

theorem dX_neg_of_even {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (e : E) (ρ : ℝ) :
    dX f (e, -ρ) = dX f (e, ρ) := by
  ext v
  have h := fderiv_parity hf 1 (fun e ρ => by rw [hev, one_smul]) e ρ v 0
  simp only [neg_zero, one_smul] at h
  simpa [dX] using h

theorem zero_of_odd {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hodd : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = -f (e, ρ)) (e : E) :
    f (e, 0) = 0 := by
  have h := hodd e 0
  rw [neg_zero] at h
  have : (2 : ℝ) • f (e, 0) = 0 := by rw [two_smul]; nth_rewrite 1 [h]; simp
  simpa using this

noncomputable def hq {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × ℝ → F) : E × ℝ → F :=
  fun p => ∫ t in (0 : ℝ)..1, dρ (dρ f) (p.1, t * p.2)

theorem contDiff_hq {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (hq f) := by
  have h2 : ContDiff ℝ ∞ (dρ (dρ f)) := contDiff_dρ (contDiff_dρ hf)
  have hmap : ContDiff ℝ ∞ (fun q : (E × ℝ) × ℝ => (q.1.1, q.2 * q.1.2)) := by fun_prop
  exact contDiff_integral (X := E × ℝ) 0 1 (fun q : (E × ℝ) × ℝ => dρ (dρ f) (q.1.1, q.2 * q.1.2))
    (h2.comp hmap)

theorem hq_even {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (e : E) (ρ : ℝ) :
    hq f (e, -ρ) = hq f (e, ρ) := by
  unfold hq
  refine intervalIntegral.integral_congr fun t _ => ?_
  have h2ev : ∀ (e : E) (ρ : ℝ), dρ (dρ f) (e, -ρ) = dρ (dρ f) (e, ρ) :=
    dρ_neg_of_odd (contDiff_dρ hf) (dρ_neg_of_even hf hev)
  simp only [mul_neg]
  exact h2ev e (t * ρ)

theorem dρ_eq_smul_hq {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (e : E) (ρ : ℝ) :
    dρ f (e, ρ) = ρ • hq f (e, ρ) := by
  have h1 : ContDiff ℝ ∞ (dρ f) := contDiff_dρ hf
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => dρ f (e, u)) (dρ (dρ f) (e, u)) u := by
    intro u
    have hF := ((h1.differentiable (by simp)) (e, u)).hasFDerivAt
    have hc : HasDerivAt (fun u : ℝ => ((e, u) : E × ℝ)) ((0 : E), (1 : ℝ)) u := by
      have := (hasFDerivAt_prodMk_right (𝕜 := ℝ) e u).hasDerivAt (x := u)
      simpa using this
    exact hF.comp_hasDerivAt u hc
  have hFTC : ∫ u in (0 : ℝ)..ρ, dρ (dρ f) (e, u) = dρ f (e, ρ) - dρ f (e, 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      (((contDiff_dρ h1).continuous.comp (Continuous.prodMk_right e)).intervalIntegrable _ _)
  have h0 : dρ f (e, 0) = 0 := zero_of_odd (dρ_neg_of_even hf hev) e
  rw [h0, sub_zero] at hFTC
  rw [← hFTC]
  unfold hq
  have := intervalIntegral.smul_integral_comp_mul_right
    (f := fun u : ℝ => dρ (dρ f) (e, u)) (a := (0 : ℝ)) (b := 1) ρ
  simpa using this.symm

noncomputable def Dsqrt {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × ℝ → F) : E × ℝ → (E × ℝ →L[ℝ] F) :=
  fun p => (dX f p).comp (ContinuousLinearMap.fst ℝ E ℝ) +
    (ContinuousLinearMap.snd ℝ E ℝ).smulRight ((1 / 2 : ℝ) • hq f p)

theorem contDiff_Dsqrt {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dsqrt f) :=
  ((contDiff_dX hf).clm_comp contDiff_const).add
    (contDiff_const.smulRight (contDiff_const.smul (contDiff_hq hf)))

theorem Dsqrt_even {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (e : E) (ρ : ℝ) :
    Dsqrt f (e, -ρ) = Dsqrt f (e, ρ) := by
  simp only [Dsqrt, dX_neg_of_even hf hev, hq_even hf hev]

theorem hasFDerivAt_comp_sqrt {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (p : E × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (fun q : E × ℝ => f (q.1, √q.2)) (Dsqrt f (p.1, √p.2)) p := by
  rcases p with ⟨e, s⟩
  simp only at hp ⊢
  have hsq : HasFDerivAt (fun q : E × ℝ => √q.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 / (2 * √s))).comp
        (ContinuousLinearMap.snd ℝ E ℝ)) (e, s) :=
    (Real.hasDerivAt_sqrt hp.ne').hasFDerivAt.comp ((e, s) : E × ℝ) hasFDerivAt_snd
  have hP : HasFDerivAt (fun q : E × ℝ => ((q.1, √q.2) : E × ℝ))
      ((ContinuousLinearMap.fst ℝ E ℝ).prod
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 / (2 * √s))).comp
          (ContinuousLinearMap.snd ℝ E ℝ))) (e, s) :=
    hasFDerivAt_fst.prodMk hsq
  have hF := ((hf.differentiable (by simp)) (e, √s)).hasFDerivAt
  have hcomp := hF.comp ((e, s) : E × ℝ) hP
  refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  rcases x with ⟨v, τ⟩
  have hsplit : ((v, τ * (1 / (2 * √s))) : E × ℝ) =
      ((v, (0 : ℝ)) : E × ℝ) + (τ * (1 / (2 * √s))) • (((0 : E), (1 : ℝ)) : E × ℝ) := by
    ext <;> simp
  have hρ : fderiv ℝ f (e, √s) ((0 : E), (1 : ℝ)) = √s • hq f (e, √s) := dρ_eq_smul_hq hf hev e (√s)
  have hspos : 0 < √s := Real.sqrt_pos.2 hp
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.one_apply, smul_eq_mul, Dsqrt, dX,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.inl_apply]
  rw [hsplit, map_add, map_smul, hρ, smul_smul]
  congr 1
  rw [show τ * (1 / (2 * √s)) * √s = τ * (1 / 2) by field_simp]
  rw [mul_smul]

theorem closure_pos_eq_Hs : closure {q : E × ℝ | 0 < q.2} = Hs E := by
  have h1 : {q : E × ℝ | 0 < q.2} = Prod.snd ⁻¹' Ioi 0 := rfl
  have h2 : Hs E = Prod.snd ⁻¹' Ici 0 := rfl
  rw [h1, h2, ← isOpenMap_snd.preimage_closure_eq_closure_preimage continuous_snd, closure_Ioi]

theorem uniqueDiffOn_Hs : UniqueDiffOn ℝ (Hs E) := by
  apply uniqueDiffOn_convex
  · exact convex_halfSpace_ge (LinearMap.snd ℝ E ℝ).isLinear 0
  · have hopen : IsOpen {q : E × ℝ | 0 < q.2} := isOpen_lt continuous_const continuous_snd
    have hsub : {q : E × ℝ | 0 < q.2} ⊆ Hs E := fun q (hq : 0 < q.2) => show 0 ≤ q.2 from le_of_lt hq
    have hmem : ((0 : E), (1 : ℝ)) ∈ interior (Hs E) :=
      hopen.subset_interior_iff.2 hsub (show (0 : ℝ) < 1 by norm_num)
    exact ⟨_, hmem⟩

theorem hasFDerivWithinAt_comp_sqrt {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) (p : E × ℝ) :
    HasFDerivWithinAt (fun q : E × ℝ => f (q.1, √q.2)) (Dsqrt f (p.1, √p.2)) (Hs E) p := by
  set S : Set (E × ℝ) := {q : E × ℝ | 0 < q.2} with hS
  have hopen : IsOpen S := isOpen_lt continuous_const continuous_snd
  have hconv : Convex ℝ S := convex_halfSpace_gt (LinearMap.snd ℝ E ℝ).isLinear 0
  have hcont : Continuous (fun q : E × ℝ => f (q.1, √q.2)) :=
    hf.continuous.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))
  have hDcont : Continuous (fun q : E × ℝ => Dsqrt f (q.1, √q.2)) :=
    (contDiff_Dsqrt hf).continuous.comp
      (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))
  have hdiff : DifferentiableOn ℝ (fun q : E × ℝ => f (q.1, √q.2)) S :=
    fun q hq => (hasFDerivAt_comp_sqrt hf hev q hq).differentiableAt.differentiableWithinAt
  rw [← closure_pos_eq_Hs]
  refine hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hconv hopen
    (fun y _ => hcont.continuousWithinAt) ?_
  have hEq : ∀ y ∈ S, fderiv ℝ (fun q : E × ℝ => f (q.1, √q.2)) y = Dsqrt f (y.1, √y.2) :=
    fun y hy => (hasFDerivAt_comp_sqrt hf hev y hy).fderiv
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun y hy => (hEq y hy).symm) ?_
  exact (hDcont.tendsto p).mono_left nhdsWithin_le_nhds

theorem contDiffOn_comp_sqrt_nat :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : E × ℝ → F), ContDiff ℝ ∞ f → (∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) →
        ContDiffOn ℝ n (fun q : E × ℝ => f (q.1, √q.2)) (Hs E) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ f hf _
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hf.continuous.comp
      (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))).continuousOn
  | succ n ih =>
    intro F _ _ _ f hf hev
    rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn uniqueDiffOn_Hs]
    refine ⟨fun h => absurd h (WithTop.natCast_ne_top n), fun q => Dsqrt f (q.1, √q.2),
      ih (Dsqrt f) (contDiff_Dsqrt hf) (Dsqrt_even hf hev), fun p _ => ?_⟩
    exact hasFDerivWithinAt_comp_sqrt hf hev p

theorem contDiffOn_comp_sqrt {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : E × ℝ → F) (hf : ContDiff ℝ ∞ f)
    (hev : ∀ (e : E) (ρ : ℝ), f (e, -ρ) = f (e, ρ)) :
    ContDiffOn ℝ ∞ (fun q : E × ℝ => f (q.1, √q.2)) (Hs E) :=
  contDiffOn_infty.2 fun n => contDiffOn_comp_sqrt_nat n f hf hev

end EvenSqrt

section Circular

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem contDiff_polarSymm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have h : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p; exact Complex.polarCoord_symm_apply p
  rw [h]
  refine (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
    (((Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_snd))).add
      ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)).mul contDiff_const))

theorem polarSymm_neg (ρ θ : ℝ) :
    Complex.polarCoord.symm (-ρ, θ) = Complex.polarCoord.symm (ρ, θ + π) := by
  simp only [Complex.polarCoord_symm_apply, Real.cos_add_pi, Real.sin_add_pi]
  push_cast
  ring

theorem polarSymm_add_two_pi (ρ θ : ℝ) :
    Complex.polarCoord.symm (ρ, θ + 2 * π) = Complex.polarCoord.symm (ρ, θ) := by
  simp only [Complex.polarCoord_symm_apply, Real.cos_add_two_pi, Real.sin_add_two_pi]

noncomputable def gbar (g : E × ℂ → ℂ) (p : E × ℝ) : ℂ :=
  ∫ θ in (-π)..π, g (p.1, Complex.polarCoord.symm (p.2, θ))

theorem contDiff_gbar {g : E × ℂ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (gbar g) := by
  have hmap : ContDiff ℝ ∞ (fun q : (E × ℝ) × ℝ => ((q.1.1, Complex.polarCoord.symm (q.1.2, q.2)) : E × ℂ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_polarSymm.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  exact contDiff_integral (X := E × ℝ) (-π) π
    (fun q : (E × ℝ) × ℝ => g (q.1.1, Complex.polarCoord.symm (q.1.2, q.2))) (hg.comp hmap)

theorem gbar_even (g : E × ℂ → ℂ) (e : E) (ρ : ℝ) : gbar g (e, -ρ) = gbar g (e, ρ) := by
  unfold gbar
  simp only
  set G : ℝ → ℂ := fun θ => g (e, Complex.polarCoord.symm (ρ, θ)) with hG
  have hper : Function.Periodic G (2 * π) := fun θ => by
    simp only [hG, polarSymm_add_two_pi]
  calc ∫ θ in (-π)..π, g (e, Complex.polarCoord.symm (-ρ, θ))
      = ∫ θ in (-π)..π, G (θ + π) := by simp only [polarSymm_neg, hG]
    _ = ∫ θ in (-π + π)..(π + π), G θ := intervalIntegral.integral_comp_add_right G π
    _ = ∫ θ in (0 : ℝ)..(0 + 2 * π), G θ := by rw [neg_add_cancel, ← two_mul, zero_add]
    _ = ∫ θ in (-π)..(-π + 2 * π), G θ := hper.intervalIntegral_add_eq 0 (-π)
    _ = ∫ θ in (-π)..π, G θ := by rw [show -π + 2 * π = π by ring]

theorem exists_radius {g : E × ℂ → ℂ} (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : E × ℂ, g p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun p hp => ?_⟩
  have hmem : p ∈ Metric.closedBall (0 : E × ℂ) R := hR (subset_tsupport g hp)
  rw [mem_closedBall_zero_iff] at hmem
  exact ⟨(norm_fst_le p).trans (hmem.trans (le_max_left _ _)),
    (norm_snd_le p).trans (hmem.trans (le_max_left _ _))⟩

theorem gbar_support (g : E × ℂ → ℂ) (R : ℝ)
    (hR : ∀ p : E × ℂ, g p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R) (e : E) (ρ : ℝ)
    (h : gbar g (e, ρ) ≠ 0) : ‖e‖ ≤ R ∧ |ρ| ≤ R := by
  by_contra hcon
  apply h
  have hzero : ∀ θ : ℝ, g (e, Complex.polarCoord.symm (ρ, θ)) = 0 := by
    intro θ
    by_contra hne
    have h' := hR _ hne
    rw [Complex.norm_polarCoord_symm] at h'
    exact hcon h'
  show ∫ θ in (-π)..π, g (e, Complex.polarCoord.symm (ρ, θ)) = 0
  simp only [hzero, intervalIntegral.integral_zero]

end Circular

section Extension

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_extension (g : E × ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ H : E × ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ (e : E) (s : ℝ), 0 ≤ s → H (e, s) = gbar g (e, √s) := by
  obtain ⟨R, hRpos, hR⟩ := exists_radius hgc
  set Ψ : E × ℝ → ℂ := fun q => gbar g (q.1, √q.2) with hΨ
  have hΨs : ContDiffOn ℝ ∞ Ψ (Hs E) :=
    contDiffOn_comp_sqrt (gbar g) (contDiff_gbar hg) (gbar_even g)
  have hΨsupp : ∀ p : E × ℝ, Ψ p ≠ 0 → ‖p.1‖ ≤ R ∧ |√p.2| ≤ R :=
    fun p hp => gbar_support g R hR p.1 (√p.2) hp
  have hsupp : ∀ p : E × ℝ, p.1 ∉ Metric.closedBall (0 : E) R → Ψ p = 0 := by
    intro p hp
    by_contra hne
    exact hp (mem_closedBall_zero_iff.2 (hΨsupp p hne).1)
  obtain ⟨B, hB, hjet⟩ :=
    MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace Ψ hΨs
      (Metric.closedBall (0 : E) R) (isCompact_closedBall 0 R) hsupp
  set D : E × ℝ → ℂ := Ψ - B with hD
  have hDs : ContDiffOn ℝ ∞ D {p : E × ℝ | 0 ≤ p.2} := hΨs.sub hB.contDiffOn
  have hflat : ∀ (n : ℕ) (e : E),
      iteratedFDerivWithin ℝ n D {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0 := by
    intro n e
    have hmem : ((e, (0 : ℝ)) : E × ℝ) ∈ Hs E := le_refl (0 : ℝ)
    have hΨw : ContDiffWithinAt ℝ n Ψ (Hs E) (e, 0) :=
      (hΨs (e, 0) hmem).of_le (by exact_mod_cast le_top)
    have hBw : ContDiffWithinAt ℝ n B (Hs E) (e, 0) :=
      (hB.of_le (by exact_mod_cast le_top)).contDiffAt.contDiffWithinAt
    have h1 := iteratedFDerivWithin_sub_apply hΨw hBw uniqueDiffOn_Hs hmem
    have h2 : iteratedFDerivWithin ℝ n B (Hs E) (e, 0) = iteratedFDeriv ℝ n B (e, 0) :=
      iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_Hs
        (hB.of_le (by exact_mod_cast le_top)).contDiffAt hmem
    change iteratedFDerivWithin ℝ n (Ψ - B) (Hs E) (e, 0) = 0
    rw [h1, h2, hjet n e]
    exact sub_self _
  have hDabs :=
    MeasureTheory.contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero D hDs hflat
  set H₀ : E × ℝ → ℂ := fun p => B p + D (p.1, |p.2|) with hH₀
  have hH₀s : ContDiff ℝ ∞ H₀ := hB.add hDabs
  have hH₀eq : ∀ (e : E) (s : ℝ), 0 ≤ s → H₀ (e, s) = Ψ (e, s) := by
    intro e s hs
    simp only [hH₀, hD, abs_of_nonneg hs, Pi.sub_apply]
    abel

  set R' : ℝ := max R (R ^ 2) with hR'
  have hΨball : ∀ p : E × ℝ, 0 ≤ p.2 → Ψ p ≠ 0 → p ∈ Metric.closedBall (0 : E × ℝ) (R' + 1) := by
    intro p hp hne
    obtain ⟨h1, h2⟩ := hΨsupp p hne
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h2
    have h3 : p.2 ≤ R ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
      rwa [Real.sq_sqrt hp] at this
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hp]
    exact max_le (h1.trans ((le_max_left _ _).trans (by linarith)))
      (h3.trans ((le_max_right _ _).trans (by linarith)))
  let χ : ContDiffBump (0 : E × ℝ) := ⟨R' + 1, R' + 2, by positivity, by linarith⟩
  refine ⟨fun p => χ p • H₀ p, χ.contDiff.smul hH₀s, ?_, ?_⟩
  · exact χ.hasCompactSupport.smul_right
  · intro e s hs
    show χ (e, s) • H₀ (e, s) = Ψ (e, s)
    by_cases hne : Ψ (e, s) = 0
    · rw [hH₀eq e s hs, hne, smul_zero]
    · rw [χ.one_of_mem_closedBall (hΨball (e, s) hs hne), one_smul, hH₀eq e s hs]

end Extension

section LogLayer

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem locallyIntegrable_log_add (q : ℝ) :
    LocallyIntegrable (fun y : ℝ => Real.log (y + q)) volume := by
  refine locallyIntegrable_iff.2 fun k hk => ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  have hR' : k ⊆ Icc (-|R|) |R| := by
    intro x hx
    have := hR hx
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    have h' : |x| ≤ |R| := this.trans (le_abs_self R)
    exact ⟨by linarith [neg_abs_le x, abs_le.1 h'], (le_abs_self x).trans h'⟩
  have hint : IntervalIntegrable (fun y : ℝ => Real.log (y + q)) volume (-|R|) |R| := by
    have := (intervalIntegrable_log' (a := -|R| + q) (b := |R| + q)).comp_add_right q
    simpa using this
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [abs_nonneg R] : -|R| ≤ |R|)] at hint
  exact hint.mono_set hR'

noncomputable def ell : ℝ → ℝ := (Ioi (0 : ℝ)).indicator Real.log

theorem locallyIntegrable_ell : LocallyIntegrable ell volume := by
  have := (locallyIntegrable_log_add 0).indicator (measurableSet_Ioi (a := (0 : ℝ)))
  simpa [ell] using this

noncomputable def Kfun (H : E × ℝ → ℂ) : E × ℝ → ℂ :=
  fun p => MeasureTheory.convolution ell (fun v : ℝ => H (p.1, -v)) (ContinuousLinearMap.lsmul ℝ ℝ)
    volume p.2

theorem contDiff_Kfun {H : E × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    ContDiff ℝ ∞ (Kfun H) := by
  obtain ⟨T, hT⟩ := hHc.isCompact.isBounded.subset_closedBall 0
  have h := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := volume) (n := ⊤)
    (ContinuousLinearMap.lsmul ℝ ℝ) (f := ell) (g := fun (e : E) (v : ℝ) => H (e, -v)) (s := univ)
    (k := Metric.closedBall (0 : ℝ) T) isOpen_univ (isCompact_closedBall 0 T) ?_
    locallyIntegrable_ell ?_
  · rw [univ_prod_univ, contDiffOn_univ] at h
    unfold Kfun
    exact h
  · intro e v _ hv
    by_contra hne
    apply hv
    have hmem : ((e, -v) : E × ℝ) ∈ Metric.closedBall (0 : E × ℝ) T := hT (subset_tsupport H hne)
    rw [mem_closedBall_zero_iff] at hmem ⊢
    have := norm_snd_le ((e, -v) : E × ℝ)
    rw [norm_neg] at this
    exact this.trans hmem
  · rw [univ_prod_univ, contDiffOn_univ]
    exact hH.comp (contDiff_fst.prodMk contDiff_snd.neg)

theorem Kfun_eq (H : E × ℝ → ℂ) (e : E) (q : ℝ) :
    Kfun H (e, q) = ∫ y in Ioi (-q), Real.log (y + q) • H (e, y) := by
  unfold Kfun
  rw [convolution_lsmul]
  simp only [neg_sub]
  rw [← integral_add_right_eq_self (fun t : ℝ => ell t • H (e, t - q)) q]
  simp only [add_sub_cancel_right]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [ell, Set.indicator_apply, mem_Ioi]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; linarith
  · exfalso; linarith
  · rw [zero_smul]

theorem hasCompactSupport_slice {H : E × ℝ → ℂ} (hHc : HasCompactSupport H) (e : E) :
    HasCompactSupport (fun y : ℝ => H (e, y)) := by
  obtain ⟨T, hT⟩ := hHc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun y hy => ?_
  by_contra hne
  apply hy
  have hmem : ((e, y) : E × ℝ) ∈ Metric.closedBall (0 : E × ℝ) T := hT (subset_tsupport H hne)
  rw [mem_closedBall_zero_iff] at hmem ⊢
  exact (norm_snd_le ((e, y) : E × ℝ)).trans hmem

theorem integrable_log_smul {H : E × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (e : E) (q : ℝ) : Integrable (fun y : ℝ => Real.log (y + q) • H (e, y)) := by
  exact (locallyIntegrable_log_add q).integrable_smul_right_of_hasCompactSupport
    (hH.continuous.comp (Continuous.prodMk_right e)) (hasCompactSupport_slice hHc e)

theorem logLayer_identity {H : E × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (e : E) (q : ℝ) (hq : 0 ≤ q) :
    ∫ y in Ioi 0, Real.log (y + q) • H (e, y) =
      Kfun H (e, q) - (q * Real.log q) • (∫ t in (0 : ℝ)..1, H (e, q * (t - 1)))
        - q • (∫ t in (0 : ℝ)..1, Real.log t • H (e, q * (t - 1))) := by
  have hint := integrable_log_smul hH hHc e q
  rw [Kfun_eq, ← Ioc_union_Ioi_eq_Ioi (neg_nonpos.2 hq : -q ≤ 0),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint.integrableOn hint.integrableOn]
  suffices hJ : ∫ y in Ioc (-q) 0, Real.log (y + q) • H (e, y) =
      (q * Real.log q) • (∫ t in (0 : ℝ)..1, H (e, q * (t - 1)))
        + q • (∫ t in (0 : ℝ)..1, Real.log t • H (e, q * (t - 1))) by
    rw [hJ]; abel
  rcases hq.eq_or_lt with hzero | hqpos
  · subst hzero
    simp
  · rw [← intervalIntegral.integral_of_le (by linarith : -q ≤ 0)]
    have hsub := intervalIntegral.smul_integral_comp_mul_sub
      (f := fun y : ℝ => Real.log (y + q) • H (e, y)) (a := (0 : ℝ)) (b := 1) q q
    simp only [mul_zero, zero_sub, mul_one, sub_self] at hsub
    rw [← hsub]
    have hcongr : ∫ t in (0 : ℝ)..1, Real.log (q * t - q + q) • H (e, q * t - q)
        = ∫ t in (0 : ℝ)..1,
            (Real.log q • H (e, q * (t - 1)) + Real.log t • H (e, q * (t - 1))) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      have htpos : 0 < t := ht.1
      rw [sub_add_cancel, Real.log_mul hqpos.ne' htpos.ne', mul_sub, mul_one, add_smul]
    have hc1 : Continuous fun t : ℝ => H (e, q * (t - 1)) :=
      hH.continuous.comp (continuous_const.prodMk (continuous_const.mul (continuous_id.sub continuous_const)))
    have hi1 : IntervalIntegrable (fun t : ℝ => Real.log q • H (e, q * (t - 1))) volume 0 1 :=
      (hc1.fun_const_smul (Real.log q)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t : ℝ => Real.log t • H (e, q * (t - 1))) volume 0 1 :=
      intervalIntegrable_log'.smul_continuousOn hc1.continuousOn
    rw [hcongr, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_smul, smul_add,
      smul_smul]

end LogLayer

section Assembly

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem abs_mul_log_le (R q ρ : ℝ) (hq : 0 ≤ q) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    |ρ * Real.log (ρ ^ 2 + q)| ≤ R * |Real.log (R ^ 2 + q)| + 2 := by
  have hR : 0 < R := hρ.trans_le hρR
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hnn : 0 ≤ R * |Real.log (R ^ 2 + q)| := by positivity
  rw [abs_mul, abs_of_pos hρ]
  rcases le_or_gt 1 (ρ ^ 2 + q) with h1 | h1
  · have hlog0 : 0 ≤ Real.log (ρ ^ 2 + q) := Real.log_nonneg h1
    have hle : Real.log (ρ ^ 2 + q) ≤ Real.log (R ^ 2 + q) :=
      Real.log_le_log (by positivity) (by nlinarith)
    calc ρ * |Real.log (ρ ^ 2 + q)| = ρ * Real.log (ρ ^ 2 + q) := by rw [abs_of_nonneg hlog0]
      _ ≤ R * Real.log (R ^ 2 + q) := mul_le_mul hρR hle hlog0 hR.le
      _ ≤ R * |Real.log (R ^ 2 + q)| := by gcongr; exact le_abs_self _
      _ ≤ _ := by linarith
  · have hρ1 : ρ ≤ 1 := by nlinarith
    have hlogneg : Real.log (ρ ^ 2 + q) ≤ 0 := Real.log_nonpos (by positivity) h1.le
    have hge : Real.log (ρ ^ 2) ≤ Real.log (ρ ^ 2 + q) := Real.log_le_log hρ2 (by linarith)
    have hlogsq : Real.log (ρ ^ 2) = 2 * Real.log ρ := by
      rw [Real.log_pow]; norm_num
    have hself : |Real.log ρ * ρ| < 1 := Real.abs_log_mul_self_lt ρ hρ hρ1
    have h5 : -(Real.log ρ * ρ) ≤ |Real.log ρ * ρ| := neg_le_abs _
    have hmain : ρ * |Real.log (ρ ^ 2 + q)| ≤ 2 := by
      rw [abs_of_nonpos hlogneg]
      have h3 : ρ * -Real.log (ρ ^ 2 + q) ≤ ρ * -(2 * Real.log ρ) := by
        apply mul_le_mul_of_nonneg_left _ hρ.le
        linarith
      have h4 : ρ * -(2 * Real.log ρ) = -2 * (Real.log ρ * ρ) := by ring
      linarith
    linarith

theorem integrableOn_polar (g : E × ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (e : E) (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 * Real.log (p.1 ^ 2 + q)) • g (e, Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
  obtain ⟨R, hRpos, hR⟩ := exists_radius hgc
  obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hzero : ∀ p : ℝ × ℝ, R < |p.1| → g (e, Complex.polarCoord.symm p) = 0 := by
    intro p hp
    by_contra hne
    have := (hR _ hne).2
    rw [Complex.norm_polarCoord_symm] at this
    linarith
  have hmeas : MeasurableSet (Ioc (0 : ℝ) R ×ˢ Ioo (-π) π) := measurableSet_Ioc.prod measurableSet_Ioo
  have hfin : IntegrableOn
      (fun p : ℝ × ℝ => (p.1 * Real.log (p.1 ^ 2 + q)) • g (e, Complex.polarCoord.symm p))
      (Ioc 0 R ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hlt : (volume.prod volume) (Ioc (0 : ℝ) R ×ˢ Ioo (-π) π) ≠ ⊤ := by
      rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (p.1 * Real.log (p.1 ^ 2 + q)) • g (e, Complex.polarCoord.symm p))
        (Ioc 0 R ×ˢ Ioo (-π) π) := by
      intro p hp
      have hp1 : 0 < p.1 := hp.1.1
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.fun_smul ?_ ?_
      · exact continuousAt_fst.mul
          (((continuousAt_fst.pow 2).add continuousAt_const).log (show p.1 ^ 2 + q ≠ 0 by positivity))
      · exact (hg.continuous.comp
          (continuous_const.prodMk contDiff_polarSymm.continuous)).continuousAt
    refine Integrable.mono' (g := fun _ => (R * |Real.log (R ^ 2 + q)| + 2) * M)
      (integrableOn_const hlt) (hcont.aestronglyMeasurable hmeas) ?_
    refine (ae_restrict_iff' hmeas).2 (ae_of_all _ fun p hp => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_mul_log_le R q p.1 hq hp.1.1 hp.1.2) (hM _) (norm_nonneg _)
      (by positivity)
  refine hfin.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  have hp1 : R < p.1 := by
    rcases hp with ⟨⟨h1, h2⟩, hn⟩
    by_contra hle
    exact hn ⟨⟨h1, not_lt.1 hle⟩, h2⟩
  have : g (e, Complex.polarCoord.symm p) = 0 :=
    hzero p (by rw [abs_of_pos (hRpos.trans hp1)]; exact hp1)
  simp only [this, smul_zero]

theorem polar_step (g : E × ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (e : E) (q : ℝ) (hq : 0 ≤ q) :
    ∫ z : ℂ, Real.log (‖z‖ ^ 2 + q) • g (e, z) =
      ∫ ρ in Ioi (0 : ℝ), (ρ * Real.log (ρ ^ 2 + q)) • gbar g (e, ρ) := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hcongr : EqOn
      (fun p : ℝ × ℝ => p.1 • (Real.log (‖Complex.polarCoord.symm p‖ ^ 2 + q) •
        g (e, Complex.polarCoord.symm p)))
      (fun p : ℝ × ℝ => (p.1 * Real.log (p.1 ^ 2 + q)) • g (e, Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-π) π) := by
    intro p _
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_smul]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcongr,
    Measure.volume_eq_prod, setIntegral_prod _ (integrableOn_polar g hg hgc e q hq)]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
  simp only
  rw [MeasureTheory.integral_smul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]
  rfl

theorem subst_step (g : E × ℂ → ℂ) (e : E) (q : ℝ) :
    ∫ ρ in Ioi (0 : ℝ), (ρ * Real.log (ρ ^ 2 + q)) • gbar g (e, ρ) =
      ∫ y in Ioi (0 : ℝ), ((1 / 2 : ℝ) * Real.log (y + q)) • gbar g (e, √y) := by
  rw [← integral_comp_rpow_Ioi (fun y => ((1 / 2 : ℝ) * Real.log (y + q)) • gbar g (e, √y))
    two_ne_zero]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ' : 0 < ρ := hρ
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Real.sqrt_sq hρ'.le,
    smul_smul]
  congr 1
  rw [abs_of_pos two_pos]
  ring

theorem main (g : E × ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℂ → ℂ, ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ B ∧
      ∀ (e : E) (r : ℂ),
        ∫ z : ℂ, g (e, z) * (Real.log (‖z‖ ^ 2 + ‖r‖ ^ 2) : ℂ) =
          A (e, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (e, r) := by
  obtain ⟨H, hH, hHc, hHeq⟩ := exists_extension g hg hgc
  set B₁ : E × ℝ → ℂ := fun p => ∫ t in (0 : ℝ)..1, H (p.1, p.2 * (t - 1)) with hB₁
  set Λ : E × ℝ → ℂ := fun p => ∫ t in (0 : ℝ)..1, Real.log t • H (p.1, p.2 * (t - 1)) with hΛ
  have hmap : ContDiff ℝ ∞ (fun q : (E × ℝ) × ℝ => ((q.1.1, q.1.2 * (q.2 - 1)) : E × ℝ)) := by
    fun_prop
  have hB₁s : ContDiff ℝ ∞ B₁ :=
    contDiff_integral (X := E × ℝ) 0 1 (fun q : (E × ℝ) × ℝ => H (q.1.1, q.1.2 * (q.2 - 1)))
      (hH.comp hmap)
  have hΛs : ContDiff ℝ ∞ Λ :=
    contDiff_integral_smul (X := E × ℝ) Real.log 0 1 intervalIntegrable_log'
      (fun q : (E × ℝ) × ℝ => H (q.1.1, q.1.2 * (q.2 - 1))) (hH.comp hmap)
  have hKs : ContDiff ℝ ∞ (Kfun H) := contDiff_Kfun hH hHc
  set φ : E × ℂ → E × ℝ := fun p => (p.1, ‖p.2‖ ^ 2) with hφ
  have hns : ContDiff ℝ ∞ (fun p : E × ℂ => ‖p.2‖ ^ 2) := (contDiff_norm_sq ℝ).comp contDiff_snd
  have hφs : ContDiff ℝ ∞ φ := contDiff_fst.prodMk hns
  refine ⟨fun p => (1 / 2 : ℝ) • (Kfun H (φ p) - (‖p.2‖ ^ 2) • Λ (φ p)), fun p => -B₁ (φ p),
    ?_, ?_, ?_⟩
  · exact (contDiff_const (c := (1 / 2 : ℝ))).smul ((hKs.comp hφs).sub (hns.smul (hΛs.comp hφs)))
  · exact (hB₁s.comp hφs).neg
  · intro e r
    have hlog : Real.log (‖r‖ ^ 2) = 2 * Real.log ‖r‖ := by
      rw [Real.log_pow]; norm_num
    have hq0 : 0 ≤ ‖r‖ ^ 2 := by positivity
    have step1 : ∫ z : ℂ, g (e, z) * (Real.log (‖z‖ ^ 2 + ‖r‖ ^ 2) : ℂ) =
        ∫ z : ℂ, Real.log (‖z‖ ^ 2 + ‖r‖ ^ 2) • g (e, z) := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only
      rw [mul_comm, Complex.real_smul]
    have step4 : ∫ y in Ioi (0 : ℝ), ((1 / 2 : ℝ) * Real.log (y + ‖r‖ ^ 2)) • gbar g (e, √y) =
        (1 / 2 : ℝ) • ∫ y in Ioi (0 : ℝ), Real.log (y + ‖r‖ ^ 2) • H (e, y) := by
      rw [← MeasureTheory.integral_smul]
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hy' : 0 < y := hy
      rw [hHeq e y hy'.le, smul_smul]
    rw [step1, polar_step g hg hgc e (‖r‖ ^ 2) hq0, subst_step g e (‖r‖ ^ 2), step4,
      logLayer_identity hH hHc e (‖r‖ ^ 2) hq0]
    simp only [hφ, hB₁, hΛ, Complex.real_smul, hlog]
    push_cast
    ring

end Assembly

end P2mD0Complex

open MeasureTheory in
theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℂ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (e : E) (r : ℂ),
        ∫ z : ℂ, g (e, z) * (Real.log (‖z‖ ^ 2 + ‖r‖ ^ 2) : ℂ) =
          A (e, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (e, r) :=
  P2mD0Complex.main g hg hgc

end S_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport (solution)
