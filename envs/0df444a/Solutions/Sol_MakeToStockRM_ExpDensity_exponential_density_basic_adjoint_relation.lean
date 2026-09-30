-- Prove2me | solution 1 for MakeToStockRM.ExpDensity.exponential_density_basic_adjoint_relation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:45:17.698242+00:00
-- url     : https://prove2.me/submissions/0977848e-4044-43be-b253-7e9f141127ae

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity
import Definitions.Def_MakeToStockRM_ExpDensity_region
import Definitions.Def_MakeToStockRM_ExpDensity_boundaryTerm



namespace MakeToStockRM.ExpDensity

open MeasureTheory Set

lemma mts_swap (f : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f)) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma mts_subst (g : ℝ → ℝ) (u v : ℝ) :
    ∫ x in u..v, g x = ∫ t in (0:ℝ)..1, (v - u) * g ((v - u) * t + u) := by
  rw [intervalIntegral.integral_const_mul]
  have := intervalIntegral.smul_integral_comp_mul_add (f := g) (a := 0) (b := 1) (v - u) u
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at this
  rw [this]


lemma mts_dy (F : ℝ × ℝ → ℝ) (D : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (hD : ∀ z, HasFDerivAt F (D z) z)
    (hDc : Continuous D) (η ξ : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ)
    (a b : ℝ) (hab : a ≤ b) :
    ∫ y in a..b, ∫ x in η y..ξ y, D (x, y) (0, 1) =
      (∫ x in η b..ξ b, F (x, b)) - (∫ x in η a..ξ a, F (x, a))
        - ((∫ y in a..b, deriv ξ y * F (ξ y, y)) - ∫ y in a..b, deriv η y * F (η y, y)) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun z => (hD z).continuousAt
  have hη' : ∀ y, HasDerivAt η (deriv η y) y := fun y =>
    ((hη.differentiable (by norm_num)) y).hasDerivAt
  have hξ' : ∀ y, HasDerivAt ξ (deriv ξ y) y := fun y =>
    ((hξ.differentiable (by norm_num)) y).hasDerivAt
  have cη : Continuous η := hη.continuous
  have cξ : Continuous ξ := hξ.continuous
  have cη' : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have cξ' : Continuous (deriv ξ) := hξ.continuous_deriv le_rfl
  set L : ℝ → ℝ := fun y => ξ y - η y with hL
  set L' : ℝ → ℝ := fun y => deriv ξ y - deriv η y with hL'
  have hLd : ∀ y, HasDerivAt L (L' y) y := fun y => (hξ' y).sub (hη' y)
  set X : ℝ → ℝ → ℝ × ℝ := fun y t => (L y * t + η y, y) with hX
  set A : ℝ → ℝ → ℝ := fun y t => L' y * F (X y t) + L y * D (X y t) (L' y * t + deriv η y, 1)
    with hA
  set B : ℝ → ℝ → ℝ := fun y t => L' y * F (X y t) + (deriv η y + t * L' y) * D (X y t) (L y, 0)
    with hB
  have hpt : ∀ y t, L y * D (X y t) (0, 1) = A y t - B y t := by
    intro y t
    have e1 : ((L' y * t + deriv η y, (1:ℝ)) : ℝ × ℝ) = (L' y * t + deriv η y) • ((1:ℝ), (0:ℝ)) + (0, 1) := by
      ext <;> simp
    have e2 : ((L y, (0:ℝ)) : ℝ × ℝ) = L y • ((1:ℝ), (0:ℝ)) := by ext <;> simp
    simp only [hA, hB, e1, e2, map_add, map_smul, smul_eq_mul]
    ring
  have hXy : ∀ y t, HasDerivAt (fun y => X y t) (L' y * t + deriv η y, 1) y := by
    intro y t
    exact (((hLd y).mul_const t).add (hη' y)).prodMk (hasDerivAt_id y)
  have hXt : ∀ y t, HasDerivAt (fun t => X y t) (L y, 0) t := by
    intro y t
    have := (((hasDerivAt_id t).const_mul (L y)).add_const (η y)).prodMk (hasDerivAt_const t y)
    simpa using this
  have hAd : ∀ y t, HasDerivAt (fun y => L y * F (X y t)) (A y t) y := by
    intro y t
    have h2 : HasDerivAt (fun y => F (X y t)) (D (X y t) (L' y * t + deriv η y, 1)) y :=
      (hD (X y t)).comp_hasDerivAt (f := fun y => X y t) y (hXy y t)
    exact ((hLd y).mul h2).congr_deriv (by simp [hA])
  have hBd : ∀ y t, HasDerivAt (fun t => (deriv η y + t * L' y) * F (X y t)) (B y t) t := by
    intro y t
    have h2 : HasDerivAt (fun t => F (X y t)) (D (X y t) (L y, 0)) t :=
      (hD (X y t)).comp_hasDerivAt (f := fun t => X y t) t (hXt y t)
    have h1 : HasDerivAt (fun t => deriv η y + t * L' y) (L' y) t := by
      simpa using ((hasDerivAt_id t).mul_const (L' y)).const_add (deriv η y)
    exact (h1.mul h2).congr_deriv (by simp [hB])
  have cX : Continuous (Function.uncurry X) := by
    simp only [hX, hL]; fun_prop
  have cA : Continuous (Function.uncurry A) := by
    simp only [hA, hL', hL]
    have : Continuous fun p : ℝ × ℝ => D (X p.1 p.2) := hDc.comp cX
    fun_prop
  have cB : Continuous (Function.uncurry B) := by
    simp only [hB, hL', hL]
    have : Continuous fun p : ℝ × ℝ => D (X p.1 p.2) := hDc.comp cX
    fun_prop
  have cAy : ∀ t, Continuous fun y => A y t := fun t => cA.comp (continuous_id.prodMk continuous_const)
  have cAt : ∀ y, Continuous fun t => A y t := fun y => cA.comp (continuous_const.prodMk continuous_id)
  have cBt : ∀ y, Continuous fun t => B y t := fun y => cB.comp (continuous_const.prodMk continuous_id)
  -- step 1
  have s1 : ∀ y, ∫ x in η y..ξ y, D (x, y) (0, 1) = ∫ t in (0:ℝ)..1, (A y t - B y t) := by
    intro y
    rw [mts_subst]
    congr 1; funext t; rw [← hpt]
  have s2 : ∀ y, ∫ t in (0:ℝ)..1, B y t = deriv ξ y * F (ξ y, y) - deriv η y * F (η y, y) := by
    intro y
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hBd y t)
      ((cBt y).intervalIntegrable _ _)]
    simp only [hX, hL, hL']
    ring_nf
  have s3 : ∀ y, ∫ t in (0:ℝ)..1, (A y t - B y t) = (∫ t in (0:ℝ)..1, A y t)
      - (deriv ξ y * F (ξ y, y) - deriv η y * F (η y, y)) := by
    intro y
    rw [intervalIntegral.integral_sub ((cAt y).intervalIntegrable _ _)
      ((cBt y).intervalIntegrable _ _), s2]
  simp_rw [s1, s3]
  have cI : Continuous fun y => ∫ t in (0:ℝ)..1, A y t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' cA 0 1
  have cG : Continuous fun y => deriv ξ y * F (ξ y, y) - deriv η y * F (η y, y) := by
    fun_prop
  rw [intervalIntegral.integral_sub (cI.intervalIntegrable _ _) (cG.intervalIntegrable _ _),
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun y => deriv ξ y * F (ξ y, y)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun y => deriv η y * F (η y, y)).intervalIntegrable _ _)]
  congr 1
  rw [mts_swap A cA a b 0 1 hab zero_le_one]
  have s4 : ∀ t, ∫ y in a..b, A y t = L b * F (X b t) - L a * F (X a t) :=
    fun t => intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hAd y t)
      ((cAy t).intervalIntegrable _ _)
  simp_rw [s4]
  rw [intervalIntegral.integral_sub, mts_subst (fun x => F (x, b)), mts_subst (fun x => F (x, a))]
  · exact (by fun_prop : Continuous fun t => L b * F (X b t)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun t => L a * F (X a t)).intervalIntegrable _ _


lemma mts_cont (h : ℝ × ℝ → ℝ) (hh : Continuous h) (η ξ : ℝ → ℝ) (cη : Continuous η)
    (cξ : Continuous ξ) : Continuous fun y => ∫ x in η y..ξ y, h (x, y) := by
  simp_rw [mts_subst (fun x => h (x, _))]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y t => (ξ y - η y) * h ((ξ y - η y) * t + η y, y)) (by fun_prop) 0 1

lemma mts_green (F1 F2 : ℝ × ℝ → ℝ) (D1 D2 : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (hD1 : ∀ z, HasFDerivAt F1 (D1 z) z) (hD2 : ∀ z, HasFDerivAt F2 (D2 z) z)
    (hc1 : Continuous D1) (hc2 : Continuous D2) (η ξ : ℝ → ℝ) (hη : ContDiff ℝ 1 η)
    (hξ : ContDiff ℝ 1 ξ) (a b : ℝ) (hab : a ≤ b) :
    ∫ y in a..b, ∫ x in η y..ξ y, (D1 (x, y) (1, 0) + D2 (x, y) (0, 1)) =
      (∫ y in a..b, (F1 (ξ y, y) - deriv ξ y * F2 (ξ y, y)))
        - (∫ y in a..b, (F1 (η y, y) - deriv η y * F2 (η y, y)))
        + (∫ x in η b..ξ b, F2 (x, b)) - ∫ x in η a..ξ a, F2 (x, a) := by
  have hF1c : Continuous F1 := continuous_iff_continuousAt.2 fun z => (hD1 z).continuousAt
  have hF2c : Continuous F2 := continuous_iff_continuousAt.2 fun z => (hD2 z).continuousAt
  have cη : Continuous η := hη.continuous
  have cξ : Continuous ξ := hξ.continuous
  have cη' : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have cξ' : Continuous (deriv ξ) := hξ.continuous_deriv le_rfl
  have c1 : Continuous fun z : ℝ × ℝ => D1 z (1, 0) := by fun_prop
  have c2 : Continuous fun z : ℝ × ℝ => D2 z (0, 1) := by fun_prop
  have inner : ∀ y, ∫ x in η y..ξ y, (D1 (x, y) (1, 0) + D2 (x, y) (0, 1)) =
      (F1 (ξ y, y) - F1 (η y, y)) + ∫ x in η y..ξ y, D2 (x, y) (0, 1) := by
    intro y
    have e1 : Continuous fun x => D1 (x, y) (1, 0) := by fun_prop
    have e2 : Continuous fun x => D2 (x, y) (0, 1) := by fun_prop
    rw [intervalIntegral.integral_add (e1.intervalIntegrable _ _) (e2.intervalIntegrable _ _)]
    congr 1
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => F1 (x, y))
    · intro x _
      exact (hD1 (x, y)).comp_hasDerivAt (f := fun x => (x, y)) x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    · exact e1.intervalIntegrable _ _
  simp_rw [inner]
  have cc := mts_cont (fun z => D2 z (0, 1)) c2 η ξ cη cξ
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun y => F1 (ξ y, y) - F1 (η y, y)).intervalIntegrable _ _)
    (cc.intervalIntegrable _ _), mts_dy F2 D2 hD2 hc2 η ξ hη hξ a b hab]
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun y => F1 (ξ y, y)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun y => F1 (η y, y)).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun y => F1 (ξ y, y)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun y => deriv ξ y * F2 (ξ y, y)).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun y => F1 (η y, y)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun y => deriv η y * F2 (η y, y)).intervalIntegrable _ _)]
  ring

lemma mts_region (h : ℝ × ℝ → ℝ) (hh : Continuous h) (η ξ : ℝ → ℝ) (cη : Continuous η)
    (cξ : Continuous ξ) (a b : ℝ) (hab : a ≤ b) (hle : ∀ y ∈ Icc a b, η y ≤ ξ y) :
    ∫ z in region η ξ a b, h z = ∫ y in a..b, ∫ x in η y..ξ y, h (x, y) := by
  have mR : MeasurableSet (region η ξ a b) := by
    apply IsOpen.measurableSet
    have : region η ξ a b = {z : ℝ × ℝ | a < z.2} ∩ {z | z.2 < b} ∩ {z | η z.2 < z.1}
        ∩ {z | z.1 < ξ z.2} := by
      ext z; simp [region, and_assoc]
    rw [this]
    refine ((((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)).inter
      (isOpen_lt (cη.comp continuous_snd) continuous_fst)).inter
      (isOpen_lt continuous_fst (cξ.comp continuous_snd)))
  obtain ⟨m, hm⟩ := (isCompact_Icc (a := a) (b := b)).bddBelow_image cη.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).bddAbove_image cξ.continuousOn
  have hsub : region η ξ a b ⊆ Icc m M ×ˢ Icc a b := by
    intro z hz
    simp only [region, mem_setOf_eq] at hz
    have hy : z.2 ∈ Icc a b := ⟨hz.1.le, hz.2.1.le⟩
    have h1 := hm (mem_image_of_mem η hy)
    have h2 := hM (mem_image_of_mem ξ hy)
    exact ⟨⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩, hy⟩
  have hint : IntegrableOn h (region η ξ a b) :=
    (hh.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hsub
  rw [← integral_indicator mR, Measure.volume_eq_prod]
  rw [integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact (integrable_indicator_iff mR).2 hint)]
  have key : ∀ y, ∫ x, (region η ξ a b).indicator h (x, y) =
      (Ioo a b).indicator (fun y => ∫ x in η y..ξ y, h (x, y)) y := by
    intro y
    by_cases hy : y ∈ Ioo a b
    · rw [indicator_of_mem hy]
      have e : (fun x => (region η ξ a b).indicator h (x, y)) =
          (Ioo (η y) (ξ y)).indicator (fun x => h (x, y)) := by
        funext x
        by_cases hx : x ∈ Ioo (η y) (ξ y)
        · rw [indicator_of_mem hx, indicator_of_mem]
          exact ⟨hy.1, hy.2, hx.1, hx.2⟩
        · rw [indicator_of_notMem hx, indicator_of_notMem]
          intro hz; exact hx ⟨hz.2.2.1, hz.2.2.2⟩
      rw [e, integral_indicator measurableSet_Ioo,
        intervalIntegral.integral_of_le (hle y (Ioo_subset_Icc_self hy)),
        integral_Ioc_eq_integral_Ioo]
    · rw [indicator_of_notMem hy]
      have e : (fun x => (region η ξ a b).indicator h (x, y)) = fun _ => 0 := by
        funext x
        rw [indicator_of_notMem]
        intro hz; exact hy ⟨hz.1, hz.2.1⟩
      rw [e, integral_zero]
  simp_rw [key]
  rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]


lemma mts_cf (σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z w : ℝ × ℝ) :
    conormalFlux σ δ ϱ f z w = (σ ^ 2 * w.1 + σ * δ * ϱ * w.2) * partialX f z
      + (σ * δ * ϱ * w.1 + δ ^ 2 * w.2) * partialY f z := by
  simp [conormalFlux, covMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma mts_sym (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) (z : ℝ × ℝ) :
    partialY (partialX f) z = partialX (partialY f) z := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z := hf1.differentiable (by norm_num) z
  have hs := (hf.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun w => fderiv ℝ f w (1, 0)) z (0, 1) = fderiv ℝ (fun w => fderiv ℝ f w (0, 1)) z (1, 0)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply]
  exact hs _ _

theorem mts_core (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (f : ℝ × ℝ → ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) (hy : ymin < ymax)
    (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y)
    (hf : ContDiff ℝ 2 f) :
    (∫ z in region η ξ ymin ymax, generator θ σ δ ϱ f z * expDensity θ σ δ ϱ z)
      + 1 / 2 * boundaryTerm σ δ ϱ η ξ ymin ymax f (expDensity θ σ δ ϱ) = 0 := by
  have hϱ2 : 1 - ϱ ^ 2 ≠ 0 := by
    have := abs_lt.1 hϱ; nlinarith
  have hm1 : σ ^ 2 * mx θ σ ϱ + σ * δ * ϱ * my θ σ δ ϱ = 2 * θ := by
    unfold mx my; field_simp; ring
  have hm2 : σ * δ * ϱ * mx θ σ ϱ + δ ^ 2 * my θ σ δ ϱ = 0 := by
    unfold mx my; field_simp; ring
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have cfx : ContDiff ℝ 1 (partialX f) := hf1.clm_apply contDiff_const
  have cfy : ContDiff ℝ 1 (partialY f) := hf1.clm_apply contDiff_const
  have cp : ContDiff ℝ 1 (expDensity θ σ δ ϱ) := by
    unfold expDensity
    exact Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd))
  have hpd : ∀ z : ℝ × ℝ, HasFDerivAt (expDensity θ σ δ ϱ) (fderiv ℝ (expDensity θ σ δ ϱ) z) z :=
    fun z => (cp.differentiable (by norm_num) z).hasFDerivAt
  have hpx : ∀ z : ℝ × ℝ, fderiv ℝ (expDensity θ σ δ ϱ) z (1, 0) = mx θ σ ϱ * expDensity θ σ δ ϱ z ∧
      fderiv ℝ (expDensity θ σ δ ϱ) z (0, 1) = my θ σ δ ϱ * expDensity θ σ δ ϱ z := by
    intro z
    have h := (((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul (mx θ σ ϱ)).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_mul (my θ σ δ ϱ))).exp
    have e : expDensity θ σ δ ϱ = fun z : ℝ × ℝ => Real.exp (mx θ σ ϱ * z.1 + my θ σ δ ϱ * z.2) := rfl
    rw [e, HasFDerivAt.fderiv (f := fun z : ℝ × ℝ => Real.exp (mx θ σ ϱ * z.1 + my θ σ δ ϱ * z.2)) h]
    constructor <;> simp <;> ring
  have hfx : ∀ z, HasFDerivAt (partialX f) (fderiv ℝ (partialX f) z) z :=
    fun z => (cfx.differentiable (by norm_num) z).hasFDerivAt
  have hfy : ∀ z, HasFDerivAt (partialY f) (fderiv ℝ (partialY f) z) z :=
    fun z => (cfy.differentiable (by norm_num) z).hasFDerivAt
  obtain ⟨F1, hF1⟩ : ∃ F : ℝ × ℝ → ℝ, F = fun z => 1 / 2 * expDensity θ σ δ ϱ z *
      (σ ^ 2 * partialX f z + σ * δ * ϱ * partialY f z) := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F : ℝ × ℝ → ℝ, F = fun z => 1 / 2 * expDensity θ σ δ ϱ z *
      (σ * δ * ϱ * partialX f z + δ ^ 2 * partialY f z) := ⟨_, rfl⟩
  have cF1 : ContDiff ℝ 1 F1 := by
    rw [hF1]; exact (contDiff_const.mul cp).mul ((contDiff_const.mul cfx).add (contDiff_const.mul cfy))
  have cF2 : ContDiff ℝ 1 F2 := by
    rw [hF2]; exact (contDiff_const.mul cp).mul ((contDiff_const.mul cfx).add (contDiff_const.mul cfy))
  have hpt : ∀ z, fderiv ℝ F1 z (1, 0) + fderiv ℝ F2 z (0, 1) =
      generator θ σ δ ϱ f z * expDensity θ σ δ ϱ z := by
    intro z
    have h1 := (((hpd z).const_mul (1 / 2)).mul
      (((hfx z).const_mul (σ ^ 2)).add ((hfy z).const_mul (σ * δ * ϱ))))
    have h2 := (((hpd z).const_mul (1 / 2)).mul
      (((hfx z).const_mul (σ * δ * ϱ)).add ((hfy z).const_mul (δ ^ 2))))
    rw [hF1, hF2, HasFDerivAt.fderiv (f := fun z => 1 / 2 * expDensity θ σ δ ϱ z *
      (σ ^ 2 * partialX f z + σ * δ * ϱ * partialY f z)) h1,
      HasFDerivAt.fderiv (f := fun z => 1 / 2 * expDensity θ σ δ ϱ z *
      (σ * δ * ϱ * partialX f z + δ ^ 2 * partialY f z)) h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [(hpx z).1, (hpx z).2]
    have e1 : fderiv ℝ (partialX f) z (1, 0) = partialX (partialX f) z := rfl
    have e2 : fderiv ℝ (partialY f) z (1, 0) = partialX (partialY f) z := rfl
    have e3 : fderiv ℝ (partialX f) z (0, 1) = partialX (partialY f) z := mts_sym f hf z
    have e4 : fderiv ℝ (partialY f) z (0, 1) = partialY (partialY f) z := rfl
    rw [e1, e2, e3, e4]
    unfold generator
    linear_combination (1 / 2 * expDensity θ σ δ ϱ z * partialX f z) * hm1
      + (1 / 2 * expDensity θ σ δ ϱ z * partialY f z) * hm2
  have hD1 : ∀ z, HasFDerivAt F1 (fderiv ℝ F1 z) z :=
    fun z => (cF1.differentiable (by norm_num) z).hasFDerivAt
  have hD2 : ∀ z, HasFDerivAt F2 (fderiv ℝ F2 z) z :=
    fun z => (cF2.differentiable (by norm_num) z).hasFDerivAt
  have hc1 : Continuous (fderiv ℝ F1) := cF1.continuous_fderiv (by norm_num)
  have hc2 : Continuous (fderiv ℝ F2) := cF2.continuous_fderiv (by norm_num)
  have eI : (∫ z in region η ξ ymin ymax, generator θ σ δ ϱ f z * expDensity θ σ δ ϱ z)
      = ∫ z in region η ξ ymin ymax, (fderiv ℝ F1 z (1, 0) + fderiv ℝ F2 z (0, 1)) := by
    congr 1; funext z; rw [hpt]
  have ch : Continuous fun z => fderiv ℝ F1 z (1, 0) + fderiv ℝ F2 z (0, 1) := by fun_prop
  rw [eI, mts_region _ ch η ξ hη.continuous hξ.continuous ymin ymax hy.le
    (fun y hy => (hlt y hy).le),
    mts_green F1 F2 (fderiv ℝ F1) (fderiv ℝ F2) hD1 hD2 hc1 hc2 η ξ hη hξ ymin ymax hy.le]
  unfold boundaryTerm
  have b1 : (fun y => conormalFlux σ δ ϱ f (η y, y) (1, -deriv η y) * expDensity θ σ δ ϱ (η y, y))
      = fun y => 2 * (F1 (η y, y) - deriv η y * F2 (η y, y)) := by
    funext y; simp only [mts_cf, hF1, hF2]; ring
  have b2 : (fun y => conormalFlux σ δ ϱ f (ξ y, y) (-1, deriv ξ y) * expDensity θ σ δ ϱ (ξ y, y))
      = fun y => (-2) * (F1 (ξ y, y) - deriv ξ y * F2 (ξ y, y)) := by
    funext y; simp only [mts_cf, hF1, hF2]; ring
  have b3 : (fun x => conormalFlux σ δ ϱ f (x, ymin) (0, 1) * expDensity θ σ δ ϱ (x, ymin))
      = fun x => 2 * F2 (x, ymin) := by
    funext x; simp only [mts_cf, hF1, hF2]; ring
  have b4 : (fun x => conormalFlux σ δ ϱ f (x, ymax) (0, -1) * expDensity θ σ δ ϱ (x, ymax))
      = fun x => (-2) * F2 (x, ymax) := by
    funext x; simp only [mts_cf, hF1, hF2]; ring
  rw [b1, b2, b3, b4]
  simp only [intervalIntegral.integral_const_mul]
  ring

end MakeToStockRM.ExpDensity

open MakeToStockRM.ExpDensity


theorem solution (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (f : ℝ × ℝ → ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) (hy : ymin < ymax)
    (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y)
    (hf : ContDiff ℝ 2 f) :
    (∫ z in region η ξ ymin ymax, generator θ σ δ ϱ f z * expDensity θ σ δ ϱ z)
      + 1 / 2 * boundaryTerm σ δ ϱ η ξ ymin ymax f (expDensity θ σ δ ϱ) = 0 := by
  exact mts_core θ σ δ ϱ ymin ymax η ξ f hσ hδ hϱ hy hη hξ hlt hf
