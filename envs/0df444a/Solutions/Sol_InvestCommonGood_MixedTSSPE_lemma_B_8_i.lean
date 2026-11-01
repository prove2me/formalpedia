-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.lemma_B_8_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:50:58.949532+00:00
-- url     : https://prove2.me/submissions/0876484c-8d4d-49bd-bece-2667926e99ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 xh : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S)
    (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) (hxh : IsLemma2Point m S xh)
    (hθ : θ < xh) (hz2 : xh < z2) :
    Sec42V2 m S c2 θ z2 (Vhat2 m S c2 θ z2) := by
  obtain ⟨⟨xh', hxh'pt, hxh'lt⟩, hpart2⟩ := lemma_2 m S zs xs hS hA1 hA2 hA4
  have hIo : IsOpen m.I := hS.I_open
  have hIc : m.I.OrdConnected := hS.I_ordConnected
  have hIconv : Convex ℝ m.I := hIc.convex
  have hxhI : xh ∈ m.I := hxh.1
  -- uniqueness of the Lemma 2 point
  have hxheq : xh' = xh := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hmid : (xh' + xh) / 2 ∈ m.I := hIc.out hxh'pt.1 hxhI ⟨by linarith, by linarith⟩
      have h1 := (hxh'pt.2.2 _ hmid (by linarith)).1
      have h2 := (hxh.2.1 _ hmid (by linarith)).1
      linarith
    · have hmid : (xh' + xh) / 2 ∈ m.I := hIc.out hxhI hxh'pt.1 ⟨by linarith, by linarith⟩
      have h1 := (hxh'pt.2.1 _ hmid (by linarith)).1
      have h2 := (hxh.2.2 _ hmid (by linarith)).1
      linarith
  subst hxheq
  have hxhxs : xh' < xs := lt_of_lt_of_le hxh'lt (min_le_left _ _)
  have hxhzs : xh' < zs := lt_of_lt_of_le hxh'lt (min_le_right _ _)
  obtain ⟨hθI, hz2I, hθz2, hI35, hJ36⟩ := hA5
  -- φ' < 0
  have hφ'ne : ∀ x ∈ m.I, deriv S.φ x ≠ 0 := by
    intro x hx h0
    have hnp : ∀ y ∈ m.I, deriv S.φ y ≤ 0 := by
      intro y hy
      have := (hS.φ_strictAnti.antitoneOn).derivWithin_nonpos (x := y)
      rwa [derivWithin_of_isOpen hIo hy] at this
    have hmax : IsLocalMax (deriv S.φ) x := by
      have : ∀ᶠ y in 𝓝 x, deriv S.φ y ≤ deriv S.φ x := by
        filter_upwards [hIo.mem_nhds hx] with y hy
        rw [h0]; exact hnp y hy
      exact this
    have h2 := hmax.deriv_eq_zero
    have hode := hS.φ_ode x hx
    unfold gen at hode
    rw [h2, h0] at hode
    have := hS.φ_pos x hx
    have := hS.r_pos
    nlinarith
  have hφ'neg : ∀ x ∈ m.I, deriv S.φ x < 0 := by
    intro x hx
    have := (hS.φ_strictAnti.antitoneOn).derivWithin_nonpos (x := x)
    rw [derivWithin_of_isOpen hIo hx] at this
    exact lt_of_le_of_ne this (hφ'ne x hx)
  have hφc : ContinuousOn S.φ m.I := hS.φ_C2.continuousOn
  have hφ'c : ContinuousOn (deriv S.φ) m.I :=
    hS.φ_C2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hR'c : ContinuousOn (deriv (R m S m.π)) m.I :=
    hS.Rπ_C2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hIfc : ContinuousOn (Ifun m S) m.I := by
    unfold Ifun
    exact (hR'c.sub continuousOn_const).div hφ'c hφ'ne
  have hIφ : ∀ x ∈ m.I, Ifun m S x * deriv S.φ x = deriv (R m S m.π) x - m.k := by
    intro x hx; unfold Ifun; field_simp [hφ'ne x hx]
  -- monotonicity of I around x̂
  have hIanti : StrictAntiOn (Ifun m S) (m.I ∩ Iic xh') := by
    apply strictAntiOn_of_deriv_neg (hIconv.inter (convex_Iic _)) (hIfc.mono inter_subset_left)
    intro x hx
    rw [interior_inter, hIo.interior_eq, interior_Iic] at hx
    exact (hxh'pt.2.1 x hx.1 hx.2).1
  have hImono : StrictMonoOn (Ifun m S) (m.I ∩ Ici xh') := by
    apply strictMonoOn_of_deriv_pos (hIconv.inter (convex_Ici _)) (hIfc.mono inter_subset_left)
    intro x hx
    rw [interior_inter, hIo.interior_eq, interior_Ici] at hx
    exact (hxh'pt.2.2 x hx.1 hx.2).1
  have hImid : ∀ x ∈ m.I, θ < x → x < z2 → Ifun m S x < Ifun m S θ := by
    intro x hx h1 h2
    by_cases hxx : x ≤ xh'
    · exact hIanti ⟨hθI, hθ.le⟩ ⟨hx, hxx⟩ h1
    · rw [← hI35]; exact hImono ⟨hx, (le_of_not_ge hxx)⟩ ⟨hz2I, hz2.le⟩ h2
  have hIright : ∀ x ∈ m.I, z2 < x → Ifun m S θ < Ifun m S x := by
    intro x hx h1
    rw [← hI35]; exact hImono ⟨hz2I, hz2.le⟩ ⟨hx, hz2.le.trans h1.le⟩ h1
  have hIθ : Ifun m S θ < 0 := (hpart2 θ hθI).1 (hθ.trans hxhzs)
  set α : ℝ := -Ifun m S θ with hα
  have hαpos : 0 < α := by linarith
  set F : ℝ → ℝ := fun y => α * S.φ y + R m S m.π y with hF
  have hFC2 : ContDiffOn ℝ 2 F m.I := (contDiffOn_const.mul hS.φ_C2).add hS.Rπ_C2
  have hFd : ∀ x ∈ m.I, HasDerivAt F (α * deriv S.φ x + deriv (R m S m.π) x) x := by
    intro x hx
    have h1 : HasDerivAt S.φ (deriv S.φ x) x :=
      ((hS.φ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have h2 : HasDerivAt (R m S m.π) (deriv (R m S m.π) x) x :=
      ((hS.Rπ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    exact (h1.const_mul α).add h2
  have hF'eq : ∀ x ∈ m.I, deriv F x - m.k = deriv S.φ x * (Ifun m S x - Ifun m S θ) := by
    intro x hx
    rw [(hFd x hx).deriv, hα]
    linear_combination -(hIφ x hx)
  have hF'θ : deriv F θ = m.k := by have := hF'eq θ hθI; simp at this; linarith
  -- the value at θ
  have hJ' := hJ36
  unfold Jfun at hJ'
  rw [hI35] at hJ'
  have hVθ : -Ifun m S θ * S.φ z2 + R m S m.π z2 - m.k * (z2 - θ) - c2 = F θ := by
    simp only [hF, hα]; linarith
  have hVle : ∀ x, x ≤ θ → Vhat2 m S c2 θ z2 x = F θ + m.k * (x - θ) := by
    intro x hx
    simp only [Vhat2, if_pos hx]
    linarith
  have hVgt : ∀ x, θ < x → Vhat2 m S c2 θ z2 x = F x := by
    intro x hx
    simp only [Vhat2, if_neg (not_le.mpr hx), hF, hα]
  have hVge : ∀ x, θ ≤ x → Vhat2 m S c2 θ z2 x = F x := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · subst h; rw [hVle _ le_rfl]; ring
    · exact hVgt x h
  set V : ℝ → ℝ := Vhat2 m S c2 θ z2 with hVdef
  set A : ℝ → ℝ := fun y => F θ + m.k * (y - θ) with hAdef
  have hAd : ∀ y, HasDerivAt A m.k y := by
    intro y
    have := ((hasDerivAt_id y).sub_const θ).const_mul m.k
    simpa [hAdef] using this.const_add (F θ)
  have hVA : ∀ y, y < θ → V =ᶠ[𝓝 y] A := by
    intro y hy
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact hVle z (le_of_lt hz)
  have hVF : ∀ y, θ < y → V =ᶠ[𝓝 y] F := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact hVgt z hz
  set D : ℝ → ℝ := fun y => deriv F (max y θ) with hDdef
  have hVd : ∀ y ∈ m.I, HasDerivAt V (D y) y := by
    intro y hy
    rcases lt_trichotomy y θ with h | h | h
    · have hD : D y = m.k := by simp only [hDdef, max_eq_right h.le, hF'θ]
      rw [hD]; exact (hAd y).congr_of_eventuallyEq (hVA y h)
    · subst h
      have hD : D y = m.k := by simp only [hDdef, max_self, hF'θ]
      rw [hD]
      have h1 : HasDerivWithinAt V m.k (Iic y) y := by
        refine ((hAd y).hasDerivWithinAt).congr (fun z hz => hVle z hz) (hVle y le_rfl)
      have h2 : HasDerivWithinAt V m.k (Ici y) y := by
        rw [← hF'θ, (hFd y hy).deriv]
        exact ((hFd y hy).hasDerivWithinAt).congr (fun z hz => hVge z hz) (hVge y le_rfl)
      have := h1.union h2
      rw [Iic_union_Ici] at this
      exact this.hasDerivAt univ_mem
    · have hD : D y = deriv F y := by simp only [hDdef, max_eq_left h.le]
      rw [hD, (hFd y hy).deriv]
      exact ((hFd y hy).congr_of_eventuallyEq (hVF y h))
  have hF'c : ContinuousOn (deriv F) m.I := hFC2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hDc : ContinuousOn D m.I := by
    refine hF'c.comp (continuous_id.max continuous_const).continuousOn ?_
    intro y hy
    show max y θ ∈ m.I
    rcases le_total y θ with h | h
    · rw [max_eq_right h]; exact hθI
    · rw [max_eq_left h]; exact hy
  have hVdiff : DifferentiableOn ℝ V m.I := fun y hy => (hVd y hy).differentiableAt.differentiableWithinAt
  have hderivV : ∀ y ∈ m.I, deriv V y = D y := fun y hy => (hVd y hy).deriv
  have hVC1 : ContDiffOn ℝ 1 V m.I := by
    have := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0) (f := V) hIo).mpr
      ⟨hVdiff, by simp, contDiffOn_zero.mpr (hDc.congr (fun y hy => hderivV y hy))⟩
    simpa using this
  have hVC2 : ContDiffOn ℝ 2 V (m.I \ {θ}) := by
    intro y hy
    have hyI := hy.1
    have hyne : y ≠ θ := hy.2
    apply ContDiffAt.contDiffWithinAt
    rcases lt_or_gt_of_ne hyne with h | h
    · have : ContDiffAt ℝ 2 A y := by
        simp only [hAdef]; fun_prop
      exact this.congr_of_eventuallyEq (hVA y h)
    · exact (hFC2.contDiffAt (hIo.mem_nhds hyI)).congr_of_eventuallyEq (hVF y h)
  have hVc : ContinuousOn V m.I := hVdiff.continuousOn
  have hRc : ContinuousOn (R m S m.π) m.I := hS.Rπ_C2.continuousOn
  obtain ⟨hzsI, hA2s⟩ := hA2
  -- V > Rπ
  have hRV : ∀ x ∈ m.I, R m S m.π x < V x := by
    have hθpos : 0 < α * S.φ θ := mul_pos hαpos (hS.φ_pos θ hθI)
    have hanti : StrictAntiOn (fun y => V y - R m S m.π y) (m.I ∩ Iic θ) := by
      apply strictAntiOn_of_deriv_neg (hIconv.inter (convex_Iic _))
        ((hVc.sub hRc).mono inter_subset_left)
      intro y hy
      rw [interior_inter, hIo.interior_eq, interior_Iic] at hy
      have hy2 : y < θ := hy.2
      have hRd : HasDerivAt (R m S m.π) (deriv (R m S m.π) y) y :=
        ((hS.Rπ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hy.1)).hasDerivAt
      rw [((hVd y hy.1).sub hRd).deriv]
      have hD : D y = m.k := by simp only [hDdef, max_eq_right hy2.le, hF'θ]
      rw [hD]
      have := ((hA2s y hy.1).1 (by linarith))
      linarith
    intro x hx
    rcases le_or_gt θ x with h | h
    · rw [hVge x h]; simp only [hF]
      have := mul_pos hαpos (hS.φ_pos x hx); linarith
    · have h1 := hanti ⟨hx, show x ≤ θ from h.le⟩ ⟨hθI, show θ ≤ θ from le_rfl⟩ h
      simp only at h1
      rw [hVge θ le_rfl] at h1
      simp only [hF] at h1
      linarith
  -- gen F = α gen φ + gen Rπ
  have hgenF : ∀ x ∈ m.I, gen m F x + m.π x = α * gen m S.φ x := by
    intro x hx
    have hφ1 : HasDerivAt (deriv S.φ) (deriv (deriv S.φ) x) x :=
      (((hS.φ_C2.deriv_of_isOpen hIo (m := 1) (by norm_num)).differentiableOn
        (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hR1 : HasDerivAt (deriv (R m S m.π)) (deriv (deriv (R m S m.π)) x) x :=
      (((hS.Rπ_C2.deriv_of_isOpen hIo (m := 1) (by norm_num)).differentiableOn
        (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hev : deriv F =ᶠ[𝓝 x] fun z => α * deriv S.φ z + deriv (R m S m.π) z := by
      filter_upwards [hIo.mem_nhds hx] with z hz
      exact (hFd z hz).deriv
    have h2 : deriv (deriv F) x = α * deriv (deriv S.φ) x + deriv (deriv (R m S m.π)) x := by
      rw [hev.deriv_eq]; exact ((hφ1.const_mul α).add hR1).deriv
    have hode := hS.Rπ_ode x hx
    unfold gen at hode ⊢
    rw [h2, (hFd x hx).deriv]
    simp only [hF]
    linear_combination hode
  have hgenVgt : ∀ x ∈ m.I, θ < x → gen m V x + m.π x = 0 := by
    intro x hx h
    have h1 : deriv V x = deriv F x := (hVF x h).deriv_eq
    have h2 : deriv (deriv V) x = deriv (deriv F) x := (hVF x h).deriv.deriv_eq
    have h3 : V x = F x := hVgt x h
    have := hgenF x hx
    rw [hS.φ_ode x hx, mul_zero] at this
    unfold gen at this ⊢
    rw [h1, h2, h3]; exact this
  -- F''(θ) ≥ 0
  have hF'C1 : ContDiffOn ℝ 1 (deriv F) m.I := hFC2.deriv_of_isOpen hIo (by norm_num)
  have hF''c : ContinuousOn (deriv (deriv F)) m.I :=
    hF'C1.continuousOn_deriv_of_isOpen hIo le_rfl
  have hF''θ : 0 ≤ deriv (deriv F) θ := by
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (((hF''c.continuousAt (hIo.mem_nhds hθI)).eventually (gt_mem_nhds hneg)).and
        (hIo.mem_nhds hθI))
    set w := θ + min (ε / 2) ((z2 - θ) / 2) with hw
    have hm1 : 0 < min (ε / 2) ((z2 - θ) / 2) := lt_min (by linarith) (by linarith)
    have hm2 : min (ε / 2) ((z2 - θ) / 2) ≤ ε / 2 := min_le_left _ _
    have hm3 : min (ε / 2) ((z2 - θ) / 2) ≤ (z2 - θ) / 2 := min_le_right _ _
    have hsub : Icc θ w ⊆ Metric.ball θ ε := by
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
    have hsubI : Icc θ w ⊆ m.I := fun y hy => (hball (hsub hy)).2
    have hanti : StrictAntiOn (deriv F) (Icc θ w) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hF'C1.continuousOn.mono hsubI)
      intro y hy
      rw [interior_Icc] at hy
      exact (hball (hsub (Ioo_subset_Icc_self hy))).1
    have h1 := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (show θ < w by linarith)
    have hwI : w ∈ m.I := hsubI ⟨by linarith, le_rfl⟩
    have h2 := hF'eq w hwI
    have h3 := hImid w hwI (by linarith) (by linarith)
    have h4 := hφ'neg w hwI
    have : 0 < deriv S.φ w * (Ifun m S w - Ifun m S θ) := mul_pos_of_neg_of_neg h4 (by linarith)
    linarith
  have hkeyθ : m.π θ + m.μ θ * m.k - m.r * F θ ≤ 0 := by
    have := hgenF θ hθI
    rw [hS.φ_ode θ hθI, mul_zero] at this
    unfold gen at this
    rw [hF'θ] at this
    have hσ := hS.σ_pos θ hθI
    have : 0 ≤ 1 / 2 * m.σ θ ^ 2 * deriv (deriv F) θ := by positivity
    linarith
  -- q strictly increasing below x*
  obtain ⟨hqC1, hxsI, hq'pos, -, -, -, -⟩ := hA4
  have hqmono : StrictMonoOn (q m) (m.I ∩ Iic xs) := by
    apply strictMonoOn_of_deriv_pos (hIconv.inter (convex_Iic _))
      (hqC1.continuousOn.mono inter_subset_left)
    intro y hy
    rw [interior_inter, hIo.interior_eq, interior_Iic] at hy
    exact hq'pos y hy.1 hy.2
  have hgenVlt : ∀ x ∈ m.I, x < θ → gen m V x + m.π x < 0 := by
    intro x hx h
    have hAderiv : deriv A = fun _ => m.k := funext fun y => (hAd y).deriv
    have h1 : deriv V x = m.k := by rw [(hVA x h).deriv_eq, hAderiv]
    have h2 : deriv (deriv V) x = 0 := by
      rw [(hVA x h).deriv.deriv_eq, hAderiv, deriv_const]
    have h3 : V x = F θ + m.k * (x - θ) := hVle x h.le
    unfold gen
    rw [h1, h2, h3]
    have hq := hqmono ⟨hx, (h.trans (hθ.trans hxhxs)).le⟩ ⟨hθI, (hθ.trans hxhxs).le⟩ h
    unfold q at hq
    nlinarith
  -- G = V - k·id
  set G : ℝ → ℝ := fun y => V y - m.k * y with hGdef
  have hGd : ∀ y ∈ m.I, HasDerivAt G (D y - m.k) y := by
    intro y hy
    have h1 : HasDerivAt (fun z => m.k * z) (m.k * 1) y := (hasDerivAt_id y).const_mul m.k
    rw [mul_one] at h1
    exact (hVd y hy).sub h1
  have hGc : ContinuousOn G m.I := fun y hy => (hGd y hy).continuousAt.continuousWithinAt
  have hsubθz2 : Icc θ z2 ⊆ m.I := hIc.out hθI hz2I
  have hGmono : StrictMonoOn G (Icc θ z2) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hGc.mono hsubθz2)
    intro y hy
    rw [interior_Icc] at hy
    have hyI := hsubθz2 (Ioo_subset_Icc_self hy)
    rw [(hGd y hyI).deriv]
    have hD : D y = deriv F y := by simp only [hDdef, max_eq_left hy.1.le]
    rw [hD, hF'eq y hyI]
    exact mul_pos_of_neg_of_neg (hφ'neg y hyI) (by linarith [hImid y hyI hy.1 hy.2])
  have hGanti : StrictAntiOn G (m.I ∩ Ici z2) := by
    apply strictAntiOn_of_deriv_neg (hIconv.inter (convex_Ici _)) (hGc.mono inter_subset_left)
    intro y hy
    rw [interior_inter, hIo.interior_eq, interior_Ici] at hy
    have hy2 : z2 < y := hy.2
    rw [(hGd y hy.1).deriv]
    have hD : D y = deriv F y := by simp only [hDdef, max_eq_left (hθz2.trans hy2).le]
    rw [hD, hF'eq y hy.1]
    exact mul_neg_of_neg_of_pos (hφ'neg y hy.1) (by linarith [hIright y hy.1 hy2])
  have hGz2 : G z2 = F z2 - m.k * z2 := by simp only [hGdef, hVgt z2 hθz2]
  have hFz2 : F z2 = -Ifun m S θ * S.φ z2 + R m S m.π z2 := by simp only [hF, hα]
  have hGle : ∀ y, y ≤ θ → G y = G z2 - c2 := by
    intro y hy
    simp only [hGdef] at hGz2 ⊢
    rw [hVle y hy, hGz2, hFz2]
    linarith
  have hGmax : ∀ y ∈ m.I, y ≠ z2 → G y < G z2 := by
    intro y hy hne
    rcases le_or_gt y θ with h1 | h1
    · rw [hGle y h1]; linarith
    · rcases lt_or_gt_of_ne hne with h2 | h2
      · exact hGmono ⟨h1.le, h2.le⟩ ⟨hθz2.le, le_rfl⟩ h2
      · exact hGanti ⟨hz2I, show z2 ≤ z2 from le_rfl⟩ ⟨hy, show z2 ≤ y from h2.le⟩ h2
  have hGlow : ∀ x ∈ m.I, x ≤ z2 → G z2 - c2 ≤ G x := by
    intro x hx h
    rcases le_or_gt x θ with h1 | h1
    · rw [hGle x h1]
    · have := hGmono.monotoneOn ⟨le_rfl, hθz2.le⟩ ⟨h1.le, h⟩ h1.le
      rw [hGle θ le_rfl] at this; exact this
  have hQVI : ∀ x ∈ m.I, ∀ ζ : ℝ, 0 ≤ ζ → x + ζ ∈ m.I → V (x + ζ) - m.k * ζ - c2 ≤ V x := by
    intro x hx ζ hζ hxζ
    have hG1 : G (x + ζ) ≤ G x + c2 → V (x + ζ) - m.k * ζ - c2 ≤ V x := by
      intro hh; simp only [hGdef] at hh; linarith
    apply hG1
    rcases le_or_gt x z2 with h | h
    · have h1 : G (x + ζ) ≤ G z2 := by
        by_cases he : x + ζ = z2
        · rw [he]
        · exact (hGmax _ hxζ he).le
      linarith [hGlow x hx h]
    · have := hGanti.antitoneOn ⟨hx, show z2 ≤ x from h.le⟩
        ⟨hxζ, show z2 ≤ x + ζ by linarith⟩ (by linarith)
      linarith
  refine ⟨hθI, hz2I, hVC2, hVC1, hRV, hgenVgt, hgenVlt, hQVI, ?_, ?_, ?_⟩
  · intro y hy hne
    have := hGmax y hy hne
    simpa [hGdef] using this
  · intro x hx h
    unfold gFun
    rw [if_pos (h.trans hθz2), hVgt z2 hθz2, hVle x h.le, hFz2]
    have := hGle θ le_rfl
    simp only [hGdef] at this hGz2
    rw [hVge θ le_rfl] at this
    rw [hGz2, hFz2] at this
    linarith
  · refine ⟨α, hαpos, fun x hx h => ?_⟩
    rw [hVge x h]; simp only [hF]; ring
-- 
