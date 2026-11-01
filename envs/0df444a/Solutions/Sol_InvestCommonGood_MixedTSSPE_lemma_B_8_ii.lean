-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.lemma_B_8_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:58:10.668484+00:00
-- url     : https://prove2.me/submissions/471d880f-be54-497b-a7b4-b1297c42ac67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_2
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_8_i

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c1 c2 zs xs θ z1 z2 xh q : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hc2 : 0 < c2) (hc12 : c2 < c1) (hA1 : Assumption1 m S)
    (hA2 : Assumption2 m S zs) (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2)
    (hxh : IsLemma2Point m S xh) (hq0 : 0 < q) (hq1 : q < 1)
    (hθ : θ < xh) (hz1 : xh < z1) (hz12 : z1 < z2)
    (hB21 : Jfun m S z1 - Jfun m S θ = c1) (hB22 : qB22 m S θ z1 z2 = q)
    (hB23 : B23 m S θ z1) :
    Sec42 m S ![c1, c2] θ ![z1, z2] q
      (Uhat1 m S c1 θ z1) (Vhat1 m S c1 θ z1) (Vhat2 m S c2 θ z2) := by
  have hz2 : xh < z2 := hz1.trans hz12
  have hV2 := lemma_B_8_i m S c2 zs xs θ z2 xh hS hc2 hA1 hA2 hA4 hA5 hxh hθ hz2
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
  obtain ⟨hzsI, hA2s⟩ := hA2
  have hV2full := hV2
  obtain ⟨-, -, hV2C2, hV2C1, hV2R, hV2gen1, hV2gen2, hV2qvi, -, -, -⟩ := hV2
  have hz1I : z1 ∈ m.I := hIc.out hθI hz2I ⟨(hθ.trans hz1).le, hz12.le⟩
  have hθz1 : θ < z1 := hθ.trans hz1
  -- key identities from (35), (36), (B.21)
  have hJ' := hJ36
  unfold Jfun at hJ'
  rw [hI35] at hJ'
  have hB21' := hB21
  unfold Jfun at hB21'
  -- V̂₁ = V̂₂
  have hVeq : Vhat1 m S c1 θ z1 = Vhat2 m S c2 θ z2 := by
    funext x
    unfold Vhat1 Vhat2
    rcases lt_trichotomy x θ with h | h | h
    · rw [if_pos h, if_pos h.le]; linarith
    · subst h; rw [if_neg (lt_irrefl _), if_pos le_rfl]; linarith
    · rw [if_neg (not_lt.mpr h.le), if_neg (not_le.mpr h)]
  set α : ℝ := -Ifun m S θ with hα
  set β : ℝ := -Ifun m S z1 with hβ
  have hIz1θ : Ifun m S z1 < Ifun m S θ := by
    rw [← hI35]; exact hImono ⟨hz1I, hz1.le⟩ ⟨hz2I, hz2.le⟩ hz12
  have hαβ : α < β := by simp only [hα, hβ]; linarith
  have hIθ : Ifun m S θ < 0 := (hpart2 θ hθI).1 (hθ.trans hxhzs)
  have hαpos : 0 < α := by linarith
  set U : ℝ → ℝ := Uhat1 m S c1 θ z1 with hUdef
  set V : ℝ → ℝ := Vhat2 m S c2 θ z2 with hVdef
  set H : ℝ → ℝ := fun y => β * S.φ y + R m S m.π y with hHdef
  set F : ℝ → ℝ := fun y => α * S.φ y + R m S m.π y with hFdef
  have hUge : ∀ x, θ ≤ x → U x = H x := by
    intro x hx; simp only [hUdef, Uhat1, if_neg (not_lt.mpr hx), hHdef, hβ]
  have hUlt : ∀ x, x < θ → U x = H z1 - m.k * (z1 - x) - c1 := by
    intro x hx; simp only [hUdef, Uhat1, if_pos hx, hHdef, hβ]
  have hVge : ∀ x, θ ≤ x → V x = F x := by
    intro x hx
    rw [← hVeq]
    simp only [Vhat1, if_neg (not_lt.mpr hx), hFdef, hα]
  have hVlt : ∀ x, x < θ → V x = H z1 - m.k * (z1 - x) - c1 := by
    intro x hx
    rw [← hVeq]
    simp only [Vhat1, if_pos hx, hHdef, hβ]
  -- H z1 - k z1 - c1 = F θ - k θ   (B.21)
  have hHF : H z1 - m.k * z1 - c1 = F θ - m.k * θ := by
    simp only [hHdef, hFdef, hα, hβ]; linarith
  have hφ1 : ∀ x ∈ m.I, HasDerivAt S.φ (deriv S.φ x) x := fun x hx =>
    ((hS.φ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
  have hR1 : ∀ x ∈ m.I, HasDerivAt (R m S m.π) (deriv (R m S m.π) x) x := fun x hx =>
    ((hS.Rπ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
  have hHd : ∀ x ∈ m.I, HasDerivAt H (β * deriv S.φ x + deriv (R m S m.π) x) x :=
    fun x hx => ((hφ1 x hx).const_mul β).add (hR1 x hx)
  have hFd : ∀ x ∈ m.I, HasDerivAt F (α * deriv S.φ x + deriv (R m S m.π) x) x :=
    fun x hx => ((hφ1 x hx).const_mul α).add (hR1 x hx)
  have hH'eq : ∀ x ∈ m.I, deriv H x - m.k = deriv S.φ x * (Ifun m S x - Ifun m S z1) := by
    intro x hx; rw [(hHd x hx).deriv, hβ]; linear_combination -(hIφ x hx)
  have hF'eq : ∀ x ∈ m.I, deriv F x - m.k = deriv S.φ x * (Ifun m S x - Ifun m S θ) := by
    intro x hx; rw [(hFd x hx).deriv, hα]; linear_combination -(hIφ x hx)
  have hHC2 : ContDiffOn ℝ 2 H m.I := (contDiffOn_const.mul hS.φ_C2).add hS.Rπ_C2
  have hHc : ContinuousOn H m.I := hHC2.continuousOn
  have hFc : ContinuousOn F m.I := ((contDiffOn_const.mul hS.φ_C2).add hS.Rπ_C2).continuousOn
  have hkpos := hS.k_pos
  set Hk : ℝ → ℝ := fun y => H y - m.k * y with hHkdef
  set Fk : ℝ → ℝ := fun y => F y - m.k * y with hFkdef
  have hHkd : ∀ y ∈ m.I, HasDerivAt Hk (deriv S.φ y * (Ifun m S y - Ifun m S z1)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z => m.k * z) (m.k * 1) y := (hasDerivAt_id y).const_mul m.k
    rw [mul_one] at h1
    have := (hHd y hy).sub h1
    rw [← (hHd y hy).deriv, hH'eq y hy] at this
    exact this
  have hFkd : ∀ y ∈ m.I, HasDerivAt Fk (deriv S.φ y * (Ifun m S y - Ifun m S θ)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z => m.k * z) (m.k * 1) y := (hasDerivAt_id y).const_mul m.k
    rw [mul_one] at h1
    have := (hFd y hy).sub h1
    rw [← (hFd y hy).deriv, hF'eq y hy] at this
    exact this
  have hHkc : ContinuousOn Hk m.I := fun y hy => (hHkd y hy).continuousAt.continuousWithinAt
  have hFkc : ContinuousOn Fk m.I := fun y hy => (hFkd y hy).continuousAt.continuousWithinAt
  have hsubθz2 : Icc θ z2 ⊆ m.I := hIc.out hθI hz2I
  have hFkmono : MonotoneOn Fk (Icc θ z2) := by
    apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) (hFkc.mono hsubθz2) ?_).monotoneOn
    intro y hy
    rw [interior_Icc] at hy
    have hyI := hsubθz2 (Ioo_subset_Icc_self hy)
    rw [(hFkd y hyI).deriv]
    exact mul_pos_of_neg_of_neg (hφ'neg y hyI) (by linarith [hImid y hyI hy.1 hy.2])
  have hHkanti : StrictAntiOn Hk (m.I ∩ Ici z1) := by
    apply strictAntiOn_of_deriv_neg (hIconv.inter (convex_Ici _)) (hHkc.mono inter_subset_left)
    intro y hy
    rw [interior_inter, hIo.interior_eq, interior_Ici] at hy
    have hy2 : z1 < y := hy.2
    rw [(hHkd y hy.1).deriv]
    have : Ifun m S z1 < Ifun m S y := hImono ⟨hz1I, hz1.le⟩ ⟨hy.1, (hz1.trans hy2).le⟩ hy2
    exact mul_neg_of_neg_of_pos (hφ'neg y hy.1) (by linarith)
  have hsubxhz1 : Icc xh' z1 ⊆ m.I := hIc.out hxhI hz1I
  have hHkmono : StrictMonoOn Hk (Icc xh' z1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hHkc.mono hsubxhz1)
    intro y hy
    rw [interior_Icc] at hy
    have hyI := hsubxhz1 (Ioo_subset_Icc_self hy)
    rw [(hHkd y hyI).deriv]
    have : Ifun m S y < Ifun m S z1 := hImono ⟨hyI, hy.1.le⟩ ⟨hz1I, hz1.le⟩ hy.2
    exact mul_pos_of_neg_of_neg (hφ'neg y hyI) (by linarith)
  have hB23' : Hk θ < Hk z1 := by
    unfold B23 Jfun at hB23
    simp only [hHkdef, hHdef, hβ]; linarith
  have hHkleft : ∀ y, θ ≤ y → y < z1 → Hk y < Hk z1 := by
    intro y h1 h2
    have hyI : y ∈ m.I := hIc.out hθI hz1I ⟨h1, h2.le⟩
    by_cases hyx : xh' ≤ y
    · exact hHkmono ⟨hyx, h2.le⟩ ⟨hz1.le, le_rfl⟩ h2
    · rw [not_le] at hyx
      by_cases hIy : Ifun m S z1 ≤ Ifun m S y
      · have hsub : Icc θ y ⊆ m.I := hIc.out hθI hyI
        have hanti : AntitoneOn Hk (Icc θ y) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hHkc.mono hsub)
            (fun z hz => (hHkd z (hsub (interior_subset hz))).differentiableAt.differentiableWithinAt)
          intro z hz
          rw [interior_Icc] at hz
          have hzI := hsub (Ioo_subset_Icc_self hz)
          rw [(hHkd z hzI).deriv]
          have : Ifun m S y ≤ Ifun m S z := (hIanti ⟨hzI, (hz.2.trans hyx).le⟩ ⟨hyI, hyx.le⟩ hz.2).le
          exact mul_nonpos_of_nonpos_of_nonneg (hφ'neg z hzI).le (by linarith)
        have := hanti ⟨le_rfl, h1⟩ ⟨h1, le_rfl⟩ h1
        linarith
      · rw [not_le] at hIy
        have hsub : Icc y xh' ⊆ m.I := hIc.out hyI hxhI
        have hmono : MonotoneOn Hk (Icc y xh') := by
          apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) (hHkc.mono hsub) ?_).monotoneOn
          intro z hz
          rw [interior_Icc] at hz
          have hzI := hsub (Ioo_subset_Icc_self hz)
          rw [(hHkd z hzI).deriv]
          have : Ifun m S z < Ifun m S y := hIanti ⟨hyI, hyx.le⟩ ⟨hzI, hz.2.le⟩ hz.1
          exact mul_pos_of_neg_of_neg (hφ'neg z hzI) (by linarith)
        have h3 := hmono ⟨le_rfl, hyx.le⟩ ⟨hyx.le, le_rfl⟩ hyx.le
        have h4 := hHkmono ⟨le_rfl, hz1.le⟩ ⟨hz1.le, le_rfl⟩ hz1
        linarith
  -- U - k·id
  have hGU : ∀ y, U y - m.k * y = if y < θ then Hk z1 - c1 else Hk y := by
    intro y
    split_ifs with h
    · rw [hUlt y h]; simp only [hHkdef]; ring
    · rw [hUge y (not_lt.mp h)]
  have hGUmax : ∀ y ∈ m.I, y ≠ z1 → U y - m.k * y < U z1 - m.k * z1 := by
    intro y hy hne
    rw [hGU y, hGU z1, if_neg (not_lt.mpr hθz1.le)]
    split_ifs with h
    · linarith
    · rw [not_lt] at h
      rcases lt_or_gt_of_ne hne with h2 | h2
      · exact hHkleft y h h2
      · exact hHkanti ⟨hz1I, show z1 ≤ z1 from le_rfl⟩ ⟨hy, show z1 ≤ y from h2.le⟩ h2
  have hGUle : ∀ y ∈ m.I, U y - m.k * y ≤ Hk z1 := by
    intro y hy
    by_cases h : y = z1
    · subst h; rw [hGU, if_neg (not_lt.mpr hθz1.le)]
    · have := hGUmax y hy h
      rw [hGU z1, if_neg (not_lt.mpr hθz1.le)] at this
      linarith
  have hFkθ : Fk θ = Hk z1 - c1 := by simp only [hFkdef, hHkdef]; linarith
  have hFkz1 : Hk z1 - c1 ≤ Fk z1 := by
    rw [← hFkθ]; exact hFkmono ⟨le_rfl, hθz2.le⟩ ⟨hθz1.le, hz12.le⟩ hθz1.le
  have hQVIa : ∀ x ∈ m.I, ∀ ζ : ℝ, 0 ≤ ζ → x + ζ ∈ m.I → U (x + ζ) - m.k * ζ - c1 ≤ V x := by
    intro x hx ζ hζ hxζ
    have hG := hGUle (x + ζ) hxζ
    rcases lt_or_ge x θ with h | h
    · rw [hVlt x h]; simp only [hHkdef] at hG ⊢; linarith
    · rw [hVge x h]
      rcases le_or_gt x z1 with h2 | h2
      · have := hFkmono ⟨le_rfl, hθz2.le⟩ ⟨h, h2.trans hz12.le⟩ h
        rw [hFkθ] at this
        simp only [hFkdef] at this
        linarith
      · have h3 : U (x + ζ) - m.k * (x + ζ) ≤ Hk x := by
          rw [hGU, if_neg (by linarith)]
          exact hHkanti.antitoneOn ⟨hx, show z1 ≤ x from h2.le⟩
            ⟨hxζ, show z1 ≤ x + ζ by linarith⟩ (by linarith)
        have h4 : (β - α) * S.φ x ≤ (β - α) * S.φ z1 :=
          mul_le_mul_of_nonneg_left (hS.φ_strictAnti.antitoneOn hz1I hx h2.le) (by linarith)
        have h5 : (β - α) * S.φ z1 ≤ c1 := by
          simp only [hFkdef, hHkdef, hFdef, hHdef] at hFkz1; nlinarith
        simp only [hHkdef, hHdef, hFdef] at h3 ⊢
        nlinarith
  have hUV : ∀ x ∈ m.I, θ ≤ x → V x < U x := by
    intro x hxI hx
    rw [hVge x hx, hUge x hx]
    have := mul_lt_mul_of_pos_right hαβ (hS.φ_pos x hxI)
    simp only [hFdef, hHdef]; linarith
  rw [hVeq]
  simp only [Sec42, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- smoothness and generator of U
  have hUH : ∀ y, θ < y → U =ᶠ[𝓝 y] H := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact hUge z hz.le
  set A : ℝ → ℝ := fun y => H z1 - m.k * (z1 - y) - c1 with hAdef
  have hUA : ∀ y, y < θ → U =ᶠ[𝓝 y] A := by
    intro y hy
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact hUlt z hz
  have hUC2 : ContDiffOn ℝ 2 U (m.I \ {θ}) := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    rcases lt_or_gt_of_ne (show y ≠ θ from hy.2) with h | h
    · have : ContDiffAt ℝ 2 A y := by simp only [hAdef]; fun_prop
      exact this.congr_of_eventuallyEq (hUA y h)
    · exact (hHC2.contDiffAt (hIo.mem_nhds hy.1)).congr_of_eventuallyEq (hUH y h)
  have hgenU : ∀ x ∈ m.I, θ < x → gen m U x + m.π x = 0 := by
    intro x hx h
    have hφ2 : HasDerivAt (deriv S.φ) (deriv (deriv S.φ) x) x :=
      (((hS.φ_C2.deriv_of_isOpen hIo (m := 1) (by norm_num)).differentiableOn
        (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hR2 : HasDerivAt (deriv (R m S m.π)) (deriv (deriv (R m S m.π)) x) x :=
      (((hS.Rπ_C2.deriv_of_isOpen hIo (m := 1) (by norm_num)).differentiableOn
        (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hev : deriv H =ᶠ[𝓝 x] fun z => β * deriv S.φ z + deriv (R m S m.π) z := by
      filter_upwards [hIo.mem_nhds hx] with z hz
      exact (hHd z hz).deriv
    have h2 : deriv (deriv H) x = β * deriv (deriv S.φ) x + deriv (deriv (R m S m.π)) x := by
      rw [hev.deriv_eq]; exact ((hφ2.const_mul β).add hR2).deriv
    have e1 : deriv U x = deriv H x := (hUH x h).deriv_eq
    have e2 : deriv (deriv U) x = deriv (deriv H) x := (hUH x h).deriv.deriv_eq
    have e3 : U x = H x := hUge x h.le
    have hode := hS.Rπ_ode x hx
    have hodeφ := hS.φ_ode x hx
    unfold gen at hode hodeφ ⊢
    rw [e1, e2, e3, h2, (hHd x hx).deriv]
    simp only [hHdef]
    linear_combination hode + β * hodeφ
  -- (B.22)
  have hnum : H θ - F θ = S.φ θ * (Ifun m S θ - Ifun m S z1) := by
    simp only [hHdef, hFdef, hα, hβ]; ring
  have hden : H z2 - F θ =
      -Ifun m S z1 * S.φ z2 + R m S m.π z2 + Ifun m S θ * S.φ θ - R m S m.π θ := by
    simp only [hHdef, hFdef, hα, hβ]; ring
  have hnumpos : 0 < H θ - F θ := by
    rw [hnum]; exact mul_pos (hS.φ_pos θ hθI) (by linarith)
  have hqeq : q = (H θ - F θ) / (H z2 - F θ) := by
    rw [← hB22, hnum, hden]; rfl
  have hdenpos : 0 < H z2 - F θ := by
    by_contra hc
    rw [not_lt] at hc
    have : (H θ - F θ) / (H z2 - F θ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hnumpos.le hc
    linarith
  have hUθ : U θ = H θ := hUge θ le_rfl
  have hUz2 : U z2 = H z2 := hUge z2 hθz2.le
  have hUz1 : U z1 = H z1 := hUge z1 hθz1.le
  have hVθ : V θ = F θ := hVge θ le_rfl
  refine ⟨hV2full, hz1I, hUC2, hV2C2, hV2C1, hV2R, hUV, ?_, hV2gen1, hV2gen2, hgenU, hQVIa, ?_,
    hGUmax, ?_, ⟨α, β, hαpos, hαβ, fun x hx h => ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx h; rw [hUlt x h, hVlt x h]
  · intro x hx ζ hζ hxζ
    have := hQVIa x hx ζ hζ hxζ
    rcases lt_or_ge x θ with h | h
    · rw [hUlt x h]; rw [hVlt x h] at this; exact this
    · linarith [hUV x hx h]
  · intro x hx h
    unfold gFun
    rw [if_pos (h.trans hθz1), hUz1, hVlt x h]
  · rw [hVge x h, hUge x h]; simp only [hFdef, hHdef]; constructor <;> ring
  · rw [hUθ, hUz2, hVθ, hqeq]
    field_simp
    ring
  · rw [hVθ, hUz2]; linarith
  · unfold gFun
    rw [if_pos hθz1, hUz1, hVθ]
    simp only [hHkdef, hFkdef] at hFkθ
    linarith
  · intro x hx h
    unfold gFun
    rw [if_pos (h.trans hθz2), if_pos (h.trans hθz1), hUz2, hUz1]
    have hq2 := hV2qvi z1 hz1I (z2 - z1) (by linarith) (by rw [show z1 + (z2 - z1) = z2 by ring]; exact hz2I)
    rw [show z1 + (z2 - z1) = z2 by ring] at hq2
    have hFkθ' := hFkθ
    simp only [hHkdef, hFkdef] at hFkθ'
    have hk1 : 0 < m.k * (z1 - x) := mul_pos hkpos (by linarith)
    have hk2 : 0 < m.k * (θ - x) := mul_pos hkpos (by linarith)
    constructor
    · linarith
    · linarith
