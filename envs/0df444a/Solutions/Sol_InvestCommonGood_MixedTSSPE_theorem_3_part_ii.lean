-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.theorem_3_part_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:34:02.879129+00:00
-- url     : https://prove2.me/submissions/39fb47bc-9674-464e-9a29-a20fb8ff108b

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

/-- Elementary facts: `I`, `J` continuous on `I`, `θ* < x̂ < z₂`, `I` strictly increasing and
`J` strictly decreasing on `[x̂, z₂]`. -/
lemma icg_part_ii_aux {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 θ z2 xh : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hA5 : Assumption5 m S c2 θ z2)
    (hxh : IsLemma2Point m S xh) :
    ContinuousOn (Ifun m S) m.I ∧ ContinuousOn (Jfun m S) m.I ∧ θ < xh ∧ xh < z2 ∧
      StrictMonoOn (Ifun m S) (Icc xh z2) ∧ StrictAntiOn (Jfun m S) (Icc xh z2) := by
  obtain ⟨hθI, hz2I, hθz2, hI35, hJ36⟩ := hA5
  have hIo : IsOpen m.I := hS.I_open
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
  have hφc : ContinuousOn S.φ m.I := hS.φ_C2.continuousOn
  have hφ'c : ContinuousOn (deriv S.φ) m.I :=
    hS.φ_C2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hR'c : ContinuousOn (deriv (R m S m.π)) m.I :=
    hS.Rπ_C2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hRc : ContinuousOn (R m S m.π) m.I := hS.Rπ_C2.continuousOn
  have hIc : ContinuousOn (Ifun m S) m.I := by
    unfold Ifun
    exact (hR'c.sub continuousOn_const).div hφ'c hφ'ne
  have hJc : ContinuousOn (Jfun m S) m.I := by
    unfold Jfun
    exact (hRc.sub (continuousOn_const.mul continuousOn_id)).sub (hIc.mul hφc)
  have hxhI : xh ∈ m.I := hxh.1
  have hsub : ∀ u v, u ∈ m.I → v ∈ m.I → Icc u v ⊆ m.I := fun u v hu hv =>
    hS.I_ordConnected.out hu hv
  have hθxh : θ < xh := by
    by_contra hc
    rw [not_lt] at hc
    have hmono : StrictMonoOn (Ifun m S) (Icc xh z2) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hIc.mono (hsub _ _ hxhI hz2I))
      intro x hx
      rw [interior_Icc] at hx
      exact (hxh.2.2 x (hsub _ _ hxhI hz2I (Ioo_subset_Icc_self hx)) hx.1).1
    have := hmono ⟨hc, hθz2.le⟩ ⟨hc.trans hθz2.le, le_rfl⟩ hθz2
    linarith
  have hxhz2 : xh < z2 := by
    by_contra hc
    rw [not_lt] at hc
    have hanti : StrictAntiOn (Ifun m S) (Icc θ z2) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hIc.mono (hsub _ _ hθI hz2I))
      intro x hx
      rw [interior_Icc] at hx
      exact (hxh.2.1 x (hsub _ _ hθI hz2I (Ioo_subset_Icc_self hx)) (lt_of_lt_of_le hx.2 hc)).1
    have := hanti ⟨le_rfl, hθz2.le⟩ ⟨hθz2.le, le_rfl⟩ hθz2
    linarith
  refine ⟨hIc, hJc, hθxh, hxhz2, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hIc.mono (hsub _ _ hxhI hz2I))
    intro x hx
    rw [interior_Icc] at hx
    exact (hxh.2.2 x (hsub _ _ hxhI hz2I (Ioo_subset_Icc_self hx)) hx.1).1
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hJc.mono (hsub _ _ hxhI hz2I))
    intro x hx
    rw [interior_Icc] at hx
    exact (hxh.2.2 x (hsub _ _ hxhI hz2I (Ioo_subset_Icc_self hx)) hx.1).2

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 xh : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S)
    (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) (hxh : IsLemma2Point m S xh) :
    ∃ chat : ℝ, c2 < chat ∧ ∀ c1 ∈ Ioo c2 chat, ∀ z1 ∈ Ico xh z2,
      Jfun m S z1 - Jfun m S θ = c1 → B23 m S θ z1 := by
  obtain ⟨hIc, hJc, hθxh, hxhz2, hImono, hJanti⟩ := icg_part_ii_aux m S c2 θ z2 xh hS hA5 hxh
  obtain ⟨hθI, hz2I, hθz2, hI35, hJ36⟩ := hA5
  have hIo : IsOpen m.I := hS.I_open
  have hφθ : 0 < S.φ θ := hS.φ_pos θ hθI
  have hcont : ContinuousAt (Ifun m S) z2 := hIc.continuousAt (hIo.mem_nhds hz2I)
  obtain ⟨δ, hδ, hδI⟩ := Metric.continuousAt_iff.mp hcont (c2 / (S.φ θ + 1)) (by positivity)
  set w : ℝ := max xh (z2 - δ / 2) with hw
  have hxhw : xh ≤ w := le_max_left _ _
  have hww : z2 - δ / 2 ≤ w := le_max_right _ _
  have hwz2 : w < z2 := max_lt hxhz2 (by linarith)
  have hwmem : w ∈ Icc xh z2 := ⟨hxhw, hwz2.le⟩
  have hz2mem : z2 ∈ Icc xh z2 := ⟨hxhz2.le, le_rfl⟩
  have hJw : Jfun m S z2 < Jfun m S w := hJanti hwmem hz2mem hwz2
  refine ⟨Jfun m S w - Jfun m S θ, by linarith, ?_⟩
  intro c1 hc1 z1 hz1 hB21
  have hz1w : w < z1 := by
    by_contra hc
    rw [not_lt] at hc
    have : Jfun m S w ≤ Jfun m S z1 := hJanti.antitoneOn ⟨hz1.1, hc.trans hwz2.le⟩ hwmem hc
    linarith [hc1.2]
  have hdist : dist z1 z2 < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz1.2]
  have hsmall := hδI hdist
  rw [Real.dist_eq, abs_lt] at hsmall
  have hdlt : Ifun m S θ - Ifun m S z1 < c2 / (S.φ θ + 1) := by rw [← hI35]; linarith [hsmall.1]
  have hkey : (Ifun m S θ - Ifun m S z1) * S.φ θ < c1 := by
    have h1 : c2 / (S.φ θ + 1) * S.φ θ < c2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    have h2 : (Ifun m S θ - Ifun m S z1) * S.φ θ ≤ c2 / (S.φ θ + 1) * S.φ θ :=
      mul_le_mul_of_nonneg_right hdlt.le hφθ.le
    linarith [hc1.1]
  unfold B23
  unfold Jfun at hB21 ⊢
  nlinarith
