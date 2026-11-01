-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.theorem_3_part_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:33:15.185138+00:00
-- url     : https://prove2.me/submissions/ebef2f9f-0fae-4913-83d0-0f4beb9c1cd0

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

/-- Elementary facts: `I`, `J` continuous on `I`, `θ* < x̂ < z₂`, `I` strictly increasing and
`J` strictly decreasing on `[x̂, z₂]`. -/
lemma icg_part_i_aux {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 θ z2 xh : ℝ)
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
    ∃ chat : ℝ, c2 < chat ∧ ∀ c1 ∈ Ioo c2 chat, ∃ z1 ∈ Ico xh z2,
      Jfun m S z1 - Jfun m S θ = c1 ∧ 0 < qB22 m S θ z1 z2 ∧ qB22 m S θ z1 z2 < 1 := by
  obtain ⟨hIc, hJc, hθxh, hxhz2, hImono, hJanti⟩ := icg_part_i_aux m S c2 θ z2 xh hS hA5 hxh
  obtain ⟨hθI, hz2I, hθz2, hI35, hJ36⟩ := hA5
  have hIo : IsOpen m.I := hS.I_open
  have hk := hS.k_pos
  set ε : ℝ := c2 + m.k * (z2 - θ) with hε
  have hεpos : 0 < ε := by have : 0 < m.k * (z2 - θ) := mul_pos hk (by linarith); linarith
  set K : ℝ := |S.φ θ - S.φ z2| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  have hcont : ContinuousAt (Ifun m S) z2 := hIc.continuousAt (hIo.mem_nhds hz2I)
  obtain ⟨δ, hδ, hδI⟩ := Metric.continuousAt_iff.mp hcont (ε / (K + 1)) (by positivity)
  set w : ℝ := max xh (z2 - δ / 2) with hw
  have hxhw : xh ≤ w := le_max_left _ _
  have hww : z2 - δ / 2 ≤ w := le_max_right _ _
  have hwz2 : w < z2 := max_lt hxhz2 (by linarith)
  have hwmem : w ∈ Icc xh z2 := ⟨hxhw, hwz2.le⟩
  have hz2mem : z2 ∈ Icc xh z2 := ⟨hxhz2.le, le_rfl⟩
  have hJw : Jfun m S z2 < Jfun m S w := hJanti hwmem hz2mem hwz2
  refine ⟨Jfun m S w - Jfun m S θ, by linarith, ?_⟩
  intro c1 hc1
  obtain ⟨hc1a, hc1b⟩ := hc1
  have hIcc : Icc w z2 ⊆ Icc xh z2 := Icc_subset_Icc hxhw le_rfl
  have hsubI : Icc xh z2 ⊆ m.I := hS.I_ordConnected.out hxh.1 hz2I
  have hJc' : ContinuousOn (Jfun m S) (Icc w z2) := hJc.mono (hIcc.trans hsubI)
  obtain ⟨z1, hz1mem, hz1J⟩ := intermediate_value_Icc' hwz2.le hJc'
    (show Jfun m S θ + c1 ∈ Icc (Jfun m S z2) (Jfun m S w) from ⟨by linarith, by linarith⟩)
  have hz1ne : z1 ≠ z2 := by
    rintro rfl; linarith
  have hz1z2 : z1 < z2 := lt_of_le_of_ne hz1mem.2 hz1ne
  have hz1xh : xh ≤ z1 := hxhw.trans hz1mem.1
  refine ⟨z1, ⟨hz1xh, hz1z2⟩, by linarith, ?_⟩
  have hd : Ifun m S z1 < Ifun m S z2 := hImono ⟨hz1xh, hz1z2.le⟩ hz2mem hz1z2
  have hdist : dist z1 z2 < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz1mem.1]
  have hsmall := hδI hdist
  rw [Real.dist_eq, abs_lt] at hsmall
  set d : ℝ := Ifun m S θ - Ifun m S z1 with hdd
  have hdpos : 0 < d := by rw [hdd, ← hI35]; linarith
  have hdlt : d < ε / (K + 1) := by rw [hdd, ← hI35]; linarith [hsmall.1]
  have hφθ : 0 < S.φ θ := hS.φ_pos θ hθI
  have hφz2 : 0 < S.φ z2 := hS.φ_pos z2 hz2I
  have hden : -Ifun m S z1 * S.φ z2 + R m S m.π z2 + Ifun m S θ * S.φ θ - R m S m.π θ
      = S.φ z2 * d + ε := by
    unfold Jfun at hJ36
    rw [hdd, hε]
    rw [hI35] at hJ36
    linear_combination hJ36
  have hDpos : 0 < S.φ z2 * d + ε := by positivity
  unfold qB22
  rw [hden]
  constructor
  · exact div_pos (mul_pos hφθ hdpos) hDpos
  · rw [div_lt_one hDpos]
    have h1 : (S.φ θ - S.φ z2) * d ≤ K * d :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hdpos.le
    have h2 : K * d ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hdlt.le hKnn
    have h3 : K * (ε / (K + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    nlinarith
