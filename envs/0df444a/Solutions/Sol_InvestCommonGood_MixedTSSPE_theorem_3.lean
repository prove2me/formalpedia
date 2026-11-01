-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:30:18.603088+00:00
-- url     : https://prove2.me/submissions/35cf3a95-7fa6-44c5-b0f0-866567d42521
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_2
import Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_3_part_i
import Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_3_part_ii
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_8

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) :
    ∃ chat : ℝ, c2 < chat ∧ ∀ c1 ∈ Ioo c2 chat, ∃ z1 q : ℝ, ∃ U1 V1 V2 : ℝ → ℝ,
      0 < q ∧ q < 1 ∧ (∃ xh : ℝ, IsLemma2Point m S xh ∧ θ < xh ∧ xh < z1) ∧ z1 < z2 ∧
      Sec42 m S ![c1, c2] θ ![z1, z2] q U1 V1 V2 ∧
      ∀ Rd : InvestCommonGood.MixedTSSPE.Rand Ω, RandStanding S Rd →
        IsSPE m S Rd ![c1, c2] θ q ![z1, z2] (rate29 m ![U1, V2] ![c1, c2] ![z1, z2] θ) := by
  obtain ⟨⟨xh, hxh, -⟩, -⟩ := lemma_2 m S zs xs hS hA1 hA2 hA4
  obtain ⟨hθI, hz2I, hθz2, hI35, hJ36⟩ := hA5
  have hIo : IsOpen m.I := hS.I_open
  -- deriv φ never vanishes on I
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
  -- continuity of I and J on I
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
  -- θ < xh
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
  -- xh < z2
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
  -- J(xh) > J(z2)
  have hJ : Jfun m S z2 < Jfun m S xh := by
    have hanti : StrictAntiOn (Jfun m S) (Icc xh z2) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hJc.mono (hsub _ _ hxhI hz2I))
      intro x hx
      rw [interior_Icc] at hx
      exact (hxh.2.2 x (hsub _ _ hxhI hz2I (Ioo_subset_Icc_self hx)) hx.1).2
    exact hanti ⟨le_rfl, hxhz2.le⟩ ⟨hxhz2.le, le_rfl⟩ hxhz2
  have hA5' : Assumption5 m S c2 θ z2 := ⟨hθI, hz2I, hθz2, hI35, hJ36⟩
  obtain ⟨ch1, hch1, H1⟩ := theorem_3_part_i m S c2 zs xs θ z2 xh hS hc2 hA1 hA2 hA4 hA5' hxh
  obtain ⟨ch2, hch2, H2⟩ := theorem_3_part_ii m S c2 zs xs θ z2 xh hS hc2 hA1 hA2 hA4 hA5' hxh
  refine ⟨min (min ch1 ch2) (Jfun m S xh - Jfun m S θ), ?_, ?_⟩
  · refine lt_min (lt_min hch1 hch2) ?_
    linarith
  intro c1 hc1
  have hc1a : c1 < ch1 := lt_of_lt_of_le hc1.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hc1b : c1 < ch2 := lt_of_lt_of_le hc1.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hc1c : c1 < Jfun m S xh - Jfun m S θ := lt_of_lt_of_le hc1.2 (min_le_right _ _)
  obtain ⟨z1, hz1, hB21, hq0, hq1⟩ := H1 c1 ⟨hc1.1, hc1a⟩
  have hB23 := H2 c1 ⟨hc1.1, hc1b⟩ z1 hz1 hB21
  have hxhz1 : xh < z1 := by
    rcases eq_or_lt_of_le hz1.1 with h | h
    · subst h; linarith
    · exact h
  obtain ⟨U1, V1, V2, hSec, hSPE⟩ := lemma_B_8 m S c1 c2 zs xs θ z1 z2 xh (qB22 m S θ z1 z2)
    hS hc2 hc1.1 hA1 hA2 hA4 hA5' hxh hq0 hq1 hθxh hxhz1 hz1.2 hB21 rfl hB23
  exact ⟨z1, qB22 m S θ z1 z2, U1, V1, V2, hq0, hq1, ⟨xh, hxh, hθxh, hxhz1⟩, hz1.2, hSec, hSPE⟩
