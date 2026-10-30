-- Prove2me | solution 1 for LLMThroughput.TokenBudget.proposition_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:09:25.901111+00:00
-- url     : https://prove2.me/submissions/e61e599f-ef48-460b-a512-1031dd455382

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model
import Definitions.Def_LLMThroughput_TokenBudget_Fluid

open LLMThroughput.TokenBudget
open Set Filter Topology MeasureTheory

theorem solution (P : Params) (hP : P.Valid) (lam mp md : ℝ) (hlam : 0 ≤ lam)
    (hmp : 0 < mp) (hmd : 0 < md)
    (hload : lam * (mp + md) < (P.bmax : ℝ) / (P.t P.bmax : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : FluidPath, IsWCFluidSolution lam mp md ((P.bmax : ℝ) / (P.t P.bmax : ℝ)) s →
        (∀ t, 0 ≤ t → 0 ≤ s.Zp t ∧ 0 ≤ s.Zd t) →
        s.Zp 0 + s.Zd 0 ≤ 1 →
        ∀ t, δ ≤ t → s.Zp t = 0 ∧ s.Zd t = 0 := by
  set κ : ℝ := (P.bmax : ℝ) / (P.t P.bmax : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ε := κ - lam * (mp + md) with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  refine ⟨(mp + md) / ε + 1, by positivity, ?_⟩
  intro s hs hnn h01 t ht
  obtain ⟨⟨h45, h46, hB0p, hB0d, hLp, hLd, h48, h49⟩, hWC⟩ := hs
  -- the Lyapunov function: total remaining work
  let W : ℝ → ℝ := fun u => (mp + md) * s.Zp u + md * s.Zd u
  have hW : ∀ u, 0 ≤ u → W u = W 0 + (mp + md) * lam * u - (s.Bp u + s.Bd u) := by
    intro u hu
    have e1 := h45 u hu
    have e2 := h46 u hu
    obtain ⟨e3, e4⟩ := h48 u hu
    simp only [W]
    rw [e1, e2, e3, e4]
    field_simp
    ring
  have hWnn : ∀ u, 0 ≤ u → 0 ≤ W u := by
    intro u hu
    obtain ⟨a1, a2⟩ := hnn u hu
    simp only [W]; positivity
  have hW0 : W 0 ≤ mp + md := by
    obtain ⟨a1, a2⟩ := hnn 0 le_rfl
    simp only [W]; nlinarith
  have hWpos : ∀ u, 0 ≤ u → 0 < W u → 0 < s.Wp u + s.Wd u := by
    intro u hu hpos
    obtain ⟨a1, a2⟩ := hnn u hu
    obtain ⟨e1, e2⟩ := h49 u hu
    rw [e1, e2]
    by_contra hc
    push Not at hc
    have z1 : mp * s.Zp u = 0 := by nlinarith [mul_nonneg hmp.le a1, mul_nonneg hmd.le a2]
    have z2 : md * s.Zd u = 0 := by nlinarith [mul_nonneg hmp.le a1, mul_nonneg hmd.le a2]
    have hZp : s.Zp u = 0 := by
      rcases mul_eq_zero.1 z1 with h | h
      · linarith
      · exact h
    have hZd : s.Zd u = 0 := by
      rcases mul_eq_zero.1 z2 with h | h
      · linarith
      · exact h
    simp only [W] at hpos
    rw [hZp, hZd] at hpos
    simp at hpos
  -- Lipschitz bounds for the cumulative processing
  have hLipP : LipschitzOnWith (Real.toNNReal κ) s.Bp (Ici 0) := by
    refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total y x with h | h
    · obtain ⟨b1, b2⟩ := hLp y x hy h
      rw [abs_of_nonneg b1, abs_of_nonneg (by linarith)]; linarith
    · obtain ⟨b1, b2⟩ := hLp x y hx h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have hLipD : LipschitzOnWith (Real.toNNReal κ) s.Bd (Ici 0) := by
    refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total y x with h | h
    · obtain ⟨b1, b2⟩ := hLd y x hy h
      rw [abs_of_nonneg b1, abs_of_nonneg (by linarith)]; linarith
    · obtain ⟨b1, b2⟩ := hLd x y hx h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  -- regularity reduces to differentiability of `B_p, B_d`
  have hreg : ∀ x, 0 < x → DifferentiableAt ℝ s.Bp x → DifferentiableAt ℝ s.Bd x →
      IsRegular s x := by
    intro x hx dp dd
    have ev : ∀ᶠ u in 𝓝 x, 0 ≤ u := Filter.mem_of_superset (Ioi_mem_nhds hx) fun u (hu : 0 < u) => (le_of_lt hu : 0 ≤ u)
    have dFp : DifferentiableAt ℝ s.Fp x :=
      (dp.div_const mp).congr_of_eventuallyEq (ev.mono fun u hu => (h48 u hu).1)
    have dFd : DifferentiableAt ℝ s.Fd x :=
      (dd.div_const md).congr_of_eventuallyEq (ev.mono fun u hu => (h48 u hu).2)
    have dZp : DifferentiableAt ℝ s.Zp x :=
      (((differentiableAt_const _).add ((differentiableAt_const lam).mul differentiableAt_id)).sub
        dFp).congr_of_eventuallyEq (ev.mono fun u hu => h45 u hu)
    have dZd : DifferentiableAt ℝ s.Zd x :=
      (((differentiableAt_const _).add dFp).sub dFd).congr_of_eventuallyEq
        (ev.mono fun u hu => h46 u hu)
    have dWp : DifferentiableAt ℝ s.Wp x :=
      ((differentiableAt_const mp).mul dZp).congr_of_eventuallyEq (ev.mono fun u hu => (h49 u hu).1)
    have dWd : DifferentiableAt ℝ s.Wd x :=
      ((differentiableAt_const md).mul dZd).congr_of_eventuallyEq (ev.mono fun u hu => (h49 u hu).2)
    exact ⟨hx, dp, dd, dFp, dFd, dWp, dWd, dZp, dZd⟩
  -- decay: while the work is positive, the processing runs at full rate
  have hdecay : ∀ a b, 0 ≤ a → a ≤ b → (∀ u ∈ Ioc a b, 0 < W u) →
      (s.Bp b + s.Bd b) - (s.Bp a + s.Bd a) = κ * (b - a) := by
    intro a b ha hab hpos
    have hsub : uIcc a b ⊆ Ici 0 := by
      rw [uIcc_of_le hab]; intro u hu; exact le_trans ha hu.1
    have acP := (hLipP.mono hsub).absolutelyContinuousOnInterval
    have acD := (hLipD.mono hsub).absolutelyContinuousOnInterval
    have ac := ((hLipP.mono hsub).add (hLipD.mono hsub)).absolutelyContinuousOnInterval
    have hftc := ac.integral_deriv_eq_sub
    rw [← hftc]
    have : ∫ x in a..b, deriv (fun x => s.Bp x + s.Bd x) x = ∫ x in a..b, κ := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [acP.ae_differentiableAt, acD.ae_differentiableAt] with x hxp hxd hx
      rw [uIoc_of_le hab] at hx
      have hxI : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨le_of_lt hx.1, hx.2⟩
      have dp := hxp hxI
      have dd := hxd hxI
      have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
      have := hWC x (hreg x hx0 dp dd) (hWpos x hx0.le (hpos x hx))
      rw [deriv_fun_add dp dd]
      exact this
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    ring
  set δ := (mp + md) / ε + 1 with hδ
  have hδpos : 0 < δ := by positivity
  -- (1) the work vanishes at some time `s₀ ≤ δ`
  obtain ⟨s0, hs0a, hs0b, hs0⟩ : ∃ s0, 0 ≤ s0 ∧ s0 ≤ δ ∧ W s0 = 0 := by
    by_contra hc
    push Not at hc
    have hpos : ∀ u ∈ Ioc 0 δ, 0 < W u := fun u hu =>
      lt_of_le_of_ne (hWnn u hu.1.le) (Ne.symm (hc u hu.1.le hu.2))
    have hd := hdecay 0 δ le_rfl hδpos.le hpos
    rw [hB0p, hB0d] at hd
    have e1 := hW δ hδpos.le
    have hεδ : ε * δ = mp + md + ε := by rw [hδ]; field_simp
    have : W δ < 0 := by nlinarith
    linarith [hWnn δ hδpos.le]
  -- (2) once zero, the work stays zero
  have hcont : ContinuousOn W (Ici 0) := by
    have h1 : ContinuousOn (fun u => W 0 + (mp + md) * lam * u - (s.Bp u + s.Bd u)) (Ici 0) :=
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).sub
        (hLipP.continuousOn.add hLipD.continuousOn)
    exact h1.congr fun u hu => hW u hu
  have hts : s0 ≤ t := le_trans hs0b ht
  have hWt : W t = 0 := by
    by_contra hne
    have hWt0 : 0 < W t := lt_of_le_of_ne (hWnn t (le_trans hs0a hts)) (Ne.symm hne)
    set S := Icc s0 t ∩ W ⁻¹' {0}
    have hSc : IsClosed S :=
      (hcont.mono fun u hu => le_trans hs0a hu.1).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton
    have hSne : S.Nonempty := ⟨s0, ⟨le_rfl, hts⟩, hs0⟩
    have hSb : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
    have haS := hSc.csSup_mem hSne hSb
    set a := sSup S
    have ha0 : 0 ≤ a := le_trans hs0a haS.1.1
    have hat : a < t := lt_of_le_of_ne haS.1.2 (fun h => hne (h ▸ haS.2))
    have hpos : ∀ u ∈ Ioc a t, 0 < W u := by
      intro u hu
      refine lt_of_le_of_ne (hWnn u (le_trans ha0 hu.1.le)) (fun h0 => ?_)
      have : u ∈ S := ⟨⟨le_trans haS.1.1 hu.1.le, hu.2⟩, h0.symm⟩
      have := le_csSup hSb this
      linarith [hu.1]
    have hd := hdecay a t ha0 hat.le hpos
    have e1 := hW t (le_trans ha0 hat.le)
    have e2 := hW a ha0
    have hWa : W a = 0 := haS.2
    nlinarith
  obtain ⟨a1, a2⟩ := hnn t (le_trans (le_trans hs0a hs0b) ht)
  simp only [W] at hWt
  constructor <;> nlinarith
