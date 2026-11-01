-- Prove2me | solution 1 for IncompleteProc.English.offer_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:40:52.718057+00:00
-- url     : https://prove2.me/submissions/54a0d29f-c5b8-4d14-8cac-ba5d3587d760

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

open MeasureTheory Set

namespace IncProcOfferOptimalAux

open IncompleteProc.English

/-- Fundamental theorem of calculus for `g(x) = (R - k(x, ω)) F(x)` on `[a, b] ⊆ [c̲, c̄]`,
together with the a.e. formula `g' = f (R - Ψ₂)`. -/
theorem gdiff {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing) (ω : Ω) {a b : ℝ}
    (ha : E.clo ≤ a) (hab : a ≤ b) (hb : b ≤ E.chi) :
    ((E.R - E.k b ω) * E.F b) - ((E.R - E.k a ω) * E.F a) =
        ∫ x in a..b, deriv (fun y => (E.R - E.k y ω) * E.F y) x ∧
      ∀ᵐ x, x ∈ Ioo a b →
        deriv (fun y => (E.R - E.k y ω) * E.F y) x = E.f x * (E.R - E.Psi2 x ω) := by
  obtain ⟨_hn, _hQ, _hR, hlt, _hfm, hfi, _hf1, ⟨δ, hδ, hfδ⟩, _hG, _hkmono, hkd, hkcb, _hkm,
    _hkcm, _hkb⟩ := hS
  have hfI : IntervalIntegrable E.f volume E.clo E.chi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).mpr hfi
  have hsub : uIcc a b ⊆ uIcc E.clo E.chi := by
    rw [uIcc_of_le hab, uIcc_of_le hlt.le]
    exact Icc_subset_Icc ha hb
  have hFac : AbsolutelyContinuousOnInterval E.F a b := by
    have := hfI.absolutelyContinuousOnInterval_intervalIntegral (c := E.clo) (by simp)
    exact this.mono hsub
  have hK0 : 0 ≤ E.K := le_trans (hkcb ω E.clo ⟨le_rfl, hlt.le⟩).1 (hkcb ω E.clo ⟨le_rfl, hlt.le⟩).2
  have hLip : LipschitzOnWith (Real.toNNReal E.K) (fun y => E.R - E.k y ω) (Icc E.clo E.chi) := by
    apply (convex_Icc E.clo E.chi).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun y => -E.kc y ω)
    · intro x hx
      exact (hkd ω x hx).const_sub E.R
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (hkcb ω x hx).1, Real.coe_toNNReal _ hK0]
      exact (hkcb ω x hx).2
  have hkac : AbsolutelyContinuousOnInterval (fun y => E.R - E.k y ω) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [uIcc_of_le hlt.le] at hsub
    exact hLip.mono hsub
  have hgac : AbsolutelyContinuousOnInterval (fun y => (E.R - E.k y ω) * E.F y) a b :=
    hkac.fun_mul hFac
  refine ⟨(hgac.integral_deriv_eq_sub).symm, ?_⟩
  filter_upwards [hfI.ae_hasDerivAt_integral] with x hx hxab
  have hxI : x ∈ Icc E.clo E.chi := ⟨ha.trans hxab.1.le, hxab.2.le.trans hb⟩
  have hxu : x ∈ uIcc E.clo E.chi := by rw [uIcc_of_le hlt.le]; exact hxI
  have hF : HasDerivAt E.F (E.f x) x := hx hxu E.clo (by simp)
  have hk : HasDerivAt (fun y => E.k y ω) (E.kc x ω) x :=
    (hkd ω x hxI).hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt ha hxab.1)
      (lt_of_lt_of_le hxab.2 hb))
  have hg : HasDerivAt (fun y => (E.R - E.k y ω) * E.F y)
      (-E.kc x ω * E.F x + (E.R - E.k x ω) * E.f x) x := (hk.const_sub E.R).mul hF
  rw [hg.deriv]
  have hfx : 0 < E.f x := lt_of_lt_of_le hδ (hfδ x hxI)
  unfold Env.Psi2
  field_simp
  ring

/-- Integral of a function that is a.e. nonnegative on `Ioo a b`. -/
theorem int_nonneg_of_ae_Ioo {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (H : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ h x) : 0 ≤ ∫ x in a..b, h x := by
  apply intervalIntegral.integral_nonneg_of_ae_restrict hab
  rw [Filter.EventuallyLE, ae_restrict_congr_set (Ioo_ae_eq_Icc (μ := volume)).symm,
    ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [H] with x hx hx' using hx hx'

end IncProcOfferOptimalAux

open IncompleteProc.English IncProcOfferOptimalAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    ∀ p ∈ Set.Ioc E.clo E.chi, ∀ ω,
      (∀ c ∈ Set.Icc E.clo p, E.offerValue ω p c ≤ E.offerValue ω p (min p (E.cStar2 ω))) ∧
      E.offer ω p = E.k (min p (E.cStar2 ω)) ω := by
  intro p hp ω
  have hS' := hS
  obtain ⟨_hn, hQ, _hR, hlt, _hfm, _hfi, _hf1, ⟨δ, hδ, hfδ⟩, _hG, hkmono, _hkd, _hkcb, _hkm,
    _hkcm, _hkb⟩ := hS'
  set S : Set ℝ := insert E.clo {c ∈ Set.Icc E.clo E.chi | E.Psi2 c ω ≤ E.R} with hSdef
  have hc2 : E.cStar2 ω = sSup S := rfl
  have hbdd : BddAbove S := by
    refine ⟨E.chi, ?_⟩
    rintro y (rfl | ⟨hy, _⟩)
    · exact hlt.le
    · exact hy.2
  have hne : S.Nonempty := ⟨E.clo, mem_insert _ _⟩
  have hc2lo : E.clo ≤ E.cStar2 ω := le_csSup hbdd (mem_insert _ _)
  have hc2hi : E.cStar2 ω ≤ E.chi := by
    apply csSup_le hne
    rintro y (rfl | ⟨hy, _⟩)
    · exact hlt.le
    · exact hy.2
  have hlow : ∀ x ∈ Icc E.clo E.chi, x < E.cStar2 ω → E.Psi2 x ω ≤ E.R := by
    intro x hx hxc
    obtain ⟨y, hyS, hxy⟩ := exists_lt_of_lt_csSup hne (hc2 ▸ hxc)
    rcases hyS with rfl | ⟨hyI, hyR⟩
    · exact absurd hx.1 (not_le.mpr hxy)
    · exact le_trans (hA.2 ω hx hyI hxy.le) hyR
  have hhigh : ∀ x ∈ Icc E.clo E.chi, E.cStar2 ω < x → E.R < E.Psi2 x ω := by
    intro x hx hxc
    by_contra hcon
    have : x ∈ S := Or.inr ⟨hx, not_lt.mp hcon⟩
    exact absurd (le_csSup hbdd this) (not_le.mpr hxc)
  -- g is monotone on [c̲, c⋆₂] and antitone on [c⋆₂, c̄]
  have hmono : ∀ a b, E.clo ≤ a → a ≤ b → b ≤ E.cStar2 ω →
      (E.R - E.k a ω) * E.F a ≤ (E.R - E.k b ω) * E.F b := by
    intro a b ha hab hb
    obtain ⟨h1, h2⟩ := gdiff E hS ω ha hab (hb.trans hc2hi)
    have : 0 ≤ ∫ x in a..b, deriv (fun y => (E.R - E.k y ω) * E.F y) x := by
      apply int_nonneg_of_ae_Ioo hab
      filter_upwards [h2] with x hx hxab
      rw [hx hxab]
      have hxI : x ∈ Icc E.clo E.chi := ⟨ha.trans hxab.1.le, (hxab.2.le.trans hb).trans hc2hi⟩
      have hfx : 0 < E.f x := lt_of_lt_of_le hδ (hfδ x hxI)
      have := hlow x hxI (lt_of_lt_of_le hxab.2 hb)
      nlinarith
    linarith
  have hanti : ∀ a b, E.cStar2 ω ≤ a → a ≤ b → b ≤ E.chi →
      (E.R - E.k b ω) * E.F b ≤ (E.R - E.k a ω) * E.F a := by
    intro a b ha hab hb
    obtain ⟨h1, h2⟩ := gdiff E hS ω (hc2lo.trans ha) hab hb
    have : 0 ≤ ∫ x in a..b, -deriv (fun y => (E.R - E.k y ω) * E.F y) x := by
      apply int_nonneg_of_ae_Ioo hab
      filter_upwards [h2] with x hx hxab
      rw [hx hxab]
      have hxI : x ∈ Icc E.clo E.chi := ⟨(hc2lo.trans ha).trans hxab.1.le, hxab.2.le.trans hb⟩
      have hfx : 0 < E.f x := lt_of_lt_of_le hδ (hfδ x hxI)
      have := hhigh x hxI (lt_of_le_of_lt ha hxab.1)
      nlinarith
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hFp : 0 ≤ E.F p := by
    unfold Env.F
    apply intervalIntegral.integral_nonneg hp.1.le
    intro u hu
    exact le_trans hδ.le (hfδ u ⟨hu.1, hu.2.trans hp.2⟩)
  have hov : ∀ c, E.offerValue ω p c = E.Q * ((E.R - E.k c ω) * E.F c) / E.F p := by
    intro c; unfold Env.offerValue; ring
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hov, hov]
    apply div_le_div_of_nonneg_right _ hFp
    apply mul_le_mul_of_nonneg_left _ hQ.le
    by_cases hcm : c ≤ min p (E.cStar2 ω)
    · exact hmono c _ hc.1 hcm (min_le_right _ _)
    · push Not at hcm
      have hm : min p (E.cStar2 ω) = E.cStar2 ω := by
        rcases min_choice p (E.cStar2 ω) with h | h
        · rw [h] at hcm; exact absurd hc.2 (not_le.mpr hcm)
        · exact h
      rw [hm] at hcm ⊢
      exact hanti _ c le_rfl hcm.le (hc.2.trans hp.2)
  · unfold Env.offer
    have hpI : p ∈ Icc E.clo E.chi := ⟨hp.1.le, hp.2⟩
    have hcI : E.cStar2 ω ∈ Icc E.clo E.chi := ⟨hc2lo, hc2hi⟩
    rcases le_total p (E.cStar2 ω) with h | h
    · rw [min_eq_left h, min_eq_left ((hkmono ω).monotoneOn hpI hcI h)]
    · rw [min_eq_right h, min_eq_right ((hkmono ω).monotoneOn hcI hpI h)]
