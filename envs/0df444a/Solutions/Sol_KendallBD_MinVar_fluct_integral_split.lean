-- Prove2me | solution 1 for KendallBD.MinVar.fluct_integral_split
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:27:07.019256+00:00
-- url     : https://prove2.me/submissions/837e2070-c7e7-4e39-b0c4-d7cbf222812d

import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting



namespace KendallBD.MinVar

open KendallBD.Sol

lemma g85_rho_deriv (lam mu : ℝ → ℝ) (hadm : Admissible lam mu) (t : ℝ) :
    HasDerivAt (rho lam mu) (mu t - lam t) t := by
  have hc : Continuous (fun τ => mu τ - lam τ) := hadm.2.1.sub hadm.1
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma g85_rho_cont (lam mu : ℝ → ℝ) (hadm : Admissible lam mu) :
    Continuous (rho lam mu) :=
  continuous_iff_continuousAt.2 fun t => (g85_rho_deriv lam mu hadm t).continuousAt

lemma g85_exp_rho_deriv (lam mu : ℝ → ℝ) (hadm : Admissible lam mu) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (rho lam mu s)) (Real.exp (rho lam mu t) * (mu t - lam t)) t :=
  (g85_rho_deriv lam mu hadm t).exp

theorem rate_difference_core (nbar lam mu : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1)
    (hadm : Admissible lam mu) (hmean : HasMean lam mu nbar) :
    ∀ t : ℝ, 0 ≤ t → lam t - mu t = growth nbar t := by
  intro t ht
  have h1 : HasDerivWithinAt (fun s => Real.exp (-rho lam mu s))
      (Real.exp (-rho lam mu t) * (-(mu t - lam t))) (Set.Ici 0) t :=
    ((g85_rho_deriv lam mu hadm t).neg.exp).hasDerivWithinAt
  have h2 : HasDerivWithinAt nbar (Real.exp (-rho lam mu t) * (-(mu t - lam t))) (Set.Ici 0) t := by
    refine h1.congr (fun s hs => ?_) ?_
    · exact (hmean s hs).symm
    · exact (hmean t ht).symm
  have h3 : HasDerivWithinAt nbar (deriv nbar t) (Set.Ici 0) t :=
    ((hn.differentiable (by norm_num) t).hasDerivAt).hasDerivWithinAt
  have h4 := (uniqueDiffOn_Ici (0:ℝ) t ht).eq_deriv _ h3 h2
  unfold growth
  rw [h4, hmean t ht]
  have := hpos t
  field_simp
  ring

theorem fluct_integral_split_core (lam mu : ℝ → ℝ)
    (hadm : Admissible lam mu) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        (Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * lam τ ∧
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        -(Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * mu τ := by
  have hr := g85_rho_cont lam mu hadm
  have hE : Continuous (fun τ => Real.exp (rho lam mu τ)) := hr.rexp
  have hl : Continuous (fun τ => Real.exp (rho lam mu τ) * lam τ) := hE.mul hadm.1
  have hm : Continuous (fun τ => Real.exp (rho lam mu τ) * mu τ) := hE.mul hadm.2.1
  have hftc : ∫ τ in a..b, Real.exp (rho lam mu τ) * (mu τ - lam τ) =
      Real.exp (rho lam mu b) - Real.exp (rho lam mu a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _; exact g85_exp_rho_deriv lam mu hadm x
    · exact (hE.mul (hadm.2.1.sub hadm.1)).intervalIntegrable _ _
  have hsub : ∫ τ in a..b, Real.exp (rho lam mu τ) * (mu τ - lam τ) =
      (∫ τ in a..b, Real.exp (rho lam mu τ) * mu τ) - ∫ τ in a..b, Real.exp (rho lam mu τ) * lam τ := by
    rw [← intervalIntegral.integral_sub (hm.intervalIntegrable _ _) (hl.intervalIntegrable _ _)]
    congr 1; ext τ; ring
  have hadd : ∫ τ in a..b, Real.exp (rho lam mu τ) * (lam τ + mu τ) =
      (∫ τ in a..b, Real.exp (rho lam mu τ) * lam τ) + ∫ τ in a..b, Real.exp (rho lam mu τ) * mu τ := by
    rw [← intervalIntegral.integral_add (hl.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
    congr 1; ext τ; ring
  constructor <;> linarith

lemma g85_growth_cont (nbar : ℝ → ℝ) (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) :
    Continuous (growth nbar) := by
  unfold growth
  exact (hn.continuous_deriv le_rfl).div hn.continuous (fun t => (hpos t).ne')

lemma g85_star_adm (nbar : ℝ → ℝ) (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) :
    Admissible (lamStar nbar) (muStar nbar) := by
  have hg := g85_growth_cont nbar hn hpos
  refine ⟨hg.max continuous_const, (hg.neg).max continuous_const, fun t _ => ⟨?_, ?_⟩⟩
  · exact le_max_right _ _
  · exact le_max_right _ _

lemma g85_star_mean (nbar : ℝ → ℝ) (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t)
    (h0 : nbar 0 = 1) : HasMean (lamStar nbar) (muStar nbar) nbar := by
  intro t _
  have hg := g85_growth_cont nbar hn hpos
  have hint : rho (lamStar nbar) (muStar nbar) t = -(Real.log (nbar t)) := by
    unfold rho
    have : ∀ τ, muStar nbar τ - lamStar nbar τ = -growth nbar τ := by
      intro τ
      unfold muStar lamStar
      rcases le_total (growth nbar τ) 0 with h | h
      · rw [max_eq_left (by linarith), max_eq_right h]; ring
      · rw [max_eq_right (by linarith), max_eq_left h]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_neg]
    have : ∫ τ in (0:ℝ)..t, growth nbar τ = Real.log (nbar t) - Real.log (nbar 0) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        exact ((hn.differentiable (by norm_num) x).hasDerivAt).log (hpos x).ne'
      · exact hg.intervalIntegrable _ _
    rw [this, h0]; simp
  rw [hint]; simp [Real.exp_log (hpos t)]

theorem fluct_excess_core (nbar lam mu : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1)
    (hadm : Admissible lam mu) (hmean : HasMean lam mu nbar) :
    ∀ t : ℝ, 0 ≤ t →
      fluct lam mu t = fluct (lamStar nbar) (muStar nbar) t +
        2 * Real.exp (-2 * KendallBD.Sol.rho lam mu t) *
          ∫ τ in (0 : ℝ)..t,
            Real.exp (KendallBD.Sol.rho lam mu τ) * min (lam τ) (mu τ) := by
  intro t ht
  have hsm := g85_star_mean nbar hn hpos h0
  have hsa := g85_star_adm nbar hn hpos
  have hrho : ∀ τ, 0 ≤ τ → rho lam mu τ = rho (lamStar nbar) (muStar nbar) τ := by
    intro τ hτ
    have := (hmean τ hτ).trans (hsm τ hτ).symm
    have := Real.exp_injective this
    linarith
  have hr := g85_rho_cont lam mu hadm
  have hE : Continuous (fun τ => Real.exp (rho lam mu τ)) := hr.rexp
  have hrate := rate_difference_core nbar lam mu hn hpos h0 hadm hmean
  have hpt : ∀ τ ∈ Set.uIcc (0:ℝ) t,
      Real.exp (rho (lamStar nbar) (muStar nbar) τ) * (lamStar nbar τ + muStar nbar τ) =
      Real.exp (rho lam mu τ) * (lam τ + mu τ) - 2 * (Real.exp (rho lam mu τ) * min (lam τ) (mu τ)) := by
    intro τ hτ
    rw [Set.uIcc_of_le ht] at hτ
    rw [← hrho τ hτ.1]
    have := hrate τ hτ.1
    unfold lamStar muStar
    rw [← this]
    rcases le_total (lam τ) (mu τ) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hI1 : Continuous (fun τ => Real.exp (rho lam mu τ) * (lam τ + mu τ)) :=
    hE.mul (hadm.1.add hadm.2.1)
  have hI2 : Continuous (fun τ => Real.exp (rho lam mu τ) * min (lam τ) (mu τ)) :=
    hE.mul (hadm.1.min hadm.2.1)
  have hint : ∫ τ in (0:ℝ)..t, Real.exp (rho (lamStar nbar) (muStar nbar) τ) * (lamStar nbar τ + muStar nbar τ)
      = (∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * (lam τ + mu τ)) -
        2 * ∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * min (lam τ) (mu τ) := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub
      (hI1.intervalIntegrable _ _) ((hI2.intervalIntegrable _ _).const_mul 2),
      intervalIntegral.integral_const_mul]
  unfold fluct
  rw [hint, ← hrho t ht]
  ring

theorem min_fluctuation_core (nbar : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1) :
    (Admissible (lamStar nbar) (muStar nbar) ∧
      HasMean (lamStar nbar) (muStar nbar) nbar) ∧
    (∀ lam mu : ℝ → ℝ, Admissible lam mu → HasMean lam mu nbar →
      ∀ t : ℝ, 0 ≤ t →
        fluct (lamStar nbar) (muStar nbar) t ≤ fluct lam mu t) ∧
    (∀ lam mu : ℝ → ℝ, Admissible lam mu → HasMean lam mu nbar →
      (∀ t : ℝ, 0 ≤ t →
        fluct lam mu t = fluct (lamStar nbar) (muStar nbar) t) →
      ∀ t : ℝ, 0 ≤ t →
        lam t = lamStar nbar t ∧ mu t = muStar nbar t) := by
  refine ⟨⟨g85_star_adm nbar hn hpos, g85_star_mean nbar hn hpos h0⟩, ?_, ?_⟩
  · intro lam mu hadm hmean t ht
    rw [fluct_excess_core nbar lam mu hn hpos h0 hadm hmean t ht]
    have hnn : 0 ≤ ∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * min (lam τ) (mu τ) := by
      apply intervalIntegral.integral_nonneg ht
      intro τ hτ
      exact mul_nonneg (Real.exp_pos _).le
        (le_min (hadm.2.2 τ hτ.1).1 (hadm.2.2 τ hτ.1).2)
    have := Real.exp_pos (-2 * rho lam mu t)
    nlinarith [mul_nonneg this.le hnn]
  · intro lam mu hadm hmean heq t ht
    have hr := g85_rho_cont lam mu hadm
    have hE : Continuous (fun τ => Real.exp (rho lam mu τ)) := hr.rexp
    have hI2 : Continuous (fun τ => Real.exp (rho lam mu τ) * min (lam τ) (mu τ)) :=
      hE.mul (hadm.1.min hadm.2.1)
    have hrate := rate_difference_core nbar lam mu hn hpos h0 hadm hmean
    set T := t + 1 with hT
    have hT0 : 0 ≤ T := by linarith
    have hex := fluct_excess_core nbar lam mu hn hpos h0 hadm hmean T hT0
    rw [heq T hT0] at hex
    have hpos' := Real.exp_pos (-2 * rho lam mu T)
    have hz : ∫ τ in (0:ℝ)..T, Real.exp (rho lam mu τ) * min (lam τ) (mu τ) = 0 := by
      have : 2 * Real.exp (-2 * rho lam mu T) *
          ∫ τ in (0:ℝ)..T, Real.exp (rho lam mu τ) * min (lam τ) (mu τ) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exfalso; linarith
      · exact h
    have hnn : ∀ τ ∈ Set.Icc (0:ℝ) T, 0 ≤ Real.exp (rho lam mu τ) * min (lam τ) (mu τ) := by
      intro τ hτ
      exact mul_nonneg (Real.exp_pos _).le
        (le_min (hadm.2.2 τ hτ.1).1 (hadm.2.2 τ hτ.1).2)
    have hf0 : Set.EqOn (fun τ => Real.exp (rho lam mu τ) * min (lam τ) (mu τ)) 0 (Set.Icc (0:ℝ) T) := by
      have hT1 : (0:ℝ) < T := by linarith
      have hempty : Set.Ioc T 0 = ∅ := Set.Ioc_eq_empty (not_lt.2 hT1.le)
      have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
        (f := fun τ => Real.exp (rho lam mu τ) * min (lam τ) (mu τ)) (a := 0) (b := T)
        (by
          rw [hempty, Set.union_empty]
          exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
            (Filter.Eventually.of_forall fun x hx => hnn x ⟨hx.1.le, hx.2⟩))
        (hI2.intervalIntegrable _ _)).1 hz
      rw [hempty, Set.union_empty] at hae
      have hae' : (fun τ => Real.exp (rho lam mu τ) * min (lam τ) (mu τ)) =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 T)] 0 :=
        MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono Set.Ioo_subset_Ioc_self le_rfl) hae
      have hoo := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hI2.continuousOn continuousOn_const
      exact Set.EqOn.of_subset_closure hoo hI2.continuousOn continuousOn_const
        Set.Ioo_subset_Icc_self (by rw [closure_Ioo hT1.ne])
    have hmin : Real.exp (rho lam mu t) * min (lam t) (mu t) = 0 :=
      hf0 (show t ∈ Set.Icc (0:ℝ) T from ⟨ht, by linarith⟩)
    have hm0 : min (lam t) (mu t) = 0 := by
      rcases mul_eq_zero.1 hmin with h | h
      · exact absurd h (Real.exp_pos _).ne'
      · exact h
    have hd := hrate t ht
    have hl := (hadm.2.2 t ht).1
    have hm := (hadm.2.2 t ht).2
    unfold lamStar muStar
    rw [← hd]
    rcases le_total (lam t) (mu t) with h | h
    · rw [min_eq_left h] at hm0
      have : lam t = 0 := hm0
      rw [this, max_eq_right (by linarith), max_eq_left (by linarith)]; constructor <;> linarith
    · rw [min_eq_right h] at hm0
      have : mu t = 0 := hm0
      rw [this, max_eq_left (by linarith), max_eq_right (by linarith)]; constructor <;> linarith

end KendallBD.MinVar

open KendallBD.MinVar


theorem solution (lam mu : ℝ → ℝ)
    (hadm : Admissible lam mu) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        (Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * lam τ ∧
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        -(Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * mu τ := by
  exact fluct_integral_split_core lam mu hadm a b ha hab
