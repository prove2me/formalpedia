-- Prove2me | solution 1 for ManyServerQED.Scheduling.nonnegative_cost_expectation_from_ae_limit_and_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:47:08.864212+00:00
-- url     : https://prove2.me/submissions/98329a25-d65a-48a3-81aa-70fe35f8c19d

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hZ : Measurable Z)
    (hy : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω) (hz : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (p : ℝ) (hp : 1 < p) (K : ℝ≥0∞) (hK : K < ⊤)
    (hMom : ∀ᶠ n in atTop, (∫⁻ ω, ENNReal.ofReal (Y n ω)^p ∂P) ≤ K) :
    Integrable Z P ∧
      Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂P) atTop
        (𝓝 (ENNReal.ofReal (∫ ω, Z ω ∂P))) := by
  let Y' n ω := ENNReal.ofReal (Y n ω)
  let Z' ω := ENNReal.ofReal (Z ω)
  have hYm : ∀ n, Measurable (Y' n) := fun n => (hY n).ennreal_ofReal
  have hZm : Measurable Z' := hZ.ennreal_ofReal
  have hconv' : ∀ᵐ ω ∂P, Tendsto (fun n => Y' n ω) atTop (𝓝 (Z' ω)) := by
    filter_upwards [hconv] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto (Z ω)).comp hω
  have hnP : 0 ≤ p := by linarith
  have hpMom : (∫⁻ ω, (Z' ω)^p ∂P) ≤ K := by
    have hFat := lintegral_liminf_le (μ := P) (u := atTop) (f := fun n ω => (Y' n ω)^p)
      (fun n => ENNReal.continuous_rpow_const.measurable.comp (hYm n))
    have hpow : ∀ᵐ ω ∂P, liminf (fun n => (Y' n ω)^p) atTop = (Z' ω)^p := by
      filter_upwards [hconv'] with ω hω
      exact ((ENNReal.continuous_rpow_const (y := p)).tendsto (Z' ω) |>.comp hω).liminf_eq
    rw [lintegral_congr_ae hpow] at hFat
    exact hFat.trans (liminf_le_of_frequently_le hMom.frequently)
  have hintFin : (∫⁻ ω, Z' ω ∂P) < ⊤ := by
    calc
      _ ≤ ∫⁻ ω, 1 + (Z' ω)^p ∂P := by
        apply lintegral_mono
        intro ω
        rcases le_total (Z' ω) 1 with h | h
        · exact h.trans le_self_add
        · rw [← ENNReal.rpow_one (Z' ω)]
          exact (ENNReal.rpow_le_rpow_of_exponent_le h hp.le).trans (le_add_left le_rfl)
      _ = P Set.univ + ∫⁻ ω, (Z' ω)^p ∂P := by rw [lintegral_add_left measurable_const,lintegral_const,one_mul]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _,hpMom.trans_lt hK⟩
  have hzInt : Integrable Z P := by
    refine ⟨hZ.aestronglyMeasurable, ?_⟩
    change (∫⁻ ω, ‖Z ω‖ₑ ∂P) < ⊤
    have he : (fun ω => ‖Z ω‖ₑ) =ᵐ[P] Z' := by
      filter_upwards [hz] with ω hω
      simp [Real.enorm_eq_ofReal_abs,abs_of_nonneg hω,Z']
    rwa [lintegral_congr_ae he]
  refine ⟨hzInt,?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hzInt hz]
  change Tendsto (fun n => ∫⁻ ω, Y' n ω ∂P) atTop (𝓝 (∫⁻ ω, Z' ω ∂P))
  have hLo : (∫⁻ ω, Z' ω ∂P) ≤ liminf (fun n => ∫⁻ ω, Y' n ω ∂P) atTop := by
    have hFat := lintegral_liminf_le (μ := P) (u := atTop) hYm
    have he : ∀ᵐ ω ∂P, liminf (fun n => Y' n ω) atTop = Z' ω := by
      filter_upwards [hconv'] with ω hω using hω.liminf_eq
    rwa [lintegral_congr_ae he] at hFat
  apply tendsto_of_le_liminf_of_limsup_le hLo
  by_contra! hHi
  obtain ⟨l,hl,ε,hε,hε'⟩ := ENNReal.exists_add_lt_of_add_lt (by simpa using hHi :
    (∫⁻ ω, Z' ω ∂P) + 0 < limsup (fun n => ∫⁻ ω, Y' n ω ∂P) atTop)
  have hDecay : Tendsto (fun A : ℝ => ENNReal.ofReal (A^(1-p))*K) atTop (𝓝 0) := by
    have h1 : 0 < p-1 := by linarith
    have he : 1-p = -(p-1) := by ring
    have hC : Continuous (fun x : ℝ => ENNReal.ofReal x * K) :=
      (ENNReal.continuous_mul_const hK.ne).comp ENNReal.continuous_ofReal
    simpa only [he, Function.comp_def, ENNReal.ofReal_zero, zero_mul] using
      (hC.tendsto 0).comp (tendsto_rpow_neg_atTop h1)
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hDecay).2 ε hε)
  let a : ℝ := max A 1
  have ha : 0 < a := zero_lt_one.trans_le (le_max_right _ _)
  have hTail : ENNReal.ofReal (a^(1-p))*K ≤ ε := (hA a (le_max_left _ _)).le
  have hPoint (v : ℝ) : ENNReal.ofReal v ≤ min (ENNReal.ofReal v) (ENNReal.ofReal a) +
      ENNReal.ofReal (a^(1-p)) * (ENNReal.ofReal v)^p := by
    by_cases hv : v ≤ a
    · rw [min_eq_left (ENNReal.ofReal_le_ofReal hv)]
      exact le_self_add
    · have hv' : a ≤ v := le_of_lt (lt_of_not_ge hv)
      have hv0 : 0 < v := ha.trans_le hv'
      have hh : v ≤ a^(1-p)*v^p := by
        have hpow : v^(1-p) ≤ a^(1-p) :=
          Real.rpow_le_rpow_of_nonpos ha hv' (by linarith)
        calc
          v = v^(1-p)*v^p := by rw [← Real.rpow_add hv0,sub_add_cancel,Real.rpow_one]
          _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hv0.le _)
      exact ((ENNReal.ofReal_le_ofReal hh).trans_eq (by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
          ENNReal.ofReal_rpow_of_nonneg hv0.le hnP])).trans (le_add_left le_rfl)
  have hFixed : Tendsto (fun n => ∫⁻ ω, min (Y' n ω) (ENNReal.ofReal a) ∂P) atTop
      (𝓝 (∫⁻ ω, min (Z' ω) (ENNReal.ofReal a) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal a)
      (fun n => (hYm n).min measurable_const) (fun _ => ae_of_all _ fun _ => min_le_right _ _) ?_ ?_
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · filter_upwards [hconv'] with ω hω
      exact hω.min tendsto_const_nhds
  have hUp : ∀ᶠ n in atTop, (∫⁻ ω, Y' n ω ∂P) ≤
      (∫⁻ ω, min (Y' n ω) (ENNReal.ofReal a) ∂P) + ε := by
    filter_upwards [hMom] with n hn
    refine (lintegral_mono (fun ω => hPoint (Y n ω))).trans ?_
    rw [lintegral_add_left ((hYm n).min measurable_const),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact add_le_add_right (((mul_le_mul_right hn _)).trans hTail) _
  have hSure := (limsup_le_limsup hUp).trans_eq ((hFixed.add tendsto_const_nhds).limsup_eq)
  exact (not_le_of_gt hε') (hSure.trans (add_le_add_left
    ((lintegral_mono fun ω => min_le_left (Z' ω) _).trans hl.le) _))
