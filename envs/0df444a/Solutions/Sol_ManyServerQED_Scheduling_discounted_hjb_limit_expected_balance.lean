-- Prove2me | solution 1 for ManyServerQED.Scheduling.discounted_hjb_limit_expected_balance
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:28:16.469359+00:00
-- url     : https://prove2.me/submissions/69dc8919-cc55-49ee-a0ae-9b95a110b41d

import Theorems.Thm_ManyServerQED_Scheduling_discounted_hjb_localized_ito_balance
import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem solution {k : ℕ} [NeZero k] (D : DiffusionData k)
    (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL γ : ℝ)
    (hL : CostAssumptions L ϱ mL) (hγ : 0 < γ)
    (x : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ)
    (hf : IsC2Pol f) (hHJB : IsHJBSolution D L γ f)
    (d : HJBCostLimit D L γ f x)
    (hb : ∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖d.b t ω‖ ≤ a*(1+l1norm (d.X t ω)))
    (hsup : ∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω → ℝ, Integrable V d.P ∧
      ∀ᵐ ω ∂d.P, ∀ t ≤ T, l1norm (d.X t ω)^q ≤ V ω) :
    ∀ T : ℝ≥0,
      Integrable (d.gap T) d.P ∧
      (∫ ω, d.cost T ω ∂d.P) =
        f x - (∫ ω, Real.exp (-γ * (T:ℝ)) * f (d.X T ω) ∂d.P) +
          ∫ ω, d.gap T ω ∂d.P := by
  intro T
  let : IsProbabilityMeasure d.P := d.isProb
  obtain ⟨τ,hτ_le,hτ_mono,hτ_hit,hτ⟩ :=
    discounted_hjb_localized_ito_balance D L ϱ mL γ hL hγ x f hf hHJB d hb T
  let C (R : ℕ) (ω : d.Ω) := d.cost (τ R ω) ω
  let G (R : ℕ) (ω : d.Ω) := d.gap (τ R ω) ω
  let F (R : ℕ) (ω : d.Ω) := Real.exp (-γ * (τ R ω:ℝ)) * f (d.X (τ R ω) ω)
  let Ft (ω : d.Ω) := Real.exp (-γ * (T:ℝ)) * f (d.X T ω)
  have hC_nonneg : ∀ᵐ ω ∂d.P, ∀ t : ℝ≥0, 0 ≤ d.cost t ω := by
    filter_upwards [d.cost_zero,d.cost_increases] with ω h0 hU
    intro t
    simpa only [h0] using hU (show (0:ℝ≥0) ≤ t from zero_le)
  have hG_nonneg : ∀ᵐ ω ∂d.P, ∀ t : ℝ≥0, 0 ≤ d.gap t ω := by
    filter_upwards [d.cost_zero,d.gap_eq,d.gap_increases] with ω h0 heq hU
    have hz : d.gap 0 ω = 0 := by simpa [h0] using heq 0
    intro t
    simpa only [hz] using hU (show (0:ℝ≥0) ≤ t from zero_le)
  have hC : Tendsto (fun R => ∫ ω, C R ω ∂d.P) atTop (𝓝 (∫ ω, d.cost T ω ∂d.P)) := by
    refine tendsto_integral_of_dominated_convergence (d.cost T)
      (fun R => (hτ R).1.aestronglyMeasurable) (d.cost_integrable T) ?_ ?_
    · intro R
      filter_upwards [hC_nonneg,d.cost_increases] with ω hN hU
      change ‖d.cost (τ R ω) ω‖ ≤ d.cost T ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hN _)]
      exact hU (hτ_le R ω)
    · filter_upwards [hτ_hit] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono (fun R hR => by simp [C,hR]))
  have hF : Tendsto (fun R => ∫ ω, F R ω ∂d.P) atTop (𝓝 (∫ ω, Ft ω ∂d.P)) := by
    obtain ⟨A,q,hA⟩ := hf.2
    obtain ⟨V,hV,hVbd⟩ := hsup T q
    have hI : Integrable (fun ω => |A| * (1+V ω)) d.P :=
      ((integrable_const (1:ℝ)).add hV).const_mul _
    refine tendsto_integral_of_dominated_convergence (fun ω => |A| * (1+V ω))
      (fun R => (hτ R).2.2.1.aestronglyMeasurable) hI ?_ ?_
    · intro R
      filter_upwards [hVbd] with ω hω
      have hD : Real.exp (-γ * (τ R ω:ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [(τ R ω).2])
      change ‖Real.exp (-γ * (τ R ω:ℝ)) * f (d.X (τ R ω) ω)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      refine (mul_le_of_le_one_left (abs_nonneg _) hD).trans ((hA _).trans ?_)
      have hN : 0 ≤ l1norm (d.X (τ R ω) ω) :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      calc
        _ ≤ |A| * (1+(l1norm (d.X (τ R ω) ω))^q) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right (hω _ (hτ_le R ω)) _) (abs_nonneg _)
    · filter_upwards [hτ_hit] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono (fun R hR => by simp [F,Ft,hR]))
  have hG_lim : Tendsto (fun R => ∫ ω, G R ω ∂d.P) atTop
      (𝓝 ((∫ ω, d.cost T ω ∂d.P) - f x + ∫ ω, Ft ω ∂d.P)) := by
    refine ((hC.sub tendsto_const_nhds).add hF).congr (fun R => ?_)
    have h := (hτ R).2.2.2
    change (∫ ω, C R ω ∂d.P) = f x - (∫ ω, F R ω ∂d.P) + ∫ ω, G R ω ∂d.P at h
    linarith only [h]
  have hG_mono : ∀ᵐ ω ∂d.P, Monotone (fun R => ENNReal.ofReal (G R ω)) := by
    filter_upwards [d.gap_increases] with ω hU
    exact fun i j hij => ENNReal.ofReal_le_ofReal (hU (hτ_mono ω hij))
  have hG_sup : ∀ᵐ ω ∂d.P, (⨆ R, ENNReal.ofReal (G R ω)) = ENNReal.ofReal (d.gap T ω) := by
    filter_upwards [hτ_hit,d.gap_increases] with ω hω hU
    apply le_antisymm
    · exact iSup_le (fun R => ENNReal.ofReal_le_ofReal (hU (hτ_le R ω)))
    · obtain ⟨R,hR⟩ := hω.exists
      exact le_iSup_of_le R (by simp [G,hR])
  have hG_ofReal (R : ℕ) :
      ENNReal.ofReal (∫ ω, G R ω ∂d.P) = ∫⁻ ω, ENNReal.ofReal (G R ω) ∂d.P :=
    ofReal_integral_eq_lintegral_ofReal (hτ R).2.1 (hG_nonneg.mono (fun ω h => h _))
  have hG_lim' := (ENNReal.continuous_ofReal.tendsto _).comp hG_lim
  have hG_tendsto : Tendsto (fun R => ∫⁻ ω, ENNReal.ofReal (G R ω) ∂d.P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (d.gap T ω) ∂d.P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun R => ENNReal.measurable_ofReal.comp_aemeasurable
        (hτ R).2.1.aestronglyMeasurable.aemeasurable) hG_mono ?_
    filter_upwards [hτ_hit] with ω hω
    exact tendsto_const_nhds.congr' (hω.mono (fun R hR => by simp [G,hR]))
  have hEq : ENNReal.ofReal ((∫ ω, d.cost T ω ∂d.P) - f x + ∫ ω, Ft ω ∂d.P) =
      ∫⁻ ω, ENNReal.ofReal (d.gap T ω) ∂d.P := by
    apply tendsto_nhds_unique _ hG_tendsto
    simpa only [Function.comp_def,hG_ofReal] using hG_lim'
  have hInt : Integrable (d.gap T) d.P := by
    refine ⟨(d.gap_meas T).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (hG_nonneg.mono fun _ h => h T), ← hEq]
    exact ENNReal.ofReal_lt_top
  refine ⟨hInt,?_⟩
  have hLimNonneg : 0 ≤ (∫ ω, d.cost T ω ∂d.P) - f x + ∫ ω, Ft ω ∂d.P :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hG_lim
      (Eventually.of_forall (fun R => integral_nonneg_of_ae (hG_nonneg.mono fun ω h => h _)))
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (hG_nonneg.mono fun _ h => h T)] at hEq
  have hEq' := (ENNReal.ofReal_eq_ofReal_iff hLimNonneg
    (integral_nonneg_of_ae (hG_nonneg.mono fun _ h => h T))).1 hEq
  dsimp [Ft] at hEq'
  linarith only [hEq']
