-- Prove2me | solution 1 for MultiPeriod.bellman_value_eq_multi_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:05.129084+00:00
-- url     : https://prove2.me/submissions/09bd505d-6a9a-4609-826b-11c85b4f5cb9

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_MeasurableStrategy
import Theorems.Thm_MultiPeriod_exists_eps_strategy_analyticallyMeasurable
import Theorems.Thm_MultiPeriod_Feas_measure_univ
import Theorems.Thm_MultiPeriod_bellman_value_eq_multi
import Theorems.Thm_MultiPeriod_costGo_le_VGo_add
import Theorems.Thm_P2M_CouplingSet__measure_univ_db95189062ba


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h)
      (_ : ∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γ t h = (φ h).toMeasure),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := by
  refine le_antisymm ?_ ?_
  · -- upper bound via measurable ε-optimal strategies
    refine le_iInf fun γ₀ => le_iInf fun h₀mem => ?_
    have hγ₀mass : γ₀ Set.univ = 1 := by
      have h1 : (γ₀.map Prod.fst) Set.univ = 1 := by
        rw [h₀mem.1]; exact measure_univ
      rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ] at h1
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · -- T = 0: cost and value both reduce to the stage-0 cost
      obtain ⟨γ1, hmem1, -, hφ1⟩ :=
        exists_eps_strategy_analyticallyMeasurable κμ κν c 0 hκμ_meas
          hκν_meas hκμ_prob hκν_prob hc hne (ε := 1) zero_lt_one
      refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le γ1
        (iInf_le_of_le h₀mem (iInf_le_of_le hmem1 (iInf_le _ hφ1))))) ?_
      exact le_of_eq rfl
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / T with hδ
      have hδpos : 0 < δ :=
        ENNReal.div_pos (by exact_mod_cast hε.ne') (by finiteness)
      obtain ⟨γε, hmem, hopt, hφ⟩ :=
        exists_eps_strategy_analyticallyMeasurable κμ κν c T hκμ_meas
          hκν_meas hκμ_prob hκν_prob hc hne hδpos
      have hbound : ∀ h₀ : PairHist X Y 0,
          costGo c γε T 0 h₀ ≤ VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ :=
        fun h₀ => costGo_le_VGo_add κμ κν c T hκμ_prob γε hmem hopt T 0
          (by omega) h₀
      have hTδ : (T : ℝ≥0∞) * δ = (ε : ℝ≥0∞) := by
        rw [hδ]
        exact ENNReal.mul_div_cancel (by exact_mod_cast hT.ne')
          (by finiteness)
      refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le γε
        (iInf_le_of_le h₀mem (iInf_le_of_le hmem (iInf_le _ hφ))))) ?_
      calc ∫⁻ h₀, costGo c γε T 0 h₀ ∂γ₀
          ≤ ∫⁻ h₀, (VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ) ∂γ₀ :=
            lintegral_mono hbound
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (T : ℝ≥0∞) * δ := by
            have hsplit := lintegral_add_right (μ := γ₀)
              (fun h₀ : X 0 × Y 0 => VGo c κμ κν T 0 h₀)
              (g := fun _ : X 0 × Y 0 => (T : ℝ≥0∞) * δ) measurable_const
            rw [hsplit, lintegral_const, hγ₀mass, mul_one]
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (ε : ℝ≥0∞) := by rw [hTδ]
  · -- lower bound: restricting the infimum can only increase it
    rw [← bellman_value_eq_multi κμ κν c T μ₀ ν₀ hκμ_prob hne]
    refine le_iInf fun γ₀ => le_iInf fun γ => le_iInf fun h₀mem =>
      le_iInf fun hfeas => le_iInf fun _ => ?_
    exact iInf_le_of_le γ₀ (iInf_le_of_le γ (iInf_le_of_le h₀mem
      (iInf_le _ hfeas)))
end MultiPeriod
