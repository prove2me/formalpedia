-- Prove2me | solution 1 for MultiPeriod.bellman_value_eq_multi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:24.373993+00:00
-- url     : https://prove2.me/submissions/cd76d8db-7065-45e6-9e6f-e9ecba39d4e6

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_MultiPeriod
import Theorems.Thm_MultiPeriod_Feas_measure_univ
import Theorems.Thm_MultiPeriod_VGo_le_costGo
import Theorems.Thm_MultiPeriod_exists_eps_strategy
import Theorems.Thm_MultiPeriod_costGo_le_VGo_add

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable {X Y}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
variable {κμ κν}
variable (κμ κν)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := by
  refine le_antisymm ?_ ?_
  · -- upper bound via ε-optimal strategies
    refine le_iInf fun γ₀ => le_iInf fun h₀mem => ?_
    have hγ₀mass : γ₀ Set.univ = 1 := by
      have h1 : (γ₀.map Prod.fst) Set.univ = 1 := by
        rw [h₀mem.1]; exact measure_univ
      rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ] at h1
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · -- T = 0: cost and value both reduce to the stage-0 cost
      refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le
        (fun t h => (hne t h).choose) (iInf_le_of_le h₀mem
          (iInf_le _ fun t h => (hne t h).choose_spec)))) ?_
      exact le_of_eq rfl
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / T with hδ
      have hδpos : 0 < δ :=
        ENNReal.div_pos (by exact_mod_cast hε.ne') (by finiteness)
      obtain ⟨γε, hmem, hopt⟩ := exists_eps_strategy κμ κν c T hne hδpos
      have hbound : ∀ h₀ : PairHist X Y 0,
          costGo c γε T 0 h₀ ≤ VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ :=
        fun h₀ => costGo_le_VGo_add κμ κν c T hκμ γε hmem hopt T 0
          (by omega) h₀
      have hTδ : (T : ℝ≥0∞) * δ = (ε : ℝ≥0∞) := by
        rw [hδ]
        exact ENNReal.mul_div_cancel (by exact_mod_cast hT.ne')
          (by finiteness)
      calc ⨅ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y)
            (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
            (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
            ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀'
          ≤ ∫⁻ h₀, costGo c γε T 0 h₀ ∂γ₀ := by
            refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le γε
              (iInf_le_of_le h₀mem (iInf_le _ hmem)))) ?_
            exact le_refl _
        _ ≤ ∫⁻ h₀, (VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ) ∂γ₀ :=
            lintegral_mono hbound
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (T : ℝ≥0∞) * δ := by
            have hsplit := lintegral_add_right (μ := γ₀)
              (fun h₀ : X 0 × Y 0 => VGo c κμ κν T 0 h₀)
              (g := fun _ : X 0 × Y 0 => (T : ℝ≥0∞) * δ) measurable_const
            rw [hsplit, lintegral_const, hγ₀mass, mul_one]
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (ε : ℝ≥0∞) := by rw [hTδ]
  · -- lower bound: integrate L2
    refine le_iInf fun γ₀ => le_iInf fun γ => le_iInf fun h₀mem =>
      le_iInf fun hfeas => ?_
    calc ⨅ (γ₀' : Measure (X 0 × Y 0)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
          ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀'
        ≤ ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := iInf₂_le γ₀ h₀mem
      _ ≤ ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀ :=
          lintegral_mono fun h₀ => VGo_le_costGo κμ κν c γ hfeas T 0 h₀
end MultiPeriod
