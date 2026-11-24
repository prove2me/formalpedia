-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_occupation_upper_exit_markov_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T04:13:46.092228+00:00
-- url     : https://prove2.me/submissions/745b7ca5-da8f-466a-9396-426680212efb

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_upper_exit_markov_occupation_factor_le_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_two_sided_occupation_sections_measurable_for_bridge
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) +
        ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  have hchild := Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2
    Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
  rw [← hchild]
  have hminM := Kyprianou.Ch08.StageB.p2m87_qpos_two_sided_occupation_sections_measurable_for_bridge
    Ω P D ψ hψ a x ha hx hxa A hA
  have hfirst : Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted D.X x) 0 ω) (tauPlus (shifted D.X x) a ω) ∧
          shifted D.X x t ω ∈ A}) :=
    (by fun_prop : Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))))).mul hminM
  calc
    (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)
      = ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            min (tauMinus (shifted D.X x) 0 ω) (tauPlus (shifted D.X x) a ω) ∧
            shifted D.X x t ω ∈ A} +
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
            tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
        apply lintegral_congr_ae
        filter_upwards with t
        obtain ⟨hU, hL⟩ := source_result81_strict_exit_clocks_aemeasurable Ω P D x a
        have hD := (D.levy.stationary_increments 0 t).aemeasurable_snd
        have hincr_eq : ProbabilityTheory.increment D.X 0 t = D.X t := by funext ω; simp [ProbabilityTheory.increment, D.levy.start_zero]
        rw [hincr_eq] at hD
        have hX : AEMeasurable (fun ω => shifted D.X x t ω) P := by simpa [shifted] using hD.const_add x
        let S : Set Ω := {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧ shifted D.X x t ω ∈ A}
        let S₁ : Set Ω := {ω | (t : WithTop ℝ≥0) < min (tauMinus (shifted D.X x) 0 ω) (tauPlus (shifted D.X x) a ω) ∧ shifted D.X x t ω ∈ A}
        let S₂ : Set Ω := {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧ tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧ shifted D.X x t ω ∈ A}
        have hS₂ : NullMeasurableSet S₂ P := by
          have hLlt : NullMeasurableSet ((fun ω => tauMinus (shifted D.X x) 0 ω) ⁻¹' Set.Ioi (t : WithTop ℝ≥0)) P :=
            hL.nullMeasurableSet_preimage (measurableSet_Ioi (a := (t : WithTop ℝ≥0)))
          have hUle : NullMeasurableSet ((fun ω => tauPlus (shifted D.X x) a ω) ⁻¹' Set.Iic (t : WithTop ℝ≥0)) P :=
            hU.nullMeasurableSet_preimage (measurableSet_Iic (a := (t : WithTop ℝ≥0)))
          have hstate : NullMeasurableSet ((fun ω => shifted D.X x t ω) ⁻¹' A) P :=
            hX.nullMeasurableSet_preimage hA
          dsimp [S₂]
          exact hLlt.inter (hUle.inter hstate)
        have hdisj : Disjoint S₁ S₂ := by
          rw [Set.disjoint_left]
          intro ω h₁ h₂
          exact (not_lt_of_ge h₂.2.1) (lt_of_lt_of_le h₁.1 (min_le_right _ _))
        have hset : S = S₁ ∪ S₂ := by
          ext ω
          constructor
          · rintro ⟨hLt, hs⟩
            by_cases hu : tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0)
            · exact Or.inr ⟨hLt, hu, hs⟩
            · exact Or.inl ⟨lt_min_iff.mpr ⟨hLt, not_le.mp hu⟩, hs⟩
          · rintro (⟨hmin, hs⟩ | ⟨hLt, hu, hs⟩)
            · exact ⟨(lt_min_iff.mp hmin).1, hs⟩
            · exact ⟨hLt, hs⟩
        have hnull : P (S₁ ∩ S₂) = 0 := by rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, measure_empty]
        have hsum : P (S₁ ∪ S₂) + P (S₁ ∩ S₂) = P S₁ + P S₂ := by simpa using (measure_union_add_inter₀ S₁ hS₂)
        have hmeasure : P S = P S₁ + P S₂ := by rw [hset]; simpa [hnull] using hsum
        have hm := congrArg
          (fun y : ℝ≥0∞ => ENNReal.ofReal (Real.exp (-q * (t : ℝ))) * y) hmeasure
        simpa [S, S₁, S₂, mul_add] using hm
    _ = (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            min (tauMinus (shifted D.X x) 0 ω) (tauPlus (shifted D.X x) a ω) ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) +
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
            tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) := by
      rw [lintegral_add_left' hfirst.aemeasurable]
