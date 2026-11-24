-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_barrier_event_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:04:44.628929+00:00
-- url     : https://prove2.me/submissions/4648f470-4cf0-4918-8ca7-a0a04ce14b96

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∀ t : ℝ≥0,
      let S : ℕ → Set Ω := fun n => {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A}
      Monotone S ∧ (⋃ n, S n) =ᵐ[P] {ω | shifted D.X x t ω ∈ A} := by
  intro t S
  constructor
  · intro n m hnm ω hω
    have hn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hc : tauMinus (shifted D.X (n : ℝ)) 0 ω ≤
        tauMinus (shifted D.X (m : ℝ)) 0 ω := by
      apply sInf_le_sInf
      rintro _ ⟨u, hu, he, hb⟩
      refine ⟨u, hu, he, ?_⟩
      dsimp [shifted] at hb ⊢
      linarith
    exact ⟨hω.1.trans_le hc, hω.2⟩
  · obtain ⟨F, X, hpath, _⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
    filter_upwards [hpath] with ω hω
    apply propext
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact hn.2
    · intro h
      obtain ⟨b, hb⟩ := AvramDividend.Classical.levy_path_bddBelow_finite_horizon X
        (t+1) ω
      obtain ⟨n, hn⟩ := exists_nat_ge (-b)
      apply mem_iUnion.mpr
      refine ⟨n, ?_, h⟩
      have hc : ((t+1 : ℝ≥0) : WithTop ℝ≥0) ≤ tauMinus (shifted D.X (n : ℝ)) 0 ω := by
        apply le_sInf
        rintro _ ⟨u, hu, rfl, hneg⟩
        apply WithTop.coe_le_coe.mpr
        by_contra hlt
        have hbu := hb (show X.X u ω ∈ {y : ℝ | ∃ s : ℝ≥0, s ≤ t+1 ∧
          y = X.X s ω} from ⟨u, le_of_not_ge hlt, rfl⟩)
        dsimp [shifted] at hneg
        rw [← hω u] at hneg
        linarith
      exact (WithTop.coe_lt_coe.mpr (lt_add_of_pos_right t zero_lt_one)).trans_le hc
