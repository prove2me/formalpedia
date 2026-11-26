-- Prove2me | solution 1 for LargeBallLem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:59.179018+00:00
-- url     : https://prove2.me/submissions/06b7331e-525e-435c-af58-2a0fd8af483c

import Definitions.Def_Tablet_DGammaBallMeasure
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_LargeBallLem
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_DGammaBallMeasure


set_option autoImplicit false
open MeasureTheory Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hlsi : IsLSI γ δ ε) (x : E) (r : ℝ)
    (hr : δ / 2 ≤ r) :
    curveMeasure γ (Metric.closedBall x r) ≤ ENNReal.ofReal (4 * (1 + ε⁻¹) * r) := by
-- BODY
  have hrpos : 0 < r := lt_of_lt_of_le (half_pos hδ) hr
  have hmeas : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
  have heq : curveMeasure γ (Metric.closedBall x r) =
      volume ((γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (0 : ℝ) γ.len) := by
    rw [curveMeasure, Measure.map_apply hmeas measurableSet_closedBall,
      Measure.restrict_apply (hmeas measurableSet_closedBall)]
  rw [heq]
  by_cases hne : ∃ s ∈ Set.Icc (0 : ℝ) γ.len, dist x (γ.toFun s) ≤ r
  · obtain ⟨s, hs, hsr⟩ := hne
    -- Step 1: `B_r(x) ⊆ B_{2r}(γ(s))`.
    have hstep1 : (γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (0 : ℝ) γ.len ⊆
        (γ.toFun ⁻¹' Metric.closedBall (γ.toFun s) (2 * r)) ∩ Set.Icc (0 : ℝ) γ.len := by
      rintro t ⟨ht1, ht2⟩
      refine ⟨?_, ht2⟩
      simp only [Set.mem_preimage, Metric.mem_closedBall] at ht1 ⊢
      calc dist (γ.toFun t) (γ.toFun s)
          ≤ dist (γ.toFun t) x + dist x (γ.toFun s) := dist_triangle _ _ _
        _ ≤ r + r := add_le_add ht1 hsr
        _ = 2 * r := by ring
    -- Step 2: split the `2r`-sublevel set of `d(γ(s),·)` by `d_γ(s,·)`.
    have hstep2 : (γ.toFun ⁻¹' Metric.closedBall (γ.toFun s) (2 * r)) ∩ Set.Icc (0 : ℝ) γ.len ⊆
        {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < δ} ∪
          {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t ≤ 2 * ε⁻¹ * r} := by
      rintro t ⟨ht1, ht2⟩
      simp only [Set.mem_preimage, Metric.mem_closedBall] at ht1
      rcases lt_or_ge (dGamma γ s t) δ with hlt | hge
      · exact Or.inl ⟨ht2, hlt⟩
      · right
        have hd : ε * dGamma γ s t ≤ dist (γ.toFun s) (γ.toFun t) := hlsi.2 s hs t ht2 hge
        have ht1' : dist (γ.toFun s) (γ.toFun t) ≤ 2 * r := by rw [dist_comm]; exact ht1
        have hb : ε * dGamma γ s t ≤ 2 * r := hd.trans ht1'
        refine ⟨ht2, ?_⟩
        have h2 : ε * dGamma γ s t ≤ ε * (2 * ε⁻¹ * r) := by
          have heqc : ε * (2 * ε⁻¹ * r) = 2 * r := by field_simp
          rw [heqc]; exact hb
        exact le_of_mul_le_mul_left h2 hε
    -- Step 3: bound each piece.
    have hpiece1 : volume {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < δ} ≤
        ENNReal.ofReal (2 * δ) := DGammaBallMeasure γ s δ hs hδ
    have hpiece2 : volume {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t ≤ 2 * ε⁻¹ * r} ≤
        ENNReal.ofReal (4 * ε⁻¹ * r) := by
      apply ENNReal.le_of_forall_pos_le_add
      intro η hη _
      have hρ'pos : 0 < 2 * ε⁻¹ * r + (η : ℝ) / 2 := by positivity
      have hρ'gt : 2 * ε⁻¹ * r < 2 * ε⁻¹ * r + (η : ℝ) / 2 := by
        have : (0 : ℝ) < (η : ℝ) / 2 := by positivity
        linarith
      have hsub : {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t ≤ 2 * ε⁻¹ * r} ⊆
          {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < 2 * ε⁻¹ * r + (η : ℝ) / 2} := by
        rintro t ⟨ht1, ht2⟩
        exact ⟨ht1, lt_of_le_of_lt ht2 hρ'gt⟩
      calc volume {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t ≤ 2 * ε⁻¹ * r}
          ≤ volume {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < 2 * ε⁻¹ * r + (η : ℝ) / 2} :=
            measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * (2 * ε⁻¹ * r + (η : ℝ) / 2)) :=
            DGammaBallMeasure γ s _ hs hρ'pos
        _ = ENNReal.ofReal (4 * ε⁻¹ * r) + (η : ℝ≥0∞) := by
            rw [show 2 * (2 * ε⁻¹ * r + (η : ℝ) / 2) = 4 * ε⁻¹ * r + (η : ℝ) by ring,
              ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_coe_nnreal]
    -- Assemble.
    calc volume ((γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (0 : ℝ) γ.len)
        ≤ volume ({t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < δ} ∪
            {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t ≤ 2 * ε⁻¹ * r}) :=
          measure_mono (hstep1.trans hstep2)
      _ ≤ volume {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < δ} +
            volume {t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t ≤ 2 * ε⁻¹ * r} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * δ) + ENNReal.ofReal (4 * ε⁻¹ * r) := add_le_add hpiece1 hpiece2
      _ = ENNReal.ofReal (2 * δ + 4 * ε⁻¹ * r) :=
          (ENNReal.ofReal_add (by linarith) (by positivity)).symm
      _ ≤ ENNReal.ofReal (4 * (1 + ε⁻¹) * r) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [hr]
  · have hempty : (γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (0 : ℝ) γ.len = ∅ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨ht1, ht2⟩
      exact hne ⟨t, ht2, by rw [dist_comm]; exact ht1⟩
    rw [hempty]
    simp
