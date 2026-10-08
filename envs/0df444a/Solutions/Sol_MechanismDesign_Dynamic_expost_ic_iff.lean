-- Prove2me | solution 1 for MechanismDesign.Dynamic.expost_ic_iff
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:56:16.928978+00:00
-- url     : https://prove2.me/submissions/55ce62d4-a65e-4ab4-b7b1-5e5411436bf2

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model



namespace MechanismDesign.Dynamic

theorem expost_dis_core : ¬ (∀ {τlo τhi θlo θhi : ℝ} (m : DirectMechanism τlo τhi θlo θhi),
    m.IsExPostIC ↔
      (∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (m.q τ) (Set.Icc θlo θhi)) ∧
      (∀ τ ∈ Set.Icc τlo τhi,
        AbsolutelyContinuousOnInterval (m.u τ) θlo θhi ∧
        {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ (m.u τ) θ}.Countable ∧
        ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ (m.u τ) θ → deriv (m.u τ) θ = m.q τ θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.t τ θ = m.t τ θlo + (θ * m.q τ θ - θlo * m.q τ θlo) - ∫ x in θlo..θ, m.q τ x)) := by
  intro h
  let m : DirectMechanism 0 0 1 0 := ⟨fun _ _ => 0, fun _ θ => if θ ≤ 1/2 then 0 else 1⟩
  have hic : m.IsExPostIC := by
    intro τ _ θ hθ
    exact absurd hθ (by intro h'; linarith [h'.1, h'.2])
  have hac := ((h m).1 hic).2.1 0 (by simp) |>.1
  have hc := hac.continuousOn
  rw [Set.uIcc_of_ge (by norm_num)] at hc
  have hu : ∀ θ, m.u 0 θ = -(if θ ≤ 1/2 then 0 else 1) := by
    intro θ; simp [DirectMechanism.u, m]
  have hiv := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num) hc
  have hmem : (-1/2 : ℝ) ∈ Set.Icc (m.u 0 1) (m.u 0 0) := by
    rw [hu, hu]; norm_num
  obtain ⟨θ, _, hθ⟩ := hiv hmem
  rw [hu] at hθ
  split_ifs at hθ <;> norm_num at hθ

end MechanismDesign.Dynamic

open MechanismDesign.Dynamic


theorem solution : ¬ (∀ {τlo τhi θlo θhi : ℝ} (m : DirectMechanism τlo τhi θlo θhi),
    m.IsExPostIC ↔
      (∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (m.q τ) (Set.Icc θlo θhi)) ∧
      (∀ τ ∈ Set.Icc τlo τhi,
        AbsolutelyContinuousOnInterval (m.u τ) θlo θhi ∧
        {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ (m.u τ) θ}.Countable ∧
        ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ (m.u τ) θ → deriv (m.u τ) θ = m.q τ θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.t τ θ = m.t τ θlo + (θ * m.q τ θ - θlo * m.q τ θlo) - ∫ x in θlo..θ, m.q τ x)) := expost_dis_core
