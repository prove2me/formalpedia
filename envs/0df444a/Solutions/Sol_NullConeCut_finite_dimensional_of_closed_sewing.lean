-- Prove2me | solution 1 for NullConeCut.finite_dimensional_of_closed_sewing
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:55:25.900399+00:00
-- url     : https://prove2.me/submissions/b60c28e0-1f68-447e-91b7-00d38473b5af

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.Finset

open Filter
open scoped Topology

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    {Cycle : Type*} [Nonempty Cycle] (weight mean : Finset Cycle → ℝ) (δ Z : ℝ)
    (uncut_pos : 0 < Z)
    (weights : ∀ P, P.Nonempty → 0 ≤ weight P)
    (cut_estimate : ¬ FiniteDimensional ℂ E → ∀ P, P.Nonempty → mean P ≤ δ / 2)
    (sewing : Tendsto (fun P => weight P * (mean P - δ / 2)) atTop (𝓝 Z)) :
    FiniteDimensional ℂ E := by
  classical
  by_contra hinf
  let c : Cycle := Classical.arbitrary _
  have bound : ∀ᶠ P : Finset Cycle in atTop, weight P * (mean P - δ / 2) ≤ 0 := by
    filter_upwards [eventually_ge_atTop ({c} : Finset Cycle)] with P hP
    have hne : P.Nonempty := ⟨c, hP (Finset.mem_singleton_self c)⟩
    exact mul_nonpos_of_nonneg_of_nonpos (weights P hne) (sub_nonpos.mpr (cut_estimate hinf P hne))
  exact uncut_pos.not_ge (le_of_tendsto sewing bound)
