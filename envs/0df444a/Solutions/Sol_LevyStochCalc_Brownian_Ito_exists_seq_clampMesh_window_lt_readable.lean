-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:00.899966+00:00
-- url     : https://prove2.me/submissions/7c7633f4-c913-4ec8-82a9-a2998e880636

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_window_clamp_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology
universe u
section Mesh
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- **Clamping levels along which the mesh of every bounded window decays geometrically.** -/
theorem solution {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ i : ℕ, LevyStochCalc.Brownian.Ito.clampMesh P H b ((i : ℝ) + 1) (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
  classical
  have hchoice : ∀ i : ℕ, ∃ j : ℕ,
      i ≤ j ∧ LevyStochCalc.Brownian.Ito.clampMesh P H b ((i : ℝ) + 1) j < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
    intro i
    have hTpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have htend := LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp_readable (P := P) hm hbm
      (fun p k => (hq p k _ hTpos).ne) (fun p => (hbq p _ hTpos).ne)
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
      refine pos_iff_ne_zero.mpr (pow_ne_zero _ ?_)
      simp
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hpos))
    exact ⟨max N i, le_max_right N i, hN (max N i) (le_max_left N i)⟩
  choose ms hge hms using hchoice
  exact ⟨ms, hge, hms⟩
