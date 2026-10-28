-- Prove2me | solution 1 for MarkovProcess.Semigroup.eventually_forall_mem_norm_apply_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:44:08.203853+00:00
-- url     : https://prove2.me/submissions/f6858ab9-2ec9-4685-9105-66649a951929

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem solution {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] F) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (hT : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 0))
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ K, ‖T i x‖ ≤ ε := by
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  set δ : ℝ := ε / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨s, -, hsfin, hcover⟩ :=
    hK.elim_finite_subcover_image (c := fun y : E ↦ Metric.ball y δ)
      (fun _ _ ↦ Metric.isOpen_ball)
      (fun y hy ↦ Set.mem_iUnion₂.2 ⟨y, hy, Metric.mem_ball_self hδ⟩)
  have hfin : ∀ᶠ i in l, ∀ y ∈ s, ‖T i y‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finite hsfin]
    intro y _
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.mp (hT y) (ε / 2) (by positivity)]
      with i hi
    exact hi.le
  filter_upwards [hfin] with i hi x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have hdist : ‖x - y‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact (Metric.mem_ball.1 hxy).le
  have hsplit : T i x = T i y + T i (x - y) := by
    rw [← map_add]
    congr 1
    abel
  have hbound : ‖T i (x - y)‖ ≤ ε / 2 := by
    calc
      ‖T i (x - y)‖ ≤ ‖T i‖ * ‖x - y‖ := (T i).le_opNorm _
      _ ≤ (|C| + 1) * δ := by
        refine mul_le_mul ?_ hdist (norm_nonneg _) hCpos.le
        exact (hC i).trans (by linarith [le_abs_self C])
      _ = ε / 2 := by
        rw [hδdef]
        field_simp
  calc
    ‖T i x‖ = ‖T i y + T i (x - y)‖ := by rw [hsplit]
    _ ≤ ‖T i y‖ + ‖T i (x - y)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hi y hy) hbound
    _ = ε := add_halves ε
