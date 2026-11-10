-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m16
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:16:22.534004+00:00
-- url     : https://prove2.me/submissions/488a3ed6-cf86-4eec-957e-5fd130143f7a

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Set
open NahmiasPerishable.Inventory

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ d ∂μ, 0 ≤ d) (k : ℕ) (hk : 1 ≤ k) (q : ℝ) (hq : 0 < q) (x : AgeState k) (hx : canonical false x), MarkovFromShocks μ (fun d t => total (trajectory false x (fun _ => q) d (t+k))) (constantStep k q) ∧ Measurable (fun yd : ℝ × ℝ => constantStep k q yd.1 yd.2) ∧ (∀ d : ℕ → ℝ, (∀ t, 0 ≤ d t) → ∀ t, let X := trajectory false x (fun _ => q) d; let Y := total (X (t+k)); let E := expires (X (t+k-1)) (d (t+k-1)); (X (t+k)).1 = packedStock k q Y ∧ 0 ≤ Y ∧ Y ≤ k*q ∧ total (X (t+k+1)) = constantStep k q Y (d (t+k)) ∧ (0 < E ↔ (k-1)*q ≤ Y ∧ Y ≤ k*q) ∧ ((k-1)*q ≤ Y → Y ≤ k*q → E = Y-(k-1)*q))) := by
  intro H
  let x0 : AgeState 1 := (fun _ => 0, 0)
  have hx0 : canonical false x0 := by
    refine ⟨⟨fun _ => le_rfl, le_rfl⟩, fun h => absurd h (lt_irrefl 0), fun _ => rfl⟩
  have hμ0 : ∀ᵐ d ∂(Measure.dirac (0 : ℝ)), 0 ≤ d := by
    rw [ae_iff]
    change (Measure.dirac (0 : ℝ)) (Ici (0 : ℝ))ᶜ = 0
    rw [Measure.dirac_apply' _ measurableSet_Ici.compl]
    simp
  have hpath := (H (Measure.dirac 0) hμ0 1 le_rfl 1 zero_lt_one x0 hx0).2.2
    (fun _ => 1) (fun _ => zero_le_one) 0
  dsimp only at hpath
  have hY : total (trajectory false x0 (fun _ => 1) (fun _ => 1) (0 + 1)) = 0 := by
    simp [trajectory, fifo, total, pos, x0]
  have hiff := hpath.2.2.2.2.1
  have heq := hpath.2.2.2.2.2
  rw [hY] at hiff heq
  have hlo : (((1 : ℕ) : ℝ) - 1) * 1 ≤ 0 := by norm_num
  have hhi : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) * 1 := by norm_num
  have hpos : 0 < expires (trajectory false x0 (fun _ => 1) (fun _ => 1) (0 + 1 - 1)) 1 :=
    hiff.mpr ⟨hlo, hhi⟩
  have hzero : expires (trajectory false x0 (fun _ => 1) (fun _ => 1) (0 + 1 - 1)) 1 =
      0 - (((1 : ℕ) : ℝ) - 1) * 1 :=
    heq hlo hhi
  have hrhs : (0 : ℝ) - (((1 : ℕ) : ℝ) - 1) * 1 = 0 := by norm_num
  rw [hrhs] at hzero
  linarith
