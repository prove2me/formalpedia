-- Prove2me | solution 1 for Kyprianou.Ch02.levyJordanGridStationaryLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:46:31.033971+00:00
-- url     : https://prove2.me/submissions/2d4bc89d-0103-4d64-97c1-149247f34252

import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    ∀ n : ℕ, ∀ s u : ℝ≥0,
      IdentDistrib (G n s (s+u)) (G n 0 u) P P := by
  dsimp only
  intro n s u
  let g (a : ℝ≥0) (i : Fin (n+1+1)) : ℝ≥0 :=
    a+u*(i.val : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
  let D (a : ℝ≥0) (i : Fin (n+1)) :=
    increment X (g a i.castSucc) (g a i.succ)
  have hmon (a : ℝ≥0) : Monotone (g a) := by
    intro i j hij
    dsimp [g]
    gcongr
    exact_mod_cast hij
  have hi (a : ℝ≥0) : iIndepFun (D a) P := hX.indep_increments _ _ (hmon a)
  have hmX := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hm (a : ℝ≥0) (i : Fin (n+1)) : AEMeasurable (D a i) P :=
    (hmX _).sub (hmX _)
  have hstat (a : ℝ≥0) (i : Fin (n+1)) :
      IdentDistrib (D a i) (increment X 0 (u/((n+1 : ℕ) : ℝ≥0))) P P := by
    have hstep : g a i.succ = g a i.castSucc + u/((n+1 : ℕ) : ℝ≥0) := by
      simp [g, Nat.cast_add, mul_add, add_div, add_assoc]
    dsimp [D]
    rw [hstep]
    exact hX.stationary_increments _ _
  have hvec : IdentDistrib (fun ω i => D s i ω) (fun ω i => D 0 i ω) P P := by
    refine ⟨aemeasurable_pi_lambda _ (hm s), aemeasurable_pi_lambda _ (hm 0), ?_⟩
    rw [(hi s).map_fun_eq_pi_map (hm s), (hi 0).map_fun_eq_pi_map (hm 0)]
    congr 1
    funext i
    exact (hstat s i).map_eq.trans (hstat 0 i).map_eq.symm
  let S (z : Fin (n+1) → ℝ) : ℝ × ℝ :=
    (∑ i, max (z i) 0, ∑ i, max (-z i) 0)
  have hS : Measurable S := by fun_prop
  simpa [S, D, g, increment, Function.comp_def, Nat.cast_add, mul_add, add_div,
    add_tsub_cancel_left] using hvec.comp hS
