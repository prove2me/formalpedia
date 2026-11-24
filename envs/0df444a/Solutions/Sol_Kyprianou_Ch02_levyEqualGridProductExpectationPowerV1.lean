-- Prove2me | solution 1 for Kyprianou.Ch02.levyEqualGridProductExpectationPowerV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:16:02.425052+00:00
-- url     : https://prove2.me/submissions/564019bb-c7dc-459b-aafb-cc92e505f858

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Equal-grid product expectation: independent increments on the partition
`0 = g₀ < ⋯ < g_{n+1} = t` of width `t/(n+1)`, plus stationarity, give
`∫ ∏ f(Δᵢ) = (∫ f(X_{t/(n+1)}))^{n+1}`.
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : ℝ≥0) (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    let g (k : ℕ) := t * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let d (k : ℕ) (ω : Ω) := X (g (k + 1)) ω - X (g k) ω
    (∫ ω, ∏ i : Fin (n + 1), f (d i.val ω) ∂P) =
      (∫ ω, f (X (t / ((n + 1 : ℕ) : ℝ≥0)) ω) ∂P) ^ (n + 1) := by
  dsimp only
  let h : ℝ≥0 := t / ((n + 1 : ℕ) : ℝ≥0)
  let τ : Fin (n + 1 + 1) → ℝ≥0 := fun i => (i.val : ℝ≥0) * h
  have hτ : Monotone τ := by
    intro i k hik
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hik) (by positivity)
  let D (i : Fin (n + 1)) : Ω → ℝ := increment X (τ i.castSucc) (τ i.succ)
  have hind : iIndepFun D P := hX.indep_increments (n + 1) τ hτ
  have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hD (i : Fin (n + 1)) : AEMeasurable (D i) P :=
    (hcoord (τ i.succ)).sub (hcoord (τ i.castSucc))
  have hprod :=
    hind.integral_prod_comp hD fun i =>
      (hf.aemeasurable : AEMeasurable f (P.map (D i))).aestronglyMeasurable
  -- Each increment law equals X_h
  have hstat (i : Fin (n + 1)) : IdentDistrib (D i) (X h) P P := by
    have hh : τ i.succ = τ i.castSucc + h := by
      simp [τ, Nat.cast_add, add_mul]
    have heq : increment X 0 h = X h := by
      funext ω
      simp [increment, congrFun hX.start_zero ω]
    change IdentDistrib (increment X (τ i.castSucc) (τ i.succ)) (X h) P P
    rw [hh, ← heq]
    exact hX.stationary_increments _ _
  have hfactor (i : Fin (n + 1)) :
      (∫ ω, f (D i ω) ∂P) = ∫ ω, f (X h ω) ∂P :=
    ((hstat i).comp hf).integral_eq
  -- Align d i.val with D i: g k = τ ⟨k,_⟩ when k ≤ n+1
  -- g k = τ ⟨k, _⟩ = k * h = t*k/(n+1)
  have hDg (i : Fin (n + 1)) (ω : Ω) :
      D i ω =
        X (t * ((i.val + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) ω -
          X (t * (i.val : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) ω := by
    have hs : τ i.succ = t * ((i.val + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by
      simp [τ, h, div_eq_mul_inv, mul_left_comm, mul_assoc]
    have hc : τ i.castSucc = t * (i.val : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by
      simp [τ, h, div_eq_mul_inv, mul_left_comm, mul_assoc]
    simp [D, increment, hs, hc]
  have hleft :
      (∫ ω, ∏ i : Fin (n + 1), f
          (X (t * ((i.val + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) ω -
            X (t * (i.val : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) ω) ∂P) =
        ∫ ω, ∏ i : Fin (n + 1), f (D i ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hDg i ω]
  rw [hleft]
  rw [show (∫ ω, ∏ i : Fin (n + 1), f (D i ω) ∂P) =
        ∏ i : Fin (n + 1), ∫ ω, f (D i ω) ∂P by
      simpa [Function.comp_def] using hprod]
  simp only [hfactor, Finset.prod_const, h]
  -- ∏_{i : Fin (n+1)} C = C^{n+1}
  rw [Finset.card_fin]
