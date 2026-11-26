-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_grid_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:01:33.790653+00:00
-- url     : https://prove2.me/submissions/f1eff2a7-88ad-46b5-98be-b50a0612b790

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_measurable
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_integrable_envelope
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_uniform_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_past_event_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite predictable Esscher grid has an integrable gain, a
common integrable envelope, and vanishing integrals on past events. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : Nat → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T) (n : Nat) (a : NNReal) (ha : a ≤ u 0) :
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha * L.X t w - L.ψ alpha * (t:Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha * runningSup L t w + L.ψ alpha * (t:Real))
    let Q : Ω → Real := fun w => ∑ i ∈ Finset.range n,
      H (u i) w * (E (u (i+1)) w - E (u i) w)
    let B : Ω → Real := fun w =>
      4 * Real.exp (alpha * runningSup L T w + |L.ψ alpha| * (T:Real)) *
        Real.exp (|L.ψ alpha| * (T:Real))
    Integrable Q P ∧ (∀ᵐ w ∂P, ‖Q w‖ ≤ B w) ∧
      (∀ A : Set Ω, MeasurableSet[F a] A → (∫ w in A, Q w ∂P) = 0) := by
  dsimp only
  let E : NNReal → Ω → Real := fun t w =>
    Real.exp (alpha * L.X t w - L.ψ alpha * (t:Real))
  let H : NNReal → Ω → Real := fun t w =>
    Real.exp (-alpha * runningSup L t w + L.ψ alpha * (t:Real))
  let Q : Ω → Real := fun w => ∑ i ∈ Finset.range n,
    H (u i) w * (E (u (i+1)) w - E (u i) w)
  let B : Ω → Real := fun w =>
    4 * Real.exp (alpha * runningSup L T w + |L.ψ alpha| * (T:Real)) *
      Real.exp (|L.ψ alpha| * (T:Real))
  have hB : Integrable B P :=
    Kyprianou.Ch04.kw47_esscher_grid_gain_integrable_envelope L alpha hAlpha T
  have hQ : Measurable Q :=
    Kyprianou.Ch04.kw47_esscher_grid_measurable L alpha u n
  have hBound : ∀ᵐ w ∂P, ‖Q w‖ ≤ B w := by
    filter_upwards [] with w
    simpa only [Q,B,H,E,Real.norm_eq_abs] using
      Kyprianou.Ch04.kw47_esscher_grid_gain_uniform_bound
        L alpha hAlpha T u hu hT n w
  refine ⟨hB.mono' hQ.aestronglyMeasurable hBound,hBound,?_⟩
  intro A hA
  exact Kyprianou.Ch04.kw47_esscher_grid_past_event_zero
    P F L alpha hAlpha T u hu hT n a ha A hA
