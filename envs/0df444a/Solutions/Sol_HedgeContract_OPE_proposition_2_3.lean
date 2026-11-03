-- Prove2me | solution 1 for HedgeContract.OPE.proposition_2_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:07:31.943661+00:00
-- url     : https://prove2.me/submissions/31d5ee99-d2d3-4aef-8143-302edd4dc4f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HedgeContract_OPE_proposition_6_4
import Theorems.Thm_HedgeContract_OPE_proposition_2_3_contract
set_option autoImplicit false

open HedgeContract.OPE MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem solution (P : Params) (hP : P.Standing) (h62 : Assumption62 P)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (W : ℝ → ℝ) (hW : IsValue P P₀ B hB W) :
    BddAbove {y : ℝ | 0 ≤ y ∧ W y < Wtil P y} ∧
    ContDiffOn ℝ 2 W (Set.Ioi 0) ∧
    (∀ y ∈ Set.Ioo 0 (ybar P W),
      P.δ * W y = hamSup P y (deriv W y) (deriv (deriv W) y)) ∧
    (∀ y : ℝ, 0 ≤ y → ybar P W ≤ y →
      HasDerivWithinAt W (-P.δ) (Set.Ici 0) y) ∧
    W 0 = P.δ * P.Φ ∧
    derivWithin (derivWithin W (Set.Ici 0)) (Set.Ici 0) (ybar P W) = 0 ∧
    (∃ Zs ζs : ℝ → ℝ,
      (∀ y ∈ Set.Ioc 0 (ybar P W),
        IsMaximizer P (deriv W y) (deriv (deriv W) y) (Zs y) (ζs y)) ∧
      ∀ yhat : ℝ, 0 ≤ yhat → ∃ C : Contract Ω,
      C.Admissible P P₀ B hB yhat ∧
      C.payoff P P₀ = W yhat ∧
      (∀ᵐ ω ∂P₀,
        C.I 0 ω = max (yhat - ybar P W) 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < C.τ ω → C.Y t ω ∈ Set.Icc 0 (ybar P W)) ∧
        C.paymentMeasure ω
          {t : ℝ | 0 < t ∧ ENNReal.ofReal t ≤ C.τ ω ∧
            C.Y t.toNNReal ω < ybar P W} = 0 ∧
        (C.τ ω < ⊤ → C.Y (C.τ ω).toReal.toNNReal ω = 0) ∧
        (∀ᵐ t : ℝ ∂MeasureTheory.volume,
          0 ≤ t → ENNReal.ofReal t < C.τ ω →
          C.Z t.toNNReal ω = Zs (C.Y t.toNNReal ω) ∧
          C.ζ t.toNNReal ω = ζs (C.Y t.toNNReal ω)))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    proposition_6_4 P hP h62 P₀ B hB W hW
  exact ⟨h1, h2, h3, h4, h5, h6,
    proposition_2_3_contract P hP h62 P₀ B hB W hW h1 h2 h3 h4 h5 h6 h7 h8⟩
