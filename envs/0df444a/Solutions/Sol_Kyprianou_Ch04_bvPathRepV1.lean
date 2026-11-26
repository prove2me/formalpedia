-- Prove2me | solution 1 for Kyprianou.Ch04.bvPathRepV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:28:41.552202+00:00
-- url     : https://prove2.me/submissions/7e4f8e9c-7812-4214-80ad-4973821c8efa

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvActualJumpDriftRepresentationV1
open MeasureTheory ProbabilityTheory Filter Set Function Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Specialise the actual jump representation to canonical left limits. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (T : LevyKhintchineTriple)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ))
    (hBV : T.gaussianVariance = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂T.levyMeasure) < ⊤)
    (d : ℝ) (hd : d = T.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂T.levyMeasure) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc (0 : ℝ≥0) t =>
        |X s ω - leftLim (fun u => X u ω) s|) ∧
      X t ω = d * (t : ℝ) +
        ∑' s : Ioc (0 : ℝ≥0) t, (X s ω - leftLim (fun u => X u ω) s) := by
  let XL : ℝ≥0 → Ω → ℝ := fun t ω => leftLim (fun u => X u ω) t
  have hL : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Iio t)) (nhds (XL t ω)) := by
    filter_upwards [hX.cadlag_ae] with ω hω
    intro t ht
    obtain ⟨l, hl⟩ := (hω t).2
    haveI : (nhdsWithin t (Iio t)).NeBot := nhdsWithin_Iio_neBot' ⟨0, ht⟩ le_rfl
    simpa only [XL, leftLim_eq_of_tendsto hl] using hl
  filter_upwards [Kyprianou.Ch04.bvActualJumpDriftRepresentationV1
    P X hX T hchar hBV XL hL] with ω hω
  intro t
  simpa only [XL, ← hd, congrFun hX.start_zero ω, zero_add] using hω t
