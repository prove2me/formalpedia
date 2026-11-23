-- Prove2me | solution 1 for Kyprianou.Ch01.independentHeadAtomHasExponentialMass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:34:36.770728+00:00
-- url     : https://prove2.me/submissions/4ce5b8f0-2eed-4acf-b1d3-91225554b86e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_independentHeadAtomOnMarkSlice

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (K : PopulationLaws)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ)
    (hPop : ∀ s : ℝ≥0,
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat = k} =
        K ((y - 1) + j) s k) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < arrival 0 ω)}).toReal =
      ∫ a in Ioc (0 : ℝ) ((y : ℝ) * (t : ℝ)),
        (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal
          ∂expMeasure (rate : ℝ) := by
  let φ : ℝ → ℝ := fun a =>
    (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal
  let s : Set ℝ := Ioc (0 : ℝ) ((y : ℝ) * (t : ℝ))
  let u : Set ℝ := {((j : ℝ) - 1)}
  have hslice :=
    independentHeadAtomOnMarkSlice Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hSupport hHeadLaw hHeadTailIndependent K y hy t ht k j hPop
  have : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
    isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hrate)
  rw [hslice]
  have hunit :
      (∫ z in s ×ˢ u, φ z.1 ∂(expMeasure (rate : ℝ)).prod jumpLaw) =
        ∫ z in s ×ˢ u, φ z.1 * (1 : ℝ) ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
    refine setIntegral_congr_fun (measurableSet_Ioc.prod (measurableSet_singleton _)) ?_
    intro _ _
    ring
  rw [hunit, setIntegral_prod_mul φ (fun _ : ℝ => (1 : ℝ)) s u]
  have hmark : ∫ m in u, (1 : ℝ) ∂jumpLaw = (offspring j).toReal := by
    rw [setIntegral_const]
    change (jumpLaw {((j : ℝ) - 1)}).toReal * (1 : ℝ) = (offspring j).toReal
    rw [hJumpMass, mul_one]
  rw [hmark, mul_comm]
  simpa [φ, s] using
    (integral_const_mul (offspring j).toReal φ
      (μ := (expMeasure (rate : ℝ)).restrict s)).symm
