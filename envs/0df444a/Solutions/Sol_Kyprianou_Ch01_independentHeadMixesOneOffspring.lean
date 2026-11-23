-- Prove2me | solution 1 for Kyprianou.Ch01.independentHeadMixesOneOffspring
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:24:03.323323+00:00
-- url     : https://prove2.me/submissions/dd4f3175-9469-4441-b60b-de865e8ab7ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_independentHeadAtomHasExponentialMass

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal Interval
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
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        exponentialPDFReal (rate : ℝ) a * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  have hmass :=
    independentHeadAtomHasExponentialMass Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hSupport hJumpMass hHeadLaw hHeadTailIndependent K y hy t ht k j hPop
  have hyt : (0 : ℝ) ≤ (y : ℝ) * (t : ℝ) := by positivity
  rw [hmass, intervalIntegral.integral_of_le hyt]
  let g : ℝ → ℝ := fun a =>
    (offspring j).toReal *
      (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal
  have hpdf : gammaPDF (1 : ℝ) (rate : ℝ) = exponentialPDF (rate : ℝ) := by
    funext x
    rfl
  have hpos : 0 < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  unfold expMeasure gammaMeasure
  rw [hpdf]
  unfold exponentialPDF
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      ((measurable_exponentialPDFReal (rate : ℝ)).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) g measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro a _
  dsimp
  rw [ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hpos a)]
  dsimp [g]
  rw [mul_assoc]
