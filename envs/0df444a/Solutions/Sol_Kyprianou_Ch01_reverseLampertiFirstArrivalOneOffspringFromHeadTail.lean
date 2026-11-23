-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalOneOffspringFromHeadTail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:00:44.011322+00:00
-- url     : https://prove2.me/submissions/06715d35-5118-477f-a30f-d3e6bd909976
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_shiftedDriverRealisesPopulation
import Theorems.Thm_Kyprianou_Ch01_independentHeadMixesOneOffspring

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
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (hFullProductLaw : HasLaw
      (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal
            ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}).toReal =
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  have hA : ∀ ω, ProbabilityTheory.arrival arrival 0 ω = arrival 0 ω := by
    intro ω
    rw [ProbabilityTheory.arrival, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hset :
      {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal
            ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)} =
      {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < arrival 0 ω)} := by
    ext ω
    simp [hA ω]
  rw [hset]
  have hyt : (0 : ℝ) ≤ (y : ℝ) * (t : ℝ) := by positivity
  have hEq :
      (Ioo (0 : ℝ) ((y : ℝ) * (t : ℝ))).EqOn
        (fun a : ℝ =>
          (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) * (offspring j).toReal *
            (K ((y - 1) + j)
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal)
        (fun a : ℝ =>
          exponentialPDFReal (rate : ℝ) a * (offspring j).toReal *
            (K ((y - 1) + j)
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal) := by
    intro a ha
    have ha0 : 0 < a := ha.1
    unfold exponentialPDFReal gammaPDFReal
    dsimp
    rw [if_pos ha0.le, Real.rpow_one, Real.Gamma_one, div_one, sub_self,
      Real.rpow_zero a, mul_one]
  rw [intervalIntegral.integral_congr_Ioo_of_le hyt hEq]
  have hPopAll :=
    shiftedDriverRealisesPopulation Q rate arrival marks jumpLaw hdriver hNoExplosion K
      hRealisation hTailDriver hFullProductLaw
  have hPop : ∀ s : ℝ≥0,
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat = k} =
        K ((y - 1) + j) s k :=
    fun s => hPopAll ((y - 1) + j) s k
  exact independentHeadMixesOneOffspring Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
    hSupport hJumpMass hHeadLaw hHeadTailIndependent K y hy t ht k j hPop
