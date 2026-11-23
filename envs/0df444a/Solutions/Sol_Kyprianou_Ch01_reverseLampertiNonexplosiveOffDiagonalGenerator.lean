-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveOffDiagonalGenerator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:35:47.845955+00:00
-- url     : https://prove2.me/submissions/943d44da-85d8-4136-8d0e-4dc95909cda1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalFirstEventRemainderZeroSlope
import Theorems.Thm_Kyprianou_Ch01_expNegNNRealHasDerivWithinAtZero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ (y k : ℕ), k ≠ y →
      HasDerivWithinAt
        (fun t : ℝ => ((K y (Real.toNNReal t)) k).toReal)
        (if y ≤ k + 1 then
          (rate : ℝ) * (y : ℝ) *
            (offspring (k + 1 - y)).toReal
         else 0)
        (Set.Ici 0) 0 := by
  intro y k hyk
  let a : ℝ := (rate : ℝ) * (y : ℝ)
  let c : ℝ :=
    if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0
  have hRem : HasDerivWithinAt
      (fun t : ℝ =>
        ((K y (Real.toNNReal t)) k).toReal -
          c * (1 - Real.exp (-(a * (Real.toNNReal t : ℝ)))))
      0 (Set.Ici 0) 0 := by
    simpa only [c, a] using
      (Kyprianou.Ch01.reverseLampertiOffDiagonalFirstEventRemainderZeroSlope
        Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
        hdriver hSupport hJumpMass hNoExplosion K hRealisation y k hyk)
  have hExp :
      HasDerivWithinAt
        (fun t : ℝ => Real.exp (-(a * (Real.toNNReal t : ℝ))))
        (-a) (Set.Ici 0) 0 :=
    Kyprianou.Ch01.expNegNNRealHasDerivWithinAtZero a
  have hFirst : HasDerivWithinAt
      (fun t : ℝ => c * (1 - Real.exp (-(a * (Real.toNNReal t : ℝ)))))
      (c * a) (Set.Ici 0) 0 := by
    simpa only [neg_neg] using ((hExp.const_sub 1).const_mul c)
  have hSum := hRem.add hFirst
  have hFun :
      (fun t : ℝ =>
        ((K y (Real.toNNReal t)) k).toReal -
          c * (1 - Real.exp (-(a * (Real.toNNReal t : ℝ))))) +
      (fun t : ℝ =>
        c * (1 - Real.exp (-(a * (Real.toNNReal t : ℝ))))) =
      (fun t : ℝ => ((K y (Real.toNNReal t)) k).toReal) := by
    funext t
    simp only [Pi.add_apply, sub_add_cancel]
  have hSum' : HasDerivWithinAt
      (fun t : ℝ => ((K y (Real.toNNReal t)) k).toReal)
      (0 + c * a) (Set.Ici 0) 0 := by
    rw [← hFun]
    exact hSum
  have hRate :
      0 + c * a =
        if y ≤ k + 1 then
          (rate : ℝ) * (y : ℝ) * (offspring (k + 1 - y)).toReal
        else 0 := by
    dsimp [c, a]
    split_ifs <;> ring
  rw [hRate] at hSum'
  exact hSum'
