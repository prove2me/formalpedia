-- Prove2me | solution 1 for Kyprianou.Ch07.exercise7_6CreepingHittingAllParts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:08:58.118691+00:00
-- url     : https://prove2.me/submissions/a590d9df-ea64-466a-9065-f92d00dce3c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_exercise7_6_GaussianAndTwoSidedCreeping
import Theorems.Thm_Kyprianou_Ch07_exercise7_6_FiniteVariationCreepingDrift
import Theorems.Thm_Kyprianou_Ch07_exercise7_6_IrregularAtZeroPrecludesCreeping
import Theorems.Thm_Kyprianou_Ch07_exercise7_6_SpectrallyNegativeNoDownCreeping
import Theorems.Thm_Kyprianou_Ch07_exercise7_6_StableNoCreepingPointHitting
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta)) :
    let upCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1
    let downCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P (fun t omega => -X t omega)
          (fun _ => (⊤ : WithTop NNReal)) 1
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    ((Tendsto (fun theta : Real =>
         Psi theta / ((theta ^ 2 : Real) : Complex))
         (Filter.comap (fun theta : Real => |theta|) atTop)
         (nhds (((sigma2 : Real) / 2 : Real) : Complex)) ∧
       ((upCreeps ∧ downCreeps) ↔ 0 < sigma2)) ∧
     ((sigma2 = 0 ∧ finiteVariationJumpMass) →
       (upCreeps ↔ 0 < canonicalDrift)) ∧
     (Kyprianou.Ch06.IsIrregularFor P X 0 (Set.Ioi 0) →
       ¬ upCreeps) ∧
     (sigma2 = 0 → Pi (Set.Ioi 0) = 0 →
       (¬ ∀ᵐ omega ∂P,
         Monotone (fun t : NNReal => -X t omega)) →
       ¬ downCreeps) ∧
     (∀ alpha : Real, 1 < alpha → alpha < 2 →
       (∃ c : Real, 0 < c ∧ ∀ theta : Real,
         Psi theta = ((c * |theta| ^ alpha : Real) : Complex)) →
       (¬ upCreeps ∧ ¬ downCreeps ∧
         ∀ x : Real, 0 < P {omega : Omega |
           ∃ t : NNReal, 0 < t ∧ X t omega = x}))) := by
  dsimp only
  exact ⟨
    Kyprianou.Ch07.exercise7_6_GaussianAndTwoSidedCreeping P X b sigma2 Pi Psi hX hTriplet hPsi,
    Kyprianou.Ch07.exercise7_6_FiniteVariationCreepingDrift P X b sigma2 Pi Psi hX hTriplet hPsi,
    Kyprianou.Ch07.exercise7_6_IrregularAtZeroPrecludesCreeping P X b sigma2 Pi Psi hX hTriplet hPsi,
    Kyprianou.Ch07.exercise7_6_SpectrallyNegativeNoDownCreeping P X b sigma2 Pi Psi hX hTriplet hPsi,
    Kyprianou.Ch07.exercise7_6_StableNoCreepingPointHitting P X b sigma2 Pi Psi hX hTriplet hPsi⟩
