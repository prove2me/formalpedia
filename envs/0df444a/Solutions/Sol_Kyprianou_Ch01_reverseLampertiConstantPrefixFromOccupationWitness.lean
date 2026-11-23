-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiConstantPrefixFromOccupationWitness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:13:46.987424+00:00
-- url     : https://prove2.me/submissions/c439d6b2-f444-4b4c-a4cb-1be1530bfad1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type*} (X : NNReal -> Omega -> Int) (omega : Omega)
    (y : Nat) (t : NNReal) (A : Real)
    (hConst : ∀ s : NNReal, (s : Real) < A -> X s omega = (y : Int))
    (hWitness : ∃ s : NNReal, (s : Real) < A ∧
      (t : ENNReal) < reciprocalOccupation X s omega) :
    (compoundPoissonToBranching X t omega).toNat = y := by
  rcases hWitness with ⟨s, hsA, hsClock⟩
  let S : Set NNReal := {u | (t : ENNReal) < reciprocalOccupation X u omega}
  have hExists : ∃ u : NNReal,
      (t : ENNReal) < reciprocalOccupation X u omega := ⟨s, hsClock⟩
  have hBdd : BddBelow S := ⟨0, fun u hu => (zero_le : (0 : NNReal) ≤ u)⟩
  have hMem : s ∈ S := hsClock
  have hInf : sInf S ≤ s := csInf_le hBdd hMem
  have hInv : inverseReciprocalOccupation X t omega ≤
      (s : WithTop NNReal) := by
    simpa [inverseReciprocalOccupation, hExists, S] using
      (WithTop.coe_le_coe.mpr hInf)
  have hClock : min (inverseReciprocalOccupation X t omega)
      (firstNegativePassage X omega) ≤ (s : WithTop NNReal) :=
    (min_le_left _ _).trans hInv
  rcases (WithTop.le_coe_iff).mp hClock with ⟨u, hu, huLe⟩
  have huA : (u : Real) < A :=
    lt_of_le_of_lt (by exact_mod_cast huLe) hsA
  simp [compoundPoissonToBranching, hu, hConst u huA]