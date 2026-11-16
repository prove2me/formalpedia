-- Prove2me | solution 1 for InfoLossLAR.WorstCase.NativeDyadicSchedule.initialWidth_matrix
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:39:10.611771+00:00
-- url     : https://prove2.me/submissions/544966e1-0c14-4f23-9a2f-9ba5ca5c730d

import Definitions.Def_RegevInitialSelection

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
open scoped BigOperators

/-- Platform binary row envelope is exactly the absolute-entry sum, with
row and column indices kept explicit. -/
theorem initialEntryMass_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    initialEntryMass (List.ofFn (fun row => List.ofFn (fun col => B row col))) =
      ∑ row, ∑ col, |(B row col : ℚ)| := by
  simp only [initialEntryMass,initialRowMass,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  simp only [Nat.cast_natAbs,Int.cast_abs]

end InfoLossLAR.WorstCase.NativeDyadicSchedule

open InfoLossLAR.WorstCase.NativeDyadicSchedule

theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (base : ℕ) :
    initialWidth (List.ofFn (fun row => List.ofFn (fun col => B row col))) base =
      (base : ℚ)*(1+∑ row, ∑ col, |(B row col : ℚ)|) := by
  rw [initialWidth,initialEntryMass_matrix]

#print axioms solution
