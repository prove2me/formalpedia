-- Prove2me | solution 1 for MassDataIdxCore.conjP_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:05.922087+00:00
-- url     : https://prove2.me/submissions/191c4172-b2e1-4f7d-bf92-9c8dfa9ebe82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (g h : GL n T) : conjPrime₂ θ P (g * h) = conjPrime₂ θ P g * conjPrime₂ θ P h := by
  have hP : (P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K) = 1 := by simp
  simp only [conjPrime₂, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P : Matrix n n K) ((P⁻¹ : GL n K) : Matrix n n K), hP, Matrix.one_mul]
end MassDataIdxCore
