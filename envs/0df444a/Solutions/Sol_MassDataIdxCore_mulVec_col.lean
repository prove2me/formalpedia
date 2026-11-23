-- Prove2me | solution 1 for MassDataIdxCore.mulVec_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:12.806163+00:00
-- url     : https://prove2.me/submissions/a86d775c-aab5-49a0-8ba7-388cb59b42fc

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
theorem _root_.solution (M N : Matrix n n K) (j : n) : (M *ᵥ fun i => N i j) = fun i => (M * N) i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
end MassDataIdxCore
