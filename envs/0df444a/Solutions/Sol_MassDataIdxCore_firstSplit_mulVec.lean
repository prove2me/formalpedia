-- Prove2me | solution 1 for MassDataIdxCore.firstSplit_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:06.553839+00:00
-- url     : https://prove2.me/submissions/bce6cff8-22ab-4cf4-8b62-92f64844170b

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
theorem _root_.solution (M : Matrix n n T) (x : n → T) :
    (fun i => t1 θ ((M *ᵥ x) i)) = M.map (t1 θ) *ᵥ fun j => t1 θ (x j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
end MassDataIdxCore
