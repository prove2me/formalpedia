-- Prove2me | solution 1 for MassDataIdxCore.secondSplit_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:25.914974+00:00
-- url     : https://prove2.me/submissions/47c2a5fb-2100-4c8b-baf4-044c4cd5c0e3

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
    (fun i => t2 θ ((M *ᵥ x) i)) = M.map (t2 θ) *ᵥ fun j => t2 θ (x j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
end MassDataIdxCore
