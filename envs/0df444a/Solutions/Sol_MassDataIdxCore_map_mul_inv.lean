-- Prove2me | solution 1 for MassDataIdxCore.map_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:27.754797+00:00
-- url     : https://prove2.me/submissions/81c40463-860d-47e1-842b-ccd050368f92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack

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
  [DecidableEq n] {θ : T ≃ₐ[K] K × K} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T)
  (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (f : T →+* K) (g : GL n T) :
    (g : Matrix n n T).map f * ((g⁻¹ : GL n T) : Matrix n n T).map f = 1 := by
  rw [← Matrix.map_mul, g.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
end MassDataIdxCore
