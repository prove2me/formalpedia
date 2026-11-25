-- Prove2me | solution 1 for MassDataIdxCore.p_pinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:04.117864+00:00
-- url     : https://prove2.me/submissions/bf18d721-e3c6-48ce-bebc-f2cfd4c7e3b8

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
theorem _root_.solution : (P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K) = 1 := by
  exact P.mul_inv
end MassDataIdxCore
