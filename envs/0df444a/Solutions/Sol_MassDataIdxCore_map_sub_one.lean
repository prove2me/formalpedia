-- Prove2me | solution 1 for MassDataIdxCore.map_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:31.383257+00:00
-- url     : https://prove2.me/submissions/cdd3ee0c-d889-46a7-9afe-68c0954d735f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul

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
  [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (M : Matrix n n T) (f : T →+* K) : (M - 1).map f = M.map f - 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
end MassDataIdxCore
