-- Prove2me | solution 1 for MassDataIdxCore.intV_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:25.807739+00:00
-- url     : https://prove2.me/submissions/c968a621-ea22-490e-9c0d-e7762300e216

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit
import Theorems.Thm_MassDataIdxCore_intV_mulVec


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
namespace MassDataIdxCore
theorem _root_.solution {M Mi : Matrix n n K} (hM : IntM O M) (hMi : IntM O Mi) (h : Mi * M = 1) (v : n → K) :
    IntV O (M *ᵥ v) ↔ IntV O v := by
  refine ⟨fun hv => ?_, intV_mulVec O hM⟩
  have := intV_mulVec O hMi hv
  rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] at this
end MassDataIdxCore
