-- Prove2me | solution 1 for MassDataIdxSpl.snd_apply_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:13.557014+00:00
-- url     : https://prove2.me/submissions/221e9bf4-5c16-4204-8486-cfaf67354c5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxSpl
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
namespace MassDataIdxSpl
theorem _root_.solution (v : n → T) (i : n) : pr2 θ v i = (θ (v i)).2 := rfl
end MassDataIdxSpl
