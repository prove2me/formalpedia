-- Prove2me | solution 1 for MassDataIdxSpl.snd_smul_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:35.988824+00:00
-- url     : https://prove2.me/submissions/2a5249c8-3861-4245-97f9-b990b5f1fb14

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
theorem _root_.solution (c : T) (v : n → T) : pr2 θ (c • v) = (θ c).2 • pr2 θ v := by
  funext i
  show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2
  rw [map_mul, Prod.snd_mul]
end MassDataIdxSpl
