-- Prove2me | solution 1 for MassDataIdxSpl.fst_smul_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:33.167798+00:00
-- url     : https://prove2.me/submissions/7c6c5628-804d-4051-93cc-3977ccb2c896

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
theorem _root_.solution (c : T) (v : n → T) : pr1 θ (c • v) = (θ c).1 • pr1 θ v := by
  funext i
  show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1
  rw [map_mul, Prod.fst_mul]
end MassDataIdxSpl
