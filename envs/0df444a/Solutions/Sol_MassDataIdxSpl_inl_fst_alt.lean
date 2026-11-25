-- Prove2me | solution 1 for MassDataIdxSpl.inl_fst_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:34.564814+00:00
-- url     : https://prove2.me/submissions/28aca18f-b979-4cf3-9dbd-cedc0455f8af

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
theorem _root_.solution (v : n → T) : inj1 θ (pr1 θ v) = θ.symm (1, 0) • v := by
  funext i
  show θ.symm ((θ (v i)).1, 0) = θ.symm (1, 0) * v i
  apply θ.injective
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  ext <;> simp
end MassDataIdxSpl
