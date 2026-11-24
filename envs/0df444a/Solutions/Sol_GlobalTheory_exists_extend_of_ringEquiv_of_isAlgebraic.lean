-- Prove2me | solution 1 for GlobalTheory.exists_extend_of_ringEquiv_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:37.496579+00:00
-- url     : https://prove2.me/submissions/6439fa12-3cb0-45bf-9baa-9f4ada8b4a2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteNormalAdjoinAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K L M F : Type} [Field K] [Field L] [Field M] [Field F]
    [IsAlgClosed F] [Algebra L M] [Algebra.IsAlgebraic L M] (φ : K ≃+* L) (g : K →+* F) :
    ∃ g' : M →+* F, g'.comp ((algebraMap L M).comp φ.toRingHom) = g := by
  letI : Algebra L F := (g.comp φ.symm.toRingHom).toAlgebra
  let g' : M →ₐ[L] F := IsAlgClosed.lift
  refine ⟨g'.toRingHom, RingHom.ext fun x => ?_⟩
  change g' (algebraMap L _ (φ x)) = g x
  rw [g'.commutes]
  change g (φ.symm (φ x)) = g x
  rw [φ.symm_apply_apply]
end GlobalTheory
