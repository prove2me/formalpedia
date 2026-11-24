-- Prove2me | solution 1 for GlobalTheory.trdeg_eq_of_ringEquiv_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:23.174598+00:00
-- url     : https://prove2.me/submissions/c4b93656-fc6a-4401-bbb6-d45f56c38971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Theorems.Thm_GlobalTheory_trdeg_le_of_ringEquiv_square

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra = @Algebra.trdeg K' L' _ _ f'.toAlgebra := by
  refine le_antisymm (trdeg_le_of_ringEquiv_square f f' eK eL h)
    (trdeg_le_of_ringEquiv_square f' f eK.symm eL.symm ?_)
  ext x
  have := congrArg (fun g => eL.symm (g (eK.symm x))) h
  simpa using this.symm
end GlobalTheory
