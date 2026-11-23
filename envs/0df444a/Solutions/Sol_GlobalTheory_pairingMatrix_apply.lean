-- Prove2me | solution 1 for GlobalTheory.pairingMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:21.036724+00:00
-- url     : https://prove2.me/submissions/f1997c2f-b56a-4981-97e5-2c0c37fa0c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (ε : ι → Module.Dual R M) (e' : ι → M) (a' a : ι) :
    pairingMatrix ε e' a' a = ε a (e' a') := rfl
end GlobalTheory
