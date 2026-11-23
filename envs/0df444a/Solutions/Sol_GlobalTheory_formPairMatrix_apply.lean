-- Prove2me | solution 1 for GlobalTheory.formPairMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:23.991162+00:00
-- url     : https://prove2.me/submissions/531e94c6-222e-431d-8482-91119e62a8c8

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
  {σ : R →+* R}
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (a' a : ι) :
    formPairMatrix h e e' a' a = h (e' a') (e a) := rfl
end GlobalTheory
