-- Prove2me | solution 1 for GlobalTheory.form_formPerpVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:36.425801+00:00
-- url     : https://prove2.me/submissions/6c004c6e-7080-4be5-b54d-34be625cb6c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_apply_perpVector

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
namespace GlobalTheory
theorem _root_.solution (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) (c : ι) :
    h (formPerpVector h e e' g) (e c) = 0 :=
  apply_perpVector (fun a => h.flip (e a)) e' g c
end GlobalTheory
