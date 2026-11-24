-- Prove2me | solution 1 for GlobalTheory.ProjBij.exists_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:27.737771+00:00
-- url     : https://prove2.me/submissions/04c34776-4e28-4faa-8b67-9b40e6cb1024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfInjectiveModMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.ProjBij
namespace GlobalTheory.ProjBij
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (y : (R ⧸ m) ⊗[R] M) : ∃ x : M, (1 : R ⧸ m) ⊗ₜ[R] x = y :=
  TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y
end GlobalTheory.ProjBij
