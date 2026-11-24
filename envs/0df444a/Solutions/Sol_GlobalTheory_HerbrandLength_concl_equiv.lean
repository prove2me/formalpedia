-- Prove2me | solution 1 for GlobalTheory.HerbrandLength.concl_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:37.328831+00:00
-- url     : https://prove2.me/submissions/e234f74a-3c97-4f3e-9363-ddf0a0261f7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
import Theorems.Thm_GlobalTheory_HerbrandLength_concl_ext
import Theorems.Thm_GlobalTheory_HerbrandLength_concl_subsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]
namespace GlobalTheory.HerbrandLength
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (b : A) (P : Finset (PrimeSpectrum A)) (e : M ≃ₗ[A] N) (h : Concl b P M) : Concl b P N :=
  concl_ext (M₃ := PUnit) b P e.toLinearMap 0 e.injective (Function.surjective_to_subsingleton _)
    ((e.exact_zero_iff_surjective _).2 e.surjective) h (concl_subsingleton b P PUnit)
end GlobalTheory.HerbrandLength
