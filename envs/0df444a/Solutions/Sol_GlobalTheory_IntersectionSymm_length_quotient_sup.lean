-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.length_quotient_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:00.314341+00:00
-- url     : https://prove2.me/submissions/4d1563ae-e02b-4650-ac31-cf4dc21f44c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm
namespace GlobalTheory.IntersectionSymm
theorem _root_.solution {A : Type} [CommRing A] (p : Ideal A) (b : A) :
    Module.length A (A ⧸ (p ⊔ Ideal.span {b})) =
      Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) := by
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ A p (Ideal.span {b})).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  exact Module.length_eq_of_surjective (S := A) (R := A ⧸ p) Ideal.Quotient.mk_surjective
end GlobalTheory.IntersectionSymm
