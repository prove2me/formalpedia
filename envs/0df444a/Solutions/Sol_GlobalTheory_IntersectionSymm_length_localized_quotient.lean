-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.length_localized_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:51:28.893577+00:00
-- url     : https://prove2.me/submissions/87d8223f-0f42-4728-957f-da121275d765

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
theorem _root_.solution {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ Ideal.span {a})) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) := by
  let f := Algebra.linearMap A (Localization.AtPrime p)
  let M' : Submodule A A := Ideal.span {a}
  let g := M'.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl f
  let e0 := IsLocalizedModule.iso p.primeCompl g
  let e := e0.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  rw [e.length_eq]
  have h : Submodule.localized' (Localization.AtPrime p) p.primeCompl f M' =
      Ideal.span {algebraMap A (Localization.AtPrime p) a} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [h]
end GlobalTheory.IntersectionSymm
