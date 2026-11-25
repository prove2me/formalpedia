-- Prove2me | solution 1 for GlobalTheory.LevDesc.crtAut_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:55.265814+00:00
-- url     : https://prove2.me/submissions/4229a73d-afd7-4882-9ab3-fec8e3087449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}
variable {ι : Type} [Finite ι] {Js : ι → Ideal O} (hle : ∀ i, I ≤ Js i)
  (hc : Pairwise (Function.onFun IsCoprime Js)) (hI : ⨅ i, Js i ≤ I)
namespace GlobalTheory.LevDesc
theorem _root_.solution (γ : QAut N I) (i : ι) : crtAut hle hc hI γ i = autRed (hle i) γ := rfl
end GlobalTheory.LevDesc
