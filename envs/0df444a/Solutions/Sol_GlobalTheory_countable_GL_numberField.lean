-- Prove2me | solution 1 for GlobalTheory.countable_GL_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:06.544772+00:00
-- url     : https://prove2.me/submissions/61ecb7c6-47df-4a9b-a99a-7171849df44c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
noncomputable section
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] (r : ℕ) :
    Countable (GL (Fin r) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable
    (f := fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) fun _ _ h => Units.ext h
end GlobalTheory
