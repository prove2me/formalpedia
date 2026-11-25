-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.not_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:42:13.182156+00:00
-- url     : https://prove2.me/submissions/35ef9d60-dbbd-4904-8a90-84a2f44a4a39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution (r : Oˣ) : ¬ (tate (r ^ 3)).InG (tateQ r 3 1) := by
  rintro ⟨z, hz⟩
  have key : ∀ w : ℤ, ¬ (1 : ℤ) = (3 : ℕ) • w := fun w => by
    simp only [nsmul_eq_mul]; push_cast; omega
  exact key z hz
end GlobalTheory.Ex.TateInh
