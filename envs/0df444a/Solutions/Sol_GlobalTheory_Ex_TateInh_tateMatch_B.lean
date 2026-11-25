-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.tateMatch_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:25.663185+00:00
-- url     : https://prove2.me/submissions/0fd77c90-d82a-418b-939d-4fbb9ee46d85

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
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) (hn : Odd n) : (tateMatch q n hn).B (AddEquiv.refl _) :=
  fun _ _ _ ⟨z, h, _⟩ => ⟨z, h⟩
end GlobalTheory.Ex.TateInh
