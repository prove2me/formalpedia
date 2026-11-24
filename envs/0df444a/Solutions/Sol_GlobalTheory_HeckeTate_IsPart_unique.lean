-- Prove2me | solution 1 for GlobalTheory.HeckeTate.IsPart.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:16:05.025234+00:00
-- url     : https://prove2.me/submissions/4f0c3978-4832-47cc-ae96-ad1d7cefbafd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_dvd_mul_of_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R]
namespace GlobalTheory.HeckeTate
namespace IsPart
theorem _root_.solution {P : Ideal R} {N e e' : R} (h : IsPart P N e) (h' : IsPart P N e') :
    N ∣ e - e' := by
  have key : ∀ {f g : R}, IsPart P N f → IsPart P N g → N ∣ f * (1 - g) := by
    intro f g hf hg
    refine dvd_mul_of_idem hf.1 (by simpa [mul_comm] using hg.1) fun q hq hN => ?_
    by_cases hqP : q = P
    · exact Or.inr (hqP ▸ hg.2.1)
    · exact Or.inl (hf.2.2 q hq hN hqP)
  have := (key h h').sub (key h' h)
  convert this using 1
  ring
end IsPart
end GlobalTheory.HeckeTate
