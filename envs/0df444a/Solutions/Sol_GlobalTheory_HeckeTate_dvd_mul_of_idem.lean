-- Prove2me | solution 1 for GlobalTheory.HeckeTate.dvd_mul_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:42.119573+00:00
-- url     : https://prove2.me/submissions/3da88dfa-0019-4853-9bfd-895bf4269059

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_dvd_of_idem

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
theorem _root_.solution {N f g : R} (hf : N ∣ f * (1 - f)) (hg : N ∣ g * (1 - g))
    (h : ∀ q : Ideal R, q.IsMaximal → N ∈ q → f ∈ q ∨ g ∈ q) : N ∣ f * g := by
  apply dvd_of_idem
  · obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a * g * g + f * b, by linear_combination (g * g) * ha + f * hb⟩
  · intro q hq hN
    rcases h q hq hN with h | h
    · exact q.mul_mem_right _ h
    · exact q.mul_mem_left _ h
end GlobalTheory.HeckeTate
