-- Prove2me | solution 1 for GlobalTheory.SplitRadical.isRadical_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:03:22.257391+00:00
-- url     : https://prove2.me/submissions/7fc85bed-430c-475b-ab21-ab589ab402d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.SplitRadical
namespace GlobalTheory.SplitRadical
theorem _root_.solution {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S}
    (hI : Squarefree I) : I.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h1 : I ∣ Ideal.span {x} ^ n := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 : I ∣ Ideal.span {x} := hI.isRadical n _ h1
  exact (Ideal.span_singleton_le_iff_mem I).1 (Ideal.dvd_iff_le.1 h2)
end GlobalTheory.SplitRadical
