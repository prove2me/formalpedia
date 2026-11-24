-- Prove2me | solution 1 for GlobalTheory.finite_support_length_localizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:00.155855+00:00
-- url     : https://prove2.me/submissions/07f28489-a3f7-4548-9c6c-9b19928edbc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_localizedModule_eq_add_of_exact
import Theorems.Thm_GlobalTheory_length_localizedModule_congr
import Theorems.Thm_GlobalTheory_length_localizedModule_quotient_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]
namespace GlobalTheory
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) :
    {n : MaximalSpectrum S | Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) ≠ 0}.Finite := by
  induction h with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    refine (ih.insert ⟨m, hm⟩).subset fun n hn => ?_
    by_cases hnm : n.asIdeal = m
    · exact Or.inl (MaximalSpectrum.ext hnm)
    · right
      rw [Set.mem_setOf_eq, length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ
        N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        length_localizedModule_congr _ e, length_localizedModule_quotient_of_ne m _ hnm,
        add_zero] at hn
      exact hn
end GlobalTheory
