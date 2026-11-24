-- Prove2me | solution 1 for GlobalTheory.length_localizedModule_atPrime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:48.407408+00:00
-- url     : https://prove2.me/submissions/a8e79ab0-f054-4090-9530-849cd02a11c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_localizedModule_eq_add_of_exact
import Theorems.Thm_GlobalTheory_length_localizedModule_congr
import Theorems.Thm_GlobalTheory_length_localizedModule_quotient_self
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
theorem _root_.solution (n : Ideal S) [n.IsPrime] {X : Type*} [AddCommGroup X]
    [Module S X] (h : IsFiniteLength S X) :
    Module.length (Localization.AtPrime n) (LocalizedModule n.primeCompl X) ≤
      Module.length S X := by
  induction h with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    rw [length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_one S (M ⧸ N)]
    refine add_le_add ih ?_
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    rw [length_localizedModule_congr _ e]
    by_cases hnm : n = m
    · subst hnm
      exact (length_localizedModule_quotient_self n).le
    · rw [length_localizedModule_quotient_of_ne m n hnm]
      exact zero_le_one
end GlobalTheory
