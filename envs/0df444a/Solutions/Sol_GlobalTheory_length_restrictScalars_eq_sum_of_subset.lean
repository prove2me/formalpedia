-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_eq_sum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:45.413735+00:00
-- url     : https://prove2.me/submissions/27cc6f18-ffba-4b12-87f5-68255c6ba6aa

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
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [iR : Module R X] [iT : IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by
  revert iR iT hT
  induction h with
  | of_subsingleton => intros; simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    intro iR iT hT
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have key : ∀ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl M) = Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl N) + Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl (S ⧸ m)) := fun n => by
      rw [length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ
        N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        length_localizedModule_congr _ e]
    have hmT : (⟨m, hm⟩ : MaximalSpectrum S) ∈ T := by
      by_contra hc
      have h0 := hT _ hc
      rw [key, length_localizedModule_quotient_self m] at h0
      simp at h0
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
      N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      ih (fun n hn => (add_eq_zero.mp ((key n).symm.trans (hT n hn))).1),
      (e.restrictScalars R).length_eq]
    simp_rw [key, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem _ hmT]
    · rw [length_localizedModule_quotient_self m, one_mul]
    · intro n _ hn
      rw [length_localizedModule_quotient_of_ne m n.asIdeal
        (fun hc => hn (MaximalSpectrum.ext hc)), zero_mul]
end GlobalTheory
