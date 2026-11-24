-- Prove2me | solution 1 for GlobalTheory.NormVal.length_localization_quot_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:41.561715+00:00
-- url     : https://prove2.me/submissions/4e9e0e6d-f7b8-4576-9823-145951ca82f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
namespace GlobalTheory.NormVal
theorem _root_.solution (m n : MaximalSpectrum S) [Decidable (n = m)]
    (B : Type*) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B n.asIdeal] :
    Module.length B (B ⧸ m.asIdeal.map (algebraMap S B)) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h
    have := IsLocalization.AtPrime.isLocalRing B n.asIdeal
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal n.asIdeal B, Module.length_eq_one_iff,
      isSimpleModule_iff_isCoatom]
    exact Ideal.isMaximal_def.1 inferInstance
  · rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
    have : ¬ m.asIdeal ≤ n.asIdeal := fun hle =>
      h (MaximalSpectrum.ext (m.isMaximal.eq_of_le n.isMaximal.ne_top hle).symm)
    obtain ⟨y, hy, hyn⟩ := Set.not_subset.1 this
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hy)
      (IsLocalization.map_units _ (⟨y, hyn⟩ : n.asIdeal.primeCompl))
end GlobalTheory.NormVal
