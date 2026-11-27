-- Prove2me | solution 1 for GlobalTheory.addVal_localization_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:42.241745+00:00
-- url     : https://prove2.me/submissions/5a329ebb-366c-472d-9394-75e85dd1cb5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_addVal_norm_ne_top_iff
import Theorems.Thm_GlobalTheory_addVal_norm_eq_sum

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
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
variable [∀ n, IsDomain (A n)] [∀ n, IsDiscreteValuationRing (A n)]
include R
namespace GlobalTheory
theorem _root_.solution {x : S} (hx : x ∈ nonZeroDivisors S) (n : MaximalSpectrum S) :
    addVal (A n) (algebraMap S (A n) x) ≠ ⊤ := by
  intro h
  refine (addVal_norm_ne_top_iff R x).2 hx ?_
  rw [addVal_norm_eq_sum R A, ENat.sum_eq_top]
  refine ⟨n, Finset.mem_univ _, ?_⟩
  rw [h, ENat.top_mul]
  exact_mod_cast (Ideal.inertiaDeg_pos n.asIdeal R).ne'
end GlobalTheory
