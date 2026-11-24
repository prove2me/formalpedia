-- Prove2me | solution 1 for GlobalTheory.addVal_norm_eq_sum_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:38.799664+00:00
-- url     : https://prove2.me/submissions/a70ee9cc-ec62-44a3-ade1-abee36a95ffb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_length_quot_eq_sum
import Theorems.Thm_GlobalTheory_addVal_norm_eq_length
import Theorems.Thm_GlobalTheory_length_quot_span_ne_top_iff

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
namespace GlobalTheory
theorem _root_.solution {x : S} (hx : x ∈ nonZeroDivisors S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ Ideal.span {algebraMap S (A n) x}) * n.asIdeal.inertiaDeg R := by
  rw [addVal_norm_eq_length, length_quot_eq_sum R A _ ((length_quot_span_ne_top_iff R x).2 hx)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Ideal.map_span, Set.image_singleton]
end GlobalTheory
