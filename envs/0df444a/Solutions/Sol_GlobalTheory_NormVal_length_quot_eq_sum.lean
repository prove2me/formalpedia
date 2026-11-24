-- Prove2me | solution 1 for GlobalTheory.NormVal.length_quot_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:27.705772+00:00
-- url     : https://prove2.me/submissions/0330c025-d254-47cd-a917-07c56d785f48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_length_eq_sum_tensor

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
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
namespace GlobalTheory.NormVal
theorem _root_.solution (I : Ideal S) (hI : Module.length R (S ⧸ I) ≠ ⊤) :
    Module.length R (S ⧸ I) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ I.map (algebraMap S (A n))) * n.asIdeal.inertiaDeg R := by
  have h : IsFiniteLength S (S ⧸ I) := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hI
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hI.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [length_eq_sum_tensor R A h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A n) I).toLinearEquiv.length_eq]
end GlobalTheory.NormVal
