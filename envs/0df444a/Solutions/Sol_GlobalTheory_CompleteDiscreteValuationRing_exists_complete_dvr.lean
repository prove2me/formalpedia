-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.exists_complete_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:49.413216+00:00
-- url     : https://prove2.me/submissions/524a0b75-101f-4226-8e08-713894e56785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
import Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_dvr_of_dim_one
import Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_complete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (t : A) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : A →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧
        ¬ IsUnit (f t) := by
  have hne : Ideal.span {t} ≠ ⊤ := fun h => ht (Ideal.span_singleton_eq_top.1 h)
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hne
  have hPp : P.IsPrime := hP.1.1
  have htP : t ∈ P := hP.1.2 (Ideal.mem_span_singleton_self t)
  have hh : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  let O := Localization.AtPrime P
  have hdim : Ring.KrullDimLE 1 O := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P O]
    exact_mod_cast hh
  have hinj : Function.Injective (algebraMap A O) :=
    IsLocalization.injective O P.primeCompl_le_nonZeroDivisors
  have hnu : ¬ IsUnit (algebraMap A O t) := fun h =>
    (IsLocalization.AtPrime.isUnit_to_map_iff O P t).1 h htP
  obtain ⟨B, _, _, _, f, hf, hft⟩ := exists_dvr_of_dim_one O (algebraMap A O t)
    ((map_ne_zero_iff _ hinj).2 ht0) hnu
  obtain ⟨W, _, _, hW, g, hc, hg, hl⟩ := exists_complete B
  exact ⟨W, inferInstance, inferInstance, hW, g.comp (f.comp (algebraMap A O)), hc,
    hg.comp (hf.comp hinj), fun h => hft (hl.1 _ h)⟩
end GlobalTheory.CompleteDiscreteValuationRing
