-- Prove2me | solution 1 for GlobalTheory.isRegularLocalRing_atPrime_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:21.396891+00:00
-- url     : https://prove2.me/submissions/2e06cd0e-9e3a-4f5a-9863-6ea310fcf5f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagata
import Theorems.Thm_GlobalTheory_isRegularRing_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {B : Type} [CommRing B] (p q : Ideal B) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have hd : Disjoint (q.primeCompl : Set B) (p : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    exact hx (hpq hxp)
  let P' : Ideal (Localization.AtPrime q) := p.map (algebraMap B _)
  haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hd
  have hc : P'.comap (algebraMap B (Localization.AtPrime q)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹p.IsPrime› hd
  have hsub : (P'.comap (algebraMap B (Localization.AtPrime q))).primeCompl = p.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_of_isRegularLocalRing _
  have hreg : IsRegularLocalRing (Localization.AtPrime P') :=
    IsRegularRing.isRegularLocalRing_localization P'
  haveI : IsLocalization p.primeCompl (Localization.AtPrime P') := by
    rw [← hsub]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime q.primeCompl P'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P')
      (Localization.AtPrime p)).toRingEquiv
end GlobalTheory
