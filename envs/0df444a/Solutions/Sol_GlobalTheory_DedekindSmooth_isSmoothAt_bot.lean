-- Prove2me | solution 1 for GlobalTheory.DedekindSmooth.isSmoothAt_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:09:20.915601+00:00
-- url     : https://prove2.me/submissions/298c394d-51c5-42ea-b913-9b1b7a4b96d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing
namespace GlobalTheory.DedekindSmooth
theorem _root_.solution (k : Type) [Field k] [PerfectField k] (B : Type) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] : Algebra.IsSmoothAt k (⊥ : Ideal B) := by
  have h : IsField (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    simp
  letI := h.toField
  have : Algebra.EssFiniteType B (Localization.AtPrime (⊥ : Ideal B)) :=
    .of_isLocalization _ (⊥ : Ideal B).primeCompl
  have : Algebra.EssFiniteType k (Localization.AtPrime (⊥ : Ideal B)) := .comp _ B _
  exact Algebra.FormallySmooth.of_perfectField
end GlobalTheory.DedekindSmooth
