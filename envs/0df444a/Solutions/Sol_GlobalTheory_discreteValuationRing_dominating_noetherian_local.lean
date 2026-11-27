-- Prove2me | solution 1 for GlobalTheory.discreteValuationRing_dominating_noetherian_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:10.991447+00:00
-- url     : https://prove2.me/submissions/caeb7b47-fc9b-4d8f-add1-ae280cf30b33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff_isLocalHom
import Theorems.Thm_GlobalTheory_irreducible_algebraMap_adicCompletion_of_dvr
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating
import Theorems.Thm_GlobalTheory_range_algebraMap_eq_iInf_discreteValuationSubring
import Theorems.Thm_GlobalTheory_injective_and_isLocalHom_adicCompletion_comp

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
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution (L : Type w) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] :
    (¬ IsField R → ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring) ∧
    (IsIntegrallyClosed R → (algebraMap R K).range =
      ⨅ V : {V : ValuationSubring K // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring}, V.1.toSubring) ∧
    ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V],
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring →
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal V) V))
        (AdicCompletion (maximalIdeal V) V) ∧
      (∀ π : V, Irreducible π → Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π)) ∧
      ∃ h : ∀ r, algebraMap R L r ∈ V,
        Function.Injective ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp
          ((algebraMap R L).codRestrict V h)) ∧
        IsLocalHom ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp
          ((algebraMap R L).codRestrict V h)) := by
  refine ⟨exists_discreteValuationSubring_dominating R K L,
    fun _ => range_algebraMap_eq_iInf_discreteValuationSubring R K, fun V _ h => ?_⟩
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  exact ⟨inferInstance, inferInstance, fun π => irreducible_algebraMap_adicCompletion_of_dvr, h1,
    injective_and_isLocalHom_adicCompletion_comp _
      fun a b hab => hinj (congrArg Subtype.val hab)⟩
end GlobalTheory
