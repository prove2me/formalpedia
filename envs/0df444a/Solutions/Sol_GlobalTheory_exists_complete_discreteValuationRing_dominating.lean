-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_dominating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:27.619642+00:00
-- url     : https://prove2.me/submissions/aaa21606-4879-4209-bcd9-c46c23feeae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff_isLocalHom
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating
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
theorem _root_.solution (hR : ¬ IsField R) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : R →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hR
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap R (FractionRing R)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)⟩
end GlobalTheory
