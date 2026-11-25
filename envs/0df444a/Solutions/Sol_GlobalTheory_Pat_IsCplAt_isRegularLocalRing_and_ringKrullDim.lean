-- Prove2me | solution 1 for GlobalTheory.Pat.IsCplAt.isRegularLocalRing_and_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:08:03.330065+00:00
-- url     : https://prove2.me/submissions/b8c93e19-7a18-4413-a1c9-e60c9ed3951b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_isRegularLocalRing_of_flat_of_map_eq_maximalIdeal
import Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
namespace GlobalTheory
namespace Pat.IsCplAt
theorem _root_.solution :
    ∀ (R S : Type) [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
      [q.IsPrime] (φ : R →+* S), IsCplAt q φ →
      ∃ _ : IsRegularLocalRing S, ringKrullDim S + ringKrullDim (R ⧸ q) = ringKrullDim R := by
  intro R S _ _ _ _ q _ φ h
  let _ : Algebra R S := φ.toAlgebra
  have := h.noeth
  have : Module.Flat R S := h.flat
  have hq : maximalIdeal S = q.map (algebraMap R S) := h.max_eq
  refine ⟨isRegularLocalRing_of_flat_of_map_eq_maximalIdeal R S q hq, ?_⟩
  have : (maximalIdeal S).LiesOver q := ⟨h.comap_eq.symm⟩
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q (maximalIdeal S)
  have e0 : (Ideal.map (Ideal.Quotient.mk (q.map (algebraMap R S))) (maximalIdeal S)).height = 0 := by
    have hp : (q.map (algebraMap R S)).IsPrime := hq ▸ inferInstance
    rw [hq, Ideal.map_quotient_self, Ideal.height_bot]
  rw [e0, add_zero] at e
  rw [← maximalIdeal_height_eq_ringKrullDim, e]
  exact (isCM_of_isRegularLocalRing R).height_add_ringKrullDim_quotient q
end Pat.IsCplAt
end GlobalTheory
