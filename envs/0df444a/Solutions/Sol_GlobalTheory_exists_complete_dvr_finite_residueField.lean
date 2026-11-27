-- Prove2me | solution 1 for GlobalTheory.exists_complete_dvr_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:53.329359+00:00
-- url     : https://prove2.me/submissions/9ac0db86-78b0-4e8d-9be9-c02766649ad0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueFieldMapAdicCompletionSurjective
import Theorems.Thm_GlobalTheory_residueField_map_adicCompletion_surjective
import Theorems.Thm_GlobalTheory_finite_residueField_of_dominating
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating
import Theorems.Thm_GlobalTheory_injective_and_isLocalHom_adicCompletion_comp
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff_isLocalHom


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
namespace GlobalTheory
theorem _root_.solution : ∀ (D : Type) [CommRing D] [IsDomain D] [IsLocalRing D], IsNoetherianRing D → ringKrullDim D = 1 → Finite (ResidueField D) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (maximalIdeal V) V) (g : D →+* V), Function.Injective g ∧ IsLocalHom g ∧ Finite (ResidueField V) := by
  intro D _ _ _ hN hdim hF
  have hD : ¬ IsField D := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim; exact zero_ne_one hdim
  haveI : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr (by simp [hdim])
  haveI : Ring.DimensionLEOne D :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hp hpr⟩
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating D (FractionRing D) (FractionRing D) hD
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hfin : Finite (ResidueField V) := finite_residueField_of_dominating D hD V h1
  obtain ⟨hi, hl⟩ := injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap D (FractionRing D)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, hi, hl,
    Finite.of_surjective _ (residueField_map_adicCompletion_surjective V)⟩
end GlobalTheory
