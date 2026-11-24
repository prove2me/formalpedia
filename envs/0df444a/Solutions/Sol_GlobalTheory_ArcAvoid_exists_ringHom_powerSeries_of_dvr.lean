-- Prove2me | solution 1 for GlobalTheory.ArcAvoid.exists_ringHom_powerSeries_of_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:43.332212+00:00
-- url     : https://prove2.me/submissions/8d90b993-7102-42b3-87f0-e0914c0a39c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingEquivPowerSeriesOfComplete
import Theorems.Thm_GlobalTheory_ArcAvoid_exists_ringEquiv_powerSeries_of_complete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ArcAvoid
namespace GlobalTheory.ArcAvoid
theorem _root_.solution {k V : Type*} [Field k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : k →+* V) (hι : Function.Surjective ((residue V).comp ι)) :
    ∃ φ : V →+* PowerSeries k, Function.Injective φ ∧ (∀ a, φ (ι a) = PowerSeries.C a) ∧
      ∀ v, v ∈ maximalIdeal V ↔ PowerSeries.constantCoeff (φ v) = 0 := by
  let O := AdicCompletion (maximalIdeal V) V
  obtain ⟨e, he⟩ := exists_ringEquiv_powerSeries_of_complete ((algebraMap V O).comp ι) (by
    intro y
    obtain ⟨z, rfl⟩ := (AdicCompletion.residueField_map_bijective V).2 y
    obtain ⟨a, rfl⟩ := hι z
    exact ⟨a, rfl⟩)
  refine ⟨(e.symm : O →+* PowerSeries k).comp (algebraMap V O),
    e.symm.injective.comp (algebraMap_adicCompletion_injective_of_dvr V), fun a => ?_, fun v => ?_⟩
  · exact e.symm_apply_eq.mpr (he a).symm
  · rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (algebraMap V O),
      ← isUnit_map_iff e.symm, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
    rfl
end GlobalTheory.ArcAvoid
