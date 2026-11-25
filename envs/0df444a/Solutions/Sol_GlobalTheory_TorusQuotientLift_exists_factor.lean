-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:59.809457+00:00
-- url     : https://prove2.me/submissions/2475852a-979f-4293-aeb5-d208c4a22236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
namespace GlobalTheory.TorusQuotientLift
theorem _root_.solution {R T C : Type} [CommRing R] [CommRing T] [CommRing C] (f : R →+* C)
    (hf : Function.Injective f) (g : T →+* C) (h : ∀ t, ∃ r, f r = g t) : ∃ k : T →+* R, ∀ t, f (k t) = g t := by
  choose k hk using h
  exact ⟨⟨⟨⟨k, hf (by rw [hk, map_one, map_one])⟩, fun a b => hf (by simp only [hk, map_mul])⟩,
    hf (by rw [hk, map_zero, map_zero]), fun a b => hf (by simp only [hk, map_add])⟩, hk⟩
end GlobalTheory.TorusQuotientLift
