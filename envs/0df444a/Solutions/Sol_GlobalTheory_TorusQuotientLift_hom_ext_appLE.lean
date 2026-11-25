-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.hom_ext_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:44.936969+00:00
-- url     : https://prove2.me/submissions/57a9f83b-18ca-4891-9d8b-705732e06c3f

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
theorem _root_.solution {Y B : Scheme.{0}} (f g : Y ⟶ B)
    (H : ∀ y : Y, ∃ (W : Y.Opens) (V : B.Opens) (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V), y ∈ W ∧ IsAffineOpen V ∧
      f.appLE V W hf = g.appLE V W hg) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun y => ?_
  obtain ⟨W, V, hf, hg, hy, hV, e⟩ := H y
  have key : ∀ (r : Y ⟶ B) (hr : W ≤ r ⁻¹ᵁ V), W.ι ≫ r = W.toSpecΓ ≫ Spec.map (r.appLE V W hr) ≫ hV.fromSpec := by
    intro r hr
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hV.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  exact ⟨W, hy, by rw [key f hf, key g hg, e]⟩
end GlobalTheory.TorusQuotientLift
