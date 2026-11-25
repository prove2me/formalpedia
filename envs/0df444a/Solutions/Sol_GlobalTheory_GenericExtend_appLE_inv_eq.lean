-- Prove2me | solution 1 for GlobalTheory.GenericExtend.appLE_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:15:03.589317+00:00
-- url     : https://prove2.me/submissions/5a80169b-06c7-40a0-830e-224df05602e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution {P Q H Z : Scheme.{0}} {J : Q ⟶ P} {φ : H ⟶ P} {k : Z ⟶ H} {ψ : Z ⟶ Q}
    {A : P.Opens} (hW : k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A) {s : Γ(H, φ ⁻¹ᵁ A)ˣ} {τ : Γ(Q, J ⁻¹ᵁ A)ˣ}
    (hu : res le_rfl (pullU k _ s) = res hW (pullU ψ _ τ)) :
    (k.appLE _ _ le_rfl).hom s.val = (ψ.appLE _ _ hW).hom τ.val ∧
      (k.appLE _ _ le_rfl).hom (s⁻¹).val = (ψ.appLE _ _ hW).hom (τ⁻¹).val := by
  have hu' : res le_rfl (pullU k _ s⁻¹) = res hW (pullU ψ _ τ⁻¹) := by
    rw [map_inv (pullU k _), map_inv (pullU ψ _), map_inv (res le_rfl), map_inv (res hW), hu]
  exact ⟨congrArg Units.val hu, congrArg Units.val hu'⟩
end GlobalTheory.GenericExtend
