-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.pbT_pbT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:45.9678+00:00
-- url     : https://prove2.me/submissions/7fac60db-6bf2-4941-8d70-fcdaaf501656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHom
import Theorems.Thm_GlobalTheory_KS_pbT_of_le
import Theorems.Thm_GlobalTheory_PowLie_isTangent_iff


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvHom
namespace GlobalTheory.KS.InvHom
theorem _root_.solution {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  have h₃ : O₂ ≤ (f ≫ g) ⁻¹ᵁ O₀ := h₂.trans (f.preimage_mono h₁)
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le _ h₃]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)
end GlobalTheory.KS.InvHom
