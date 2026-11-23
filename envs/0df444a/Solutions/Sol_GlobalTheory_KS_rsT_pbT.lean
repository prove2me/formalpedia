-- Prove2me | solution 1 for GlobalTheory.KS.rsT_pbT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:30.885419+00:00
-- url     : https://prove2.me/submissions/c175a58a-4251-43e9-9fe7-1a6fa6a5bceb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Theorems.Thm_GlobalTheory_KS_rsT_of_le
import Theorems.Thm_GlobalTheory_KS_pbT_of_le

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
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {Y Z : Scheme.{0}}
namespace GlobalTheory.KS
theorem _root_.solution (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(Y, O₀)) : rsT (pbT f s O₁) O₂ = pbT f s O₂ := by
  rw [pbT_of_le f h₁, rsT_of_le h₂, pbT_of_le f (h₂.trans h₁)]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_map f h₁ (homOfLE h₂).op)
end GlobalTheory.KS
