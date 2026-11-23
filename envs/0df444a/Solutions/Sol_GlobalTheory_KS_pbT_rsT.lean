-- Prove2me | solution 1 for GlobalTheory.KS.pbT_rsT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:30.94682+00:00
-- url     : https://prove2.me/submissions/88e5f00e-8978-4016-bb5b-730720387c8b

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
theorem _root_.solution (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁)
    (s : Γ(Y, O₀)) : pbT f (rsT s O₁) O₂ = pbT f s O₂ := by
  rw [rsT_of_le h₁, pbT_of_le f h₂, pbT_of_le f (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.map_appLE f h₂ (homOfLE h₁).op)
end GlobalTheory.KS
