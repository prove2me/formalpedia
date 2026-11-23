-- Prove2me | solution 1 for GlobalTheory.KS.Sym.pbT_pbT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:32.390249+00:00
-- url     : https://prove2.me/submissions/0a397eb9-f0a1-4468-a0ae-d68d60309beb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
namespace GlobalTheory.KS.Sym
theorem _root_.solution (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ g ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) : pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  have h₃ : O₂ ≤ (f ≫ g) ⁻¹ᵁ O₀ := h₂.trans (fun x hx => h₁ hx)
  unfold pbT
  rw [dif_pos h₁, dif_pos h₂, dif_pos h₃, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.KS.Sym
