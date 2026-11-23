-- Prove2me | solution 1 for GlobalTheory.KS.Sym.pbT_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:37.26464+00:00
-- url     : https://prove2.me/submissions/90ba124c-d0b2-4fe7-b907-dbc3514a6dc5

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
theorem _root_.solution {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : pbT (𝟙 Y) s O = rsT s O := by
  unfold pbT rsT
  by_cases h : O ≤ O₀
  · rw [dif_pos (show O ≤ 𝟙 Y ⁻¹ᵁ O₀ from h), dif_pos h]
    rfl
  · rw [dif_neg (show ¬O ≤ 𝟙 Y ⁻¹ᵁ O₀ from h), dif_neg h]
end GlobalTheory.KS.Sym
