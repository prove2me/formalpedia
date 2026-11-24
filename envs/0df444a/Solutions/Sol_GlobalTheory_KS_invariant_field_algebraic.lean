-- Prove2me | solution 1 for GlobalTheory.KS.invariant_field_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:36:07.622825+00:00
-- url     : https://prove2.me/submissions/35e0ab66-9c2f-4376-aa6a-b1b23a6047d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationOfDualNumberThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraic
import Theorems.Thm_GlobalTheory_KS_exists_locDer_of_isDiff

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
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ w : (Fin P₀.g → ℂ), ∃ d, LocDer P₀.A.hom P₀.A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left ((𝟙 P₀.A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  intro P₀ u Hm χ hU w
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := hU.tan₂ w
  exact exists_locDer_of_isDiff P₀.A u w v hv hd
end GlobalTheory.KS
