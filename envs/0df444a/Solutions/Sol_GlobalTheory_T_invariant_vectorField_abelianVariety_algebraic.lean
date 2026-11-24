-- Prove2me | solution 1 for GlobalTheory.T.invariant_vectorField_abelianVariety_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:28.835525+00:00
-- url     : https://prove2.me/submissions/07b9d38b-ca3d-4406-8153-d23009d72294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Theorems.Thm_GlobalTheory_KS_invariant_field_algebraic


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ w : (Fin P₀.g → ℂ), ∃ d, LocDer P₀.A.hom P₀.A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left ((𝟙 P₀.A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  first | exact @GlobalTheory.KS.invariant_field_algebraic | exact GlobalTheory.KS.invariant_field_algebraic | (intros; apply GlobalTheory.KS.invariant_field_algebraic <;> assumption)
end _root_.GlobalTheory.T
