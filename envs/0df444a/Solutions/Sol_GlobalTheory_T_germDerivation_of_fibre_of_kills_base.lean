-- Prove2me | solution 1 for GlobalTheory.T.germDerivation_of_fibre_of_kills_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:15.509743+00:00
-- url     : https://prove2.me/submissions/38c73274-4c82-43ea-a811-b10d73819a6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBaseStatement
import Theorems.Thm_GlobalTheory_KS_ptDer_of_fibre


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
theorem _root_.solution : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  first | exact @GlobalTheory.KS.ptDer_of_fibre | exact GlobalTheory.KS.ptDer_of_fibre | (intros; apply GlobalTheory.KS.ptDer_of_fibre <;> assumption)
end _root_.GlobalTheory.T
