-- Prove2me | solution 1 for GlobalTheory.KS.EpsBundle.unit_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:25:57.141801+00:00
-- url     : https://prove2.me/submissions/fc7751a1-4fef-4ce4-b575-37b9bc87e02a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TrivialIffCoboundary
import Theorems.Thm_GlobalTheory_KS_EpsBundle_uniq

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsBundle
namespace GlobalTheory.KS.EpsBundle
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) (u : Bˣ) :
    ∃ b b' c : A, b * b' = 1 ∧ (u : B) = φ b + e * φ c := by
  obtain ⟨⟨b, c⟩, h, -⟩ := H u
  obtain ⟨⟨b', c'⟩, h', -⟩ := H (u⁻¹ : Bˣ)
  refine ⟨b, b', c, ?_, h⟩
  have h1 : (u : B) * (u⁻¹ : Bˣ) = 1 := u.mul_inv
  rw [h', h] at h1
  refine (uniq φ e H (a := b * b') (b := b * c' + c * b') (a' := 1) (b' := 0) ?_).1
  simp only [map_mul, map_add, map_one, map_zero] at h1 ⊢
  linear_combination h1 - (φ c * φ c') * he
end GlobalTheory.KS.EpsBundle
