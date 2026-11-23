-- Prove2me | solution 1 for GlobalTheory.LocDerExt.der_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:49.033256+00:00
-- url     : https://prove2.me/submissions/7941769e-7e30-412b-8eca-08837d2d0f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine

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
open GlobalTheory GlobalTheory.LocDerExt
namespace GlobalTheory.LocDerExt
theorem _root_.solution {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (δ₁ δ₂ : B → C)
    (h₁ : ∀ a b, δ₁ (a * b) = φ a * δ₁ b + φ b * δ₁ a)
    (h₂ : ∀ a b, δ₂ (a * b) = φ a * δ₂ b + φ b * δ₂ a)
    (h : ∀ a, δ₁ (algebraMap A B a) = δ₂ (algebraMap A B a)) (s : B) : δ₁ s = δ₂ s := by
  obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) s
  have hu : IsUnit (φ (algebraMap A B t)) := (IsLocalization.map_units B t).map φ
  have e₁ := h₁ s (algebraMap A B t)
  have e₂ := h₂ s (algebraMap A B t)
  dsimp only at e
  rw [e] at e₁ e₂
  rw [h, e₂, h] at e₁
  exact (hu.mul_left_cancel (add_left_cancel e₁)).symm
end GlobalTheory.LocDerExt
