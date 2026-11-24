-- Prove2me | solution 1 for GlobalTheory.GenericHom.mul_four_eq_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:30.701903+00:00
-- url     : https://prove2.me/submissions/fef73677-00c3-4ca0-b57c-166c61b7802d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.GenericHom
namespace GlobalTheory.GenericHom
theorem _root_.solution {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y c z : P)
    (h : (j a * j x) * (j b * j y) = j c * j z) : (f a * f x) * (f b * f y) = f c * f z := by
  obtain ⟨u, hu⟩ := hg [1, j y, j b * j y, j x * (j b * j y), j c * j z, j z]
  obtain ⟨p₀, h₀⟩ := hu 1 (by simp)
  obtain ⟨p₁, h₁⟩ := hu (j y) (by simp)
  obtain ⟨p₂, h₂⟩ := hu (j b * j y) (by simp)
  obtain ⟨p₃, h₃⟩ := hu (j x * (j b * j y)) (by simp)
  obtain ⟨p₄, h₄⟩ := hu (j c * j z) (by simp)
  obtain ⟨p₅, h₅⟩ := hu (j z) (by simp)
  rw [_root_.one_mul] at h₀
  have e1 := hm y p₀ p₁ (by rw [h₀, h₁])
  have e2 := hm b p₁ p₂ (by rw [h₁, h₂, _root_.mul_assoc])
  have e3 := hm x p₂ p₃ (by rw [h₂, h₃]; simp only [_root_.mul_assoc])
  have e4 := hm a p₃ p₄ (by rw [h₃, h₄, ← h]; simp only [_root_.mul_assoc])
  have e5 := hm z p₀ p₅ (by rw [h₀, h₅])
  have e6 := hm c p₅ p₄ (by rw [h₅, h₄, _root_.mul_assoc])
  apply mul_right_cancel (b := f p₀)
  simp only [_root_.mul_assoc]
  rw [e1, e2, e3, e4, e5, e6]
end GlobalTheory.GenericHom
