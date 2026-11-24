-- Prove2me | solution 1 for GlobalTheory.GenericHom.mul_eq_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:06.077418+00:00
-- url     : https://prove2.me/submissions/098accb8-d509-4d72-83cf-b48aebd8f926

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
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y : P)
    (h : j a * j x = j b * j y) : f a * f x = f b * f y := by
  obtain ⟨u, hu⟩ := hg [1, j x, j y, j a * j x]
  obtain ⟨c, hc⟩ := hu 1 (by simp)
  obtain ⟨p, hp⟩ := hu (j x) (by simp)
  obtain ⟨q, hq⟩ := hu (j y) (by simp)
  obtain ⟨r, hr⟩ := hu (j a * j x) (by simp)
  rw [_root_.one_mul] at hc
  have e1 := hm x c p (by rw [hc, hp])
  have e2 := hm y c q (by rw [hc, hq])
  have e3 := hm a p r (by rw [hp, hr, _root_.mul_assoc])
  have e4 := hm b q r (by rw [hq, hr, h, _root_.mul_assoc])
  apply mul_right_cancel (b := f c)
  rw [_root_.mul_assoc, _root_.mul_assoc, e1, e2, e3, e4]
end GlobalTheory.GenericHom
