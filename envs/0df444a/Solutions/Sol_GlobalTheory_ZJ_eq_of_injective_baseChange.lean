-- Prove2me | solution 1 for GlobalTheory.ZJ.eq_of_injective_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:55.310263+00:00
-- url     : https://prove2.me/submissions/a0ae98fc-abca-406f-94c8-b748d4f05bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') (h ≫ s) q) (w : a ≫ h = h' ≫ b)
    (hinj : Function.Injective h') {x y : H} (hxy : h x = h y) (hx : s (h x) ∈ Set.range q) : x = y := by
  have sq : IsPullback a h' h b := IsPullback.of_bot hH w hX
  obtain ⟨t, ht⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hX (h x) t ht.symm
  obtain ⟨x', rfl, hx'⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
  obtain ⟨y', rfl, hy'⟩ := Scheme.exists_preimage_of_isPullback sq y z (hxy.symm.trans hz.symm)
  rw [hinj (hx'.trans hy'.symm)]
end GlobalTheory.ZJ
