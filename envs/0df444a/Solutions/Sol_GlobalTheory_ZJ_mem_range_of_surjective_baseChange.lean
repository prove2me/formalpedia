-- Prove2me | solution 1 for GlobalTheory.ZJ.mem_range_of_surjective_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:52.130259+00:00
-- url     : https://prove2.me/submissions/7d6bcd9e-540c-4294-a7b6-f6309af0cf4b

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
    (hX : IsPullback b s' s q) (w : a ≫ h = h' ≫ b)
    (hsurj : Function.Surjective h') {z : X} (hz : s z ∈ Set.range q) : z ∈ Set.range h := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨z', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hX z t ht.symm
  obtain ⟨x, rfl⟩ := hsurj z'
  exact ⟨a x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩
end GlobalTheory.ZJ
