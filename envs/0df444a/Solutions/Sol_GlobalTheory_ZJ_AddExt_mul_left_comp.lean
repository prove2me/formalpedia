-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.mul_left_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:56.111849+00:00
-- url     : https://prove2.me/submissions/342d16b8-08a3-442a-b515-19f598384e13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {r : T ⟶ S} {r' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ r = r') (c d : Over.mk r ⟶ H) (c' d' : Over.mk r' ⟶ H) (hc : c'.left = g ≫ c.left)
    (hd : d'.left = g ≫ d.left) : (c' * d').left = g ≫ (c * d).left := by
  let u : Over.mk r' ⟶ Over.mk r := Over.homMk g hg
  have e₁ : c' = u ≫ c := Over.OverMorphism.ext hc
  have e₂ : d' = u ≫ d := Over.OverMorphism.ext hd
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl
end GlobalTheory.ZJ.AddExt
