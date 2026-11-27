-- Prove2me | solution 1 for GlobalTheory.TorsionRepresent.comp_incl_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:24.809962+00:00
-- url     : https://prove2.me/submissions/2eb45cb0-6481-462a-9d3c-2d23f43c809d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionFiniteFlatIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionRepresent
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ)
namespace GlobalTheory.TorsionRepresent
theorem _root_.solution {T : Over S} (y : T ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k) : (y ≫ incl G k) ^ k = 1 := by
  have h : incl G k ≫ ((𝟙 G : G ⟶ G) ^ k) = pullback.snd ((𝟙 G : G ⟶ G) ^ k) η[G] ≫ η[G] := pullback.condition
  rw [MonObj.comp_pow, Category.comp_id] at h
  have h1 : incl G k ^ k = 1 := by
    rw [h, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [← MonObj.comp_pow, h1, MonObj.comp_one]
end GlobalTheory.TorsionRepresent
