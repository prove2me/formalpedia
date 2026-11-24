-- Prove2me | solution 1 for GlobalTheory.MapComapIso.map_comap_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:02.053222+00:00
-- url     : https://prove2.me/submissions/5eb24fba-6bf2-41d1-a65b-34e16b824afe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrict
import Theorems.Thm_GlobalTheory_MapComapIso_map_eq_comap_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory GlobalTheory.MapComapIso
namespace GlobalTheory.MapComapIso
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).map f = I := by
  rw [map_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp]
  simp
end GlobalTheory.MapComapIso
