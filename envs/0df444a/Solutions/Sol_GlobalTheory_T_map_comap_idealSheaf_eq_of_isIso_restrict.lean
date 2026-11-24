-- Prove2me | solution 1 for GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:05.939427+00:00
-- url     : https://prove2.me/submissions/606dc3f9-c18c-420c-89bb-79302c725b18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrictStatement
import Theorems.Thm_GlobalTheory_MapComapIso_map_comap_ideal_eq_of_isIso_restrict


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by
  first | exact @GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | exact GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | (intros; apply GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict <;> assumption)
end _root_.GlobalTheory.T
