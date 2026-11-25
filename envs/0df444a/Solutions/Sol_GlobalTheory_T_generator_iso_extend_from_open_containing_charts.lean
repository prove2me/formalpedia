-- Prove2me | solution 1 for GlobalTheory.T.generator_iso_extend_from_open_containing_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:22.619549+00:00
-- url     : https://prove2.me/submissions/53d0ecc8-4546-4ce4-93ff-ceee522f9852

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingChartsStatement
import Theorems.Thm_GlobalTheory_GenPush_gen_iso_of_charts_le_range


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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  first | exact @GlobalTheory.GenPush.gen_iso_of_charts_le_range | exact GlobalTheory.GenPush.gen_iso_of_charts_le_range | (intros; apply GlobalTheory.GenPush.gen_iso_of_charts_le_range <;> assumption)
end _root_.GlobalTheory.T
