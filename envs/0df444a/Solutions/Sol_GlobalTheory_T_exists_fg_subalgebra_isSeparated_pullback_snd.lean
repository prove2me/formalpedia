-- Prove2me | solution 1 for GlobalTheory.T.exists_fg_subalgebra_isSeparated_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:55.311302+00:00
-- url     : https://prove2.me/submissions/bbe787f7-46cb-4bfb-9521-663064a23771

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFgIsSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFgIsSeparatedStatement
import Theorems.Thm_GlobalTheory_SpreadSep_exists_fg_isSeparated


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), LocallyOfFiniteType p → QuasiCompact p → IsSeparated (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.SpreadSep.exists_fg_isSeparated | exact GlobalTheory.SpreadSep.exists_fg_isSeparated | (intros; apply GlobalTheory.SpreadSep.exists_fg_isSeparated <;> assumption)
end _root_.GlobalTheory.T
