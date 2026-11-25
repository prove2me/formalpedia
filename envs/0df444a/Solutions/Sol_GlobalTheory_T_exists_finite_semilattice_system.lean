-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_semilattice_system
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:09.552251+00:00
-- url     : https://prove2.me/submissions/07ab1bc1-a9e7-48d0-87b8-01a2e78aeaec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSemilatticeSystem
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSemilatticeSystemStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_exists_finite_sys_of_separated_quasiCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | exact GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact <;> assumption)
end _root_.GlobalTheory.T
