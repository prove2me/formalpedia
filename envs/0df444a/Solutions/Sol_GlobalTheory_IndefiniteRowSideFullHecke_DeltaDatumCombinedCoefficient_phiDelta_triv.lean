-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.phiDelta_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:41.131839+00:00
-- url     : https://prove2.me/submissions/b8c0db18-c7fa-4207-91d5-08a14982219e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H}
namespace GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
theorem _root_.solution (F : Type) [Field F] (v : Vol D (IsAuxiliarySplitSquarefreeLevel.triv l)) {n : ℕ}
    (x : Fin n → ConjCl D (IsAuxiliarySplitSquarefreeLevel.triv l).l₂) : phiDelta (DeltaChar.triv l F) v x = 1 := by
  change (1 : MulChar _ F)⁻¹ _ = 1
  rw [inv_one, MulChar.one_apply (isUnit_of_subsingleton _)]
end GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
