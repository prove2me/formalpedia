-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.eq_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:42.711723+00:00
-- url     : https://prove2.me/submissions/222b8b7d-ef94-49e6-b008-41fc0779e46c

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
theorem _root_.solution (a : IsAuxiliarySplitSquarefreeLevel l) (jK : KA l →+* KA a.l₂) (hj : ∀ x, ((jK x : KA a.l₂) : ℂ) = ((x : KA l) : ℂ)) :
    jK = (IntermediateField.inclusion a.KA_le).toRingHom :=
  RingHom.ext fun x => Subtype.ext ((hj x).trans (IntermediateField.coe_inclusion a.KA_le x).symm)
end GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
