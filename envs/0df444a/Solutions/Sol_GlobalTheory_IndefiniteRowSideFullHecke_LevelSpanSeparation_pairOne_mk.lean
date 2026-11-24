-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.pairOne_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:26.695819+00:00
-- url     : https://prove2.me/submissions/dbd28cc9-6a61-4853-b229-ac2f8ec8c854

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable (D : Datum H) (l : Level H)
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
theorem _root_.solution {c : 𝓞 E} (hc : IsSep l c) (u v : D.La) :
    pairOne D l (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ((D.EF u (c • v) : ℤ) : ZMod l.M) := by
  change ((D.EF u (sep l • v) : ℤ) : ZMod l.M) = _
  have h1 := ef_smul_eq_zero D l hc.2 (sep_spec l).1 u v
  have h2 := ef_smul_eq_zero D l (sep_spec l).2 hc.1 u v
  rw [sub_mul, _root_.one_mul, sub_smul, map_sub, Int.cast_sub, sub_eq_zero] at h1 h2
  rw [← h1, ← h2, mul_comm]
end GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
