-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.zeta_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:48:09.873847+00:00
-- url     : https://prove2.me/submissions/5a1e596e-fe26-47da-a50b-b62edb446e10

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant

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
open GlobalTheory GlobalTheory.ShortDatumEq
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
namespace GlobalTheory.ShortDatumEq
theorem _root_.solution (c : Coeff l) (m : ℤ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ^ m = GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ^ (m : ZMod l.M).val := by
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  have hz := zetaM_prim c
  have hne : GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ≠ 0 := hz.ne_zero (NeZero.ne _)
  rw [← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv m l.M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hz.pow_eq_one, one_zpow, _root_.mul_one]
end GlobalTheory.ShortDatumEq
