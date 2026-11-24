-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.zetaM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:48:09.210746+00:00
-- url     : https://prove2.me/submissions/4f6fcdf8-dddb-4fcb-862a-5de5a013e6ec

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
theorem _root_.solution (c : Coeff l) : Formalism.L2.Pj.zetaM c = GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM' hk
  have hd : l.M' / l.M = k := by rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM)]
  apply Subtype.ext
  rw [Formalism.L2.Pj.zetaM, hd, GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM]
  change zeta l.M' ^ k = zeta l.M
  rw [zeta, zeta, ← Complex.exp_nat_mul, hk]
  congr 1
  have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  have : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  push_cast
  field_simp
end GlobalTheory.ShortDatumEq
