-- Prove2me | solution 1 for GlobalTheory.Survey.BaseClassMove.zetaM_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:51.21197+00:00
-- url     : https://prove2.me/submissions/a4ab47a3-d0cc-43d1-a154-30ebccd8575c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove

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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.BaseClassMove
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.Survey.BaseClassMove
theorem _root_.solution : zetaM c ^ l.M = 1 := by
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  unfold zetaM
  rw [← pow_mul, Nat.div_mul_cancel hM]
  apply Subtype.ext
  exact (Complex.isPrimitiveRoot_exp l.M' h0).pow_eq_one
end GlobalTheory.Survey.BaseClassMove
