-- Prove2me | solution 1 for GlobalTheory.LevelPairing.zpow_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:38.353264+00:00
-- url     : https://prove2.me/submissions/6ebb1ef0-0fb9-4077-aa3d-3234311f1cbd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_zetaM_prim

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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution (c : Coeff l) {a b : ℤ} (h : (l.M : ℤ) ∣ a - b) : zetaM c ^ a = zetaM c ^ b := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : zetaM c ≠ 0 := (zetaM_prim c).ne_zero hM
  have := ((zetaM_prim c).zpow_eq_one_iff_dvd (a - b)).2 h
  rw [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  exact this
end GlobalTheory.LevelPairing
