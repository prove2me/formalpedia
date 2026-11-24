-- Prove2me | solution 1 for GlobalTheory.LevelCoverDatum.Mb_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:56.774575+00:00
-- url     : https://prove2.me/submissions/3df89920-0a0a-483c-a5b8-27f5f177a3ae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_AdmissibleSmulIffOfCoprime

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
open GlobalTheory GlobalTheory.LevelCoverDatum
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj GlobalTheory.LevelPairing
open CategoryTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
namespace GlobalTheory.LevelCoverDatum
theorem _root_.solution (l : Level H) : l.Mb ≠ ⊥ := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  intro h
  have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  have := this (Ideal.subset_span rfl)
  rw [h, Ideal.mem_bot] at this
  exact hM (by exact_mod_cast this)
end GlobalTheory.LevelCoverDatum
