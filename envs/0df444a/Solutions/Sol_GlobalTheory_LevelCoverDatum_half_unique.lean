-- Prove2me | solution 1 for GlobalTheory.LevelCoverDatum.half_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:03:20.200161+00:00
-- url     : https://prove2.me/submissions/e21a43c7-7331-42a2-9c80-6243165b4844

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_AdmissibleSmulIffOfCoprime
import Theorems.Thm_GlobalTheory_LevelCoverDatum_Mb_ne_bot

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
theorem _root_.solution (d d' : DeltaDat Xo c n) (h : d.IsLev) (h' : d'.IsLev) (e : d.l₂ = d'.l₂) :
    d.I = d'.I ∧ d.pd = d'.pd := by
  have hM : 0 < l.M := by have := l.three_le; omega
  refine ⟨mul_left_cancel₀ (Mb_ne_bot l) ?_, Nat.eq_of_mul_eq_mul_left hM ?_⟩
  · rw [← h.2.2.2.1, ← h'.2.2.2.1, e]
  · rw [← h.2.1, ← h'.2.1, e]
end GlobalTheory.LevelCoverDatum
