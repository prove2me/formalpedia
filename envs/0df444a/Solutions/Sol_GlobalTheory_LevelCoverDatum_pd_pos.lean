-- Prove2me | solution 1 for GlobalTheory.LevelCoverDatum.pd_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:59.02103+00:00
-- url     : https://prove2.me/submissions/23cfabff-cd33-44e2-8c2f-be229ff110f4

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
set_option autoImplicit false
open NumberField
open CategoryTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ}
namespace GlobalTheory.LevelCoverDatum
namespace _root_.GlobalTheory.LevelCoverDatum
theorem _root_.solution (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) : 0 < d.pd := by
  obtain ⟨-, hM, -⟩ := h
  have h3 := d.l₂.three_le
  rw [hM] at h3
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, mul_zero] at h3
  omega
end _root_.GlobalTheory.LevelCoverDatum
end GlobalTheory.LevelCoverDatum
