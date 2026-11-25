-- Prove2me | solution 1 for GlobalTheory.LevelCoverDatum.noDelta_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:19.186548+00:00
-- url     : https://prove2.me/submissions/a4ec6757-76b9-4c76-9ccd-c87880290f22

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
theorem _root_.solution (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) (x0 : Fin n → Dw.La) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).w x0 = _root_.Formalism.L2.Pj.x0Dat c x0 := by
  funext q
  apply Subtype.ext
  simp only [_root_.Formalism.L2.Pj.DeltaDat.w, _root_.Formalism.L2.Pj.noDelta, mul_one]
  unfold _root_.Formalism.L2.Pj.x0Dat
  rfl
end _root_.GlobalTheory.LevelCoverDatum
end GlobalTheory.LevelCoverDatum
