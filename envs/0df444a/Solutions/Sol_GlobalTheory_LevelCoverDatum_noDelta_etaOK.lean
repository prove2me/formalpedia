-- Prove2me | solution 1 for GlobalTheory.LevelCoverDatum.noDelta_etaOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:26.828212+00:00
-- url     : https://prove2.me/submissions/cfb4fd02-4a80-435b-9b09-7aaea129404f

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
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).EtaOK ↔ (∀ a, (Xo.univ.eta a).left ≫ m.φ = (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA a).left ≫ m.φ = (Xo.univ.etaA a).left := by
  simp only [_root_.Formalism.L2.Pj.DeltaDat.EtaOK, _root_.Formalism.L2.Pj.noDelta, Nat.div_self l.A_pos, Category.id_comp]
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_) <;>
  · apply Iff.of_eq
    congr 3
    open scoped MonObj in exact pow_one _
end _root_.GlobalTheory.LevelCoverDatum
end GlobalTheory.LevelCoverDatum
