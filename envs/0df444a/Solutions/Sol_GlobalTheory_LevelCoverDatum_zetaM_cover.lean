-- Prove2me | solution 1 for GlobalTheory.LevelCoverDatum.zetaM_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:05.384152+00:00
-- url     : https://prove2.me/submissions/18147ff8-538e-4a25-b91f-b845a7129513

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_AdmissibleSmulIffOfCoprime
import Theorems.Thm_GlobalTheory_LevelPairing_zetaM_coe


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
theorem _root_.solution (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.l₂.M = l.M * d.pd) :
    _root_.Formalism.L2.Pj.zetaM d.c₂ ^ d.pd = d.eF (_root_.Formalism.L2.Pj.zetaM c) := by
  have h3 := d.l₂.three_le
  rw [h] at h3
  have hM : l.M ≠ 0 := fun h0 => by rw [h0, zero_mul] at h3; omega
  have hp : d.pd ≠ 0 := fun h0 => by rw [h0, mul_zero] at h3; omega
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow]
  change ((_root_.Formalism.L2.Pj.zetaM d.c₂ : ℂ)) ^ d.pd = (_root_.Formalism.L2.Pj.zetaM c : ℂ)
  rw [_root_.GlobalTheory.LevelPairing.zetaM_coe, _root_.GlobalTheory.LevelPairing.zetaM_coe, h]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
end _root_.GlobalTheory.LevelCoverDatum
end GlobalTheory.LevelCoverDatum
