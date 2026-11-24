-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.card_ne_zero_of_perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:07.316632+00:00
-- url     : https://prove2.me/submissions/d3b66f29-bc30-4f75-85d5-f3cafe811893

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
variable [Fintype A] [Fintype B]
omit [Fintype B]
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    (Fintype.card A : K) ≠ 0 := by
  intro h
  obtain ⟨p, hp⟩ := CharP.exists K
  have hd : p ∣ Fintype.card A := (CharP.cast_eq_zero_iff K p _).mp h
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact Fintype.card_ne_zero (zero_dvd_iff.mp hd)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card p hd
  have h0 : a = 0 := he.nondeg_left a fun t => by
    have h1 : chr he t a ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, ← ha, addOrderOf_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have h2 : (chr he t a - 1) ^ p = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff hp0 |>.mp h2))
  rw [h0, addOrderOf_zero] at ha
  exact (Fact.out : p.Prime).one_lt.ne ha
end GlobalTheory.FourierChainCompare
