-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.chainInt_iff_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:04.079053+00:00
-- url     : https://prove2.me/submissions/ca3ae752-5bdb-4bfa-9a7c-ff659d8658bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_chainIntOn_nonneg
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_one


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
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution (H : NChainSt) : ChainInt ↔ ChainIntOn {-1} := by
  refine ⟨fun H' R _ d G O _ A ι _ u P k hP n _ f => H' R d G O A ι u P k hP n f, fun H' => ?_⟩
  intro R _ d G O _ A ι _ u P k hP n f
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact chainIntOn_nonneg H R d G O A ι u P k hP m (Int.natCast_nonneg m) f
  · have e : ev ![A.act ((-(m : ℤ) : ℤ) : O)] f =
        ev ![A.act ((-1 : ℤ) : O)] (ev ![A.act ((m : ℤ) : O)] f) := by
      rw [GlobalTheory.GaugeAdjoint.ev_ev_one (A.const _) (GlobalTheory.GaugeAdjoint.const_one (A.const _)),
        show ((-(m : ℤ) : ℤ) : O) = ((m : ℤ) : O) * ((-1 : ℤ) : O) by push_cast; ring, A.mul_act]
      rfl
    rw [e, H' R d G O A ι u P k hP (-1) rfl,
      chainIntOn_nonneg H R d G O A ι u P k hP m (Int.natCast_nonneg m) f, ← mul_assoc, ← mul_pow]
    push_cast
    rw [neg_one_mul]
end GlobalTheory.FourierChainCompare
