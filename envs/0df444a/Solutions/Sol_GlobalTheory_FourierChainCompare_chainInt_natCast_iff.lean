-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.chainInt_natCast_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:04.368191+00:00
-- url     : https://prove2.me/submissions/34d5e6c2-9b67-4967-a11d-eb730f777b67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_act_natCast

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
theorem _root_.solution {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (P : MvPolynomial ι R) (k n : ℕ) (f : PS R 1 d) :
    (constantCoeff (DpolyOf G.F u P (ev ![mulN G n] f)) =
        (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)) ↔
      constantCoeff (DpolyOf G.F u P (ev ![A.act (((n : ℤ) : O))] f)) =
        (((n : ℤ) : R)) ^ k * constantCoeff (DpolyOf G.F u P f) := by
  rw [act_natCast, Int.cast_natCast]
end GlobalTheory.FourierChainCompare
