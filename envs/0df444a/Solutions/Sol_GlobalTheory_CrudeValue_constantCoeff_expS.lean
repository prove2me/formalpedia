-- Prove2me | solution 1 for GlobalTheory.CrudeValue.constantCoeff_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:30.348564+00:00
-- url     : https://prove2.me/submissions/5f86341e-3e24-41a8-a6ba-a87989bce75e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CrudeValue
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.CrudeValue
theorem _root_.solution [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) :
    constantCoeff (FB.expS k g) = 1 := by
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [map_pow, hg, zero_pow hj, smul_zero]
end GlobalTheory.CrudeValue
