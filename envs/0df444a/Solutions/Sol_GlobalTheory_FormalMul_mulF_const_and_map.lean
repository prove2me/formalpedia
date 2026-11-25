-- Prove2me | solution 1 for GlobalTheory.FormalMul.mulF_const_and_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:49.977576+00:00
-- url     : https://prove2.me/submissions/52cab2b0-4edd-46a8-a59a-9bc4efa043d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MulFConstAndMap
import Theorems.Thm_GlobalTheory_FormalMul_constantCoeff_mulF
import Theorems.Thm_GlobalTheory_FormalMul_mulF_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.FormalMul
namespace GlobalTheory.FormalMul
theorem _root_.solution : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (d : ℕ) (F : FGLaw T d)
    (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0 ∧
      mulF (F.mapF io) N j = MvPowerSeries.map io (mulF F.F N j) :=
  fun _ _ _ _ io _ F N j => ⟨constantCoeff_mulF F.F F.const N j, mulF_map io F.F F.const N j⟩
end GlobalTheory.FormalMul
