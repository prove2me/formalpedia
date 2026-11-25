-- Prove2me | solution 1 for GlobalTheory.FiniteColength.map_maximalIdeal_eq_ker_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:52.740237+00:00
-- url     : https://prove2.me/submissions/301deecd-7383-47bd-9599-8fea7f300faa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MapMaximalIdealEqKerMapResidue
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_mem_map_C_of_coeff_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.FiniteColength
namespace GlobalTheory.FiniteColength
theorem _root_.solution (T : Type) [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (σ : Type) :
    (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)) =
      RingHom.ker (MvPowerSeries.map (σ := σ) (residue T)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change MvPowerSeries.map (residue T) (MvPowerSeries.C r) = 0
    rw [MvPowerSeries.map_C, (residue_eq_zero_iff r).2 hr, map_zero]
  · intro g hg
    refine GlobalTheory.FormalIsogeny.mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => ?_
    rw [← residue_eq_zero_iff, ← MvPowerSeries.coeff_map, RingHom.mem_ker.1 hg, map_zero]
end GlobalTheory.FiniteColength
