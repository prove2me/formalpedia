-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.mem_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:04.575704+00:00
-- url     : https://prove2.me/submissions/81acea48-9d8a-4f74-94de-601128defb51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ↔
      coeff 0 f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff, coeff_zero_eq_constantCoeff_apply]
end GlobalTheory.FiltrationMultiplicative
