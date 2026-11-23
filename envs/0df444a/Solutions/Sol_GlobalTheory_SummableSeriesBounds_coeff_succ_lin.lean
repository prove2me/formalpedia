-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.coeff_succ_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:53.308808+00:00
-- url     : https://prove2.me/submissions/50730e64-7ff3-4426-8b2a-21820d88727d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution (π : C) (G : PowerSeries C) (n : ℕ) :
    coeff (n + 1) ((X - PowerSeries.C π) * G) = coeff n G - π * coeff (n + 1) G := by
  rw [sub_mul, map_sub, coeff_C_mul, coeff_succ_X_mul]
end GlobalTheory.SummableSeriesBounds
