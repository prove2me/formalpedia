-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.coeff_zero_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:16.172821+00:00
-- url     : https://prove2.me/submissions/172b98c0-14be-4723-a742-318b9cb7536e

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
theorem _root_.solution (π : C) (G : PowerSeries C) :
    coeff 0 ((X - PowerSeries.C π) * G) = -(π * coeff 0 G) := by
  rw [sub_mul, map_sub, coeff_C_mul]
  simp
end GlobalTheory.SummableSeriesBounds
