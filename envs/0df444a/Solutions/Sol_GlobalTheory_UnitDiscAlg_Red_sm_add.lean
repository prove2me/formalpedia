-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.Red.sm_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:51.913841+00:00
-- url     : https://prove2.me/submissions/e9083bec-e6b8-4e65-909c-dd638469692c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.UnitDiscAlg.Red
theorem _root_.solution {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : Sm y) : Sm (x + y) := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hx i j) (hy i j))
end GlobalTheory.UnitDiscAlg.Red
