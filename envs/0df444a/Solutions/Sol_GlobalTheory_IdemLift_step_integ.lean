-- Prove2me | solution 1 for GlobalTheory.IdemLift.step_integ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:35.121307+00:00
-- url     : https://prove2.me/submissions/98b0dfbb-4cf9-4106-aca0-2266a0168ef3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_add
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_mul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.IdemLift
open Filter Topology
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.IdemLift
theorem _root_.solution {y : Matrix (Fin n) (Fin n) E} (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖step y i j‖ ≤ 1 := by
  have h2 := integ_mul hy hy
  have h3 := integ_mul h2 hy
  exact integ_sub (integ_add (integ_add h2 h2) h2) (integ_add h3 h3)
end GlobalTheory.IdemLift
