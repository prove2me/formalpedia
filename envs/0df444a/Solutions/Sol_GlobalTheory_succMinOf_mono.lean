-- Prove2me | solution 1 for GlobalTheory.succMinOf_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:43.586624+00:00
-- url     : https://prove2.me/submissions/e3f68ac3-51dc-4122-b2de-ae97d68c5205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable (K : Type*) [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {K}
variable {N N' : V → ℝ} {S S' : Set V} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution (hij : i ≤ j) (hj : (j : Cardinal) ≤ Module.rank K (span K S)) :
    succMinOf K N S i ≤ succMinOf K N S j :=
  le_succMinOf hj fun _ hr => succMinOf_le_of_mem
    ⟨hr.1, (Nat.cast_le.2 hij).trans hr.2⟩
end GlobalTheory
