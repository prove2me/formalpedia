-- Prove2me | solution 1 for GlobalTheory.GradedFixed.le_WA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:45.631945+00:00
-- url     : https://prove2.me/submissions/54aa1d4b-234d-447b-a612-988eeed44acb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.GradedFixed
theorem _root_.solution (V : ι → Submodule ℂ M) {A : Set ι} {j : ι} (hj : j ∈ A) : V j ≤ WA V A :=
  le_iSup₂_of_le j hj le_rfl
end GlobalTheory.GradedFixed
