-- Prove2me | solution 1 for GlobalTheory.OppRad.S_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:09.662198+00:00
-- url     : https://prove2.me/submissions/85c9f1b3-2415-489c-93c4-739465f8c71c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
namespace GlobalTheory.OppRad
theorem _root_.solution (H : Subgroup G) [Fintype H] (v : V) : S π H v = ∑ h : H, π h v := by
  rw [S, LinearMap.sum_apply]
  congr!
end GlobalTheory.OppRad
