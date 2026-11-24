-- Prove2me | solution 1 for GlobalTheory.OppRad.S_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:21.019807+00:00
-- url     : https://prove2.me/submissions/9c261897-3b96-4f4c-8043-4b568f099808

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_S_apply
import Theorems.Thm_GlobalTheory_OppRad_S_right

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
variable {π}
namespace GlobalTheory.OppRad
theorem _root_.solution {H K : Subgroup G} (hle : H ≤ K) {v : V} (hv : S π K v = 0) : S π K (S π H v) = 0 := by
  haveI := Fintype.ofFinite H
  rw [S_apply π H, map_sum]
  exact Finset.sum_eq_zero fun u _ => by rw [S_right (hle u.2), hv]
end GlobalTheory.OppRad
