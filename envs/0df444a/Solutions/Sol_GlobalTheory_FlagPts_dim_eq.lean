-- Prove2me | solution 1 for GlobalTheory.FlagPts.dim_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:21.687832+00:00
-- url     : https://prove2.me/submissions/c375aab5-ba4f-40cd-ba2b-70ef56590f32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {k V}
namespace GlobalTheory.FlagPts
theorem _root_.solution {s : Closeds (Flags k V)} {n : ℕ} (h : topologicalKrullDim (s : Set (Flags k V)) = n) : dim s = n := by
  rw [dim, h]
  rfl
end GlobalTheory.FlagPts
