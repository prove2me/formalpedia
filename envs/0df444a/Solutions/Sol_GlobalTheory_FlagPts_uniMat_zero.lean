-- Prove2me | solution 1 for GlobalTheory.FlagPts.uniMat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:45.340632+00:00
-- url     : https://prove2.me/submissions/74efa331-41f4-4223-bf2d-f2711fd82e25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {k V}
namespace GlobalTheory.FlagPts
theorem _root_.solution (i : ι) : uniMat (0 : AffPts k (CellIdx k V)) i = 1 := by
  ext a c
  by_cases h : a = c
  · subst h; simp [uniMat_apply_self]
  · rw [Matrix.one_apply_ne h]
    simp only [uniMat, h, if_false]
    split_ifs <;> rfl
end GlobalTheory.FlagPts
