-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.spanFrom_update_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:14:15.200796+00:00
-- url     : https://prove2.me/submissions/8bdf7466-b505-48dd-b163-087617d9d016

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_of_lt
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
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    spanFrom k (Function.update f m v) N m = spanFrom k f N (m + 1) ⊔ k ∙ v := by
  rw [← spanFrom_update_of_lt (k := k) f N m (m + 1) v (Nat.lt_succ_self m)]
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = insert m {a | m + 1 ≤ a ∧ a < N} := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_insert_iff]; omega
  rw [this, Set.image_insert_eq, Submodule.span_insert, Function.update_self, sup_comm]
end GlobalTheory.FlagPts.SphericalEisensteinCover
