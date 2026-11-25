-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.nodeGapGe_of_noncompactGapGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:42.211362+00:00
-- url     : https://prove2.me/submissions/edcb8efd-2ee5-4c88-8e07-7694d125b3ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_node
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node

set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b)
    (hg : NoncompactGapGe r k hk (param r k hk v b) h) : NodeGapGe r b h := by
  intro i hi
  have hlt : nodeIdx r k hk ⟨i, by omega⟩ < nodeIdx r k hk ⟨i + 1, hi⟩ := by
    simp [nodeIdx, Fin.lt_def]
  have h1 := hd hlt
  have h2 := hg (nodeIdx r k hk ⟨i, by omega⟩) (nodeIdx r k hk ⟨i + 1, hi⟩) (by
    simp only [sign_node, Nat.even_add_one]
    by_cases he : Even i <;> simp [he])
  simp only [param_node] at h1 h2
  rwa [abs_of_pos (by linarith)] at h2
end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
