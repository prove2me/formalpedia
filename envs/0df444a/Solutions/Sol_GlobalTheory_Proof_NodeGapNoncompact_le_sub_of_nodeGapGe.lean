-- Prove2me | solution 1 for GlobalTheory.Proof.NodeGapNoncompact.le_sub_of_nodeGapGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:57:03.949355+00:00
-- url     : https://prove2.me/submissions/54ca91a6-7640-4647-9a88-cb264d0fa8e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_sign_eq
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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.NodeGapNoncompact
open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.Proof.NodeGapNoncompact
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) (hg : NodeGapGe r b h)
    (s t : Fin (2 * r + k + 1)) (hst : s < t) (hne : sign r k hk s ≠ sign r k hk t) :
    h ≤ param r k hk v b s - param r k hk v b t := by
  have hlt : s.val < t.val := hst
  have ht : k ≤ t.val := by
    by_contra hc
    apply hne
    rw [← sign_eq]
    unfold eps48
    have h1 : s.val < k - 1 := by omega
    rw [if_pos h1]
    by_cases h2 : t.val < k - 1
    · rw [if_pos h2]
    · rw [if_neg h2]
      have : t.val - (k - 1) = 0 := by omega
      simp [this]
  have htl := t.isLt
  have hi : t.val - k + 1 < 2 * r + 2 := by omega
  have h1 := hg (t.val - k) hi
  have e1 : t = nodeIdx r k hk ⟨t.val - k + 1, hi⟩ := by
    apply Fin.ext
    simp only [nodeIdx]
    omega
  have e2 : s ≤ nodeIdx r k hk ⟨t.val - k, by omega⟩ := by
    simp only [nodeIdx, Fin.le_def]
    omega
  have h2 := hd.antitone e2
  have h3 : param r k hk v b t = -b ⟨t.val - k + 1, hi⟩ := by
    conv_lhs => rw [e1, param_node]
  rw [param_node] at h2
  linarith
end GlobalTheory.Proof.NodeGapNoncompact
