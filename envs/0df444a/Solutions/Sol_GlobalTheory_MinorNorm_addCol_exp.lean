-- Prove2me | solution 1 for GlobalTheory.MinorNorm.addCol_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:16.964781+00:00
-- url     : https://prove2.me/submissions/c73f0fc0-2ae7-46c7-9d3e-3e34737de528

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CornerMinors_nextPart_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
namespace GlobalTheory.MinorNorm
theorem _root_.solution {a : Fin l → ℕ} (ha : Antitone a) (K i : Fin l) :
    addCol a K i - nextPart (addCol a K) i = (a i - nextPart a i) + if i = K then 1 else 0 := by
  have h := nextPart_le ha i
  have hK := K.2
  unfold nextPart addCol at *
  simp only [Fin.le_def, Fin.ext_iff]
  split_ifs at h ⊢ <;> omega
end GlobalTheory.MinorNorm
