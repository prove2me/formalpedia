-- Prove2me | solution 1 for GlobalTheory.MinorFrame.rowSub_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:48.999574+00:00
-- url     : https://prove2.me/submissions/72733168-ff21-4fb4-a8d3-25d462861cf3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Theorems.Thm_GlobalTheory_MinorFrame_colSub_rowSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by
  intro g
  rw [colSub_rowSub, hP g, map_smul]
end GlobalTheory.MinorFrame
