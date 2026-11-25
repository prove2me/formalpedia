-- Prove2me | solution 1 for GlobalTheory.MinorFrame.prodMinors_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:46.107095+00:00
-- url     : https://prove2.me/submissions/9c66c799-4827-4949-a340-ae09e9a2bb73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Theorems.Thm_GlobalTheory_MinorFrame_colSub_prodMinors

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
theorem _root_.solution {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n :=
  fun g => colSub_prodMinors _ T
end GlobalTheory.MinorFrame
