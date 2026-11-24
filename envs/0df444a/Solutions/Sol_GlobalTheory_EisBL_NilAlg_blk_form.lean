-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.blk_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:34.954799+00:00
-- url     : https://prove2.me/submissions/274f540e-547e-4bcc-a8a7-e254d2bc2565

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_blk_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c =
      GlobalTheory.WeilM.dbl J + fromBlocks (phi c J X) (-phi c J X) (-phi c J X) (phi c J X) := by
  rw [blk_map]
  simp only [blk, phi, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add, transpose_add,
    transpose_sub, transpose_neg, transpose_one]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring
end GlobalTheory.EisBL.NilAlg
