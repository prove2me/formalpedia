-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.blk_form_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:19.499808+00:00
-- url     : https://prove2.me/submissions/decda1ae-8557-4d3f-8cb4-b43cab8bce21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_blk_form

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
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c = GlobalTheory.WeilM.dbl J ↔ phi c J X = 0 := by
  rw [blk_form]
  constructor
  · intro h
    rw [GlobalTheory.WeilM.dbl, fromBlocks_add, fromBlocks_inj] at h
    simpa using h.1
  · intro h
    rw [h]
    simp
end GlobalTheory.EisBL.NilAlg
