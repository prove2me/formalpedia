-- Prove2me | solution 1 for GlobalTheory.RankStrata.gdet_glRenum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:37.00186+00:00
-- url     : https://prove2.me/submissions/4a5a2ce2-cece-4376-8c84-7a98e425f970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Theorems.Thm_GlobalTheory_RankStrata_glRenum_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankStrata
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.RankStrata
theorem _root_.solution (e : A ≃ A') (g : GL A' k) :
    GlobalTheory.SplitFlip.gdet (glRenum e g) = GlobalTheory.SplitFlip.gdet g := by
  ext
  simp [GlobalTheory.SplitFlip.gdet, glRenum_val, Matrix.det_submatrix_equiv_self]
end GlobalTheory.RankStrata
