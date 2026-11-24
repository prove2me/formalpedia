-- Prove2me | solution 1 for GlobalTheory.RankStrata.Nsp_le_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:34.830055+00:00
-- url     : https://prove2.me/submissions/83c2f062-1ff0-45cb-8f68-48c3aac86664

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Theorems.Thm_GlobalTheory_SplitFlip_omB_mem_SB


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
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.RankStrata
theorem _root_.solution (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Nsp k A D ν ≤ SB (Matrix A D k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, Ψ', hΨ', rfl⟩
  exact Submodule.sub_mem _ (GlobalTheory.SplitFlip.omB_mem_SB ν ν g 1 hΨ') hΨ'
end GlobalTheory.RankStrata
