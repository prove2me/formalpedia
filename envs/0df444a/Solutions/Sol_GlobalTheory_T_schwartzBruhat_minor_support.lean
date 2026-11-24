-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_minor_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:22.002999+00:00
-- url     : https://prove2.me/submissions/b443bfea-552f-4bd5-a783-6f97a2d7a10d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatMinorSupport
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatMinorSupportStatement
import Theorems.Thm_GlobalTheory_RankChart_exists_mem_nsp_eq_of_rank_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  first | exact @GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | exact GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | (intros; apply GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le <;> assumption)
end _root_.GlobalTheory.T
