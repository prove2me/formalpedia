-- Prove2me | solution 1 for GlobalTheory.FinsetSumSmulCoe.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:14.276485+00:00
-- url     : https://prove2.me/submissions/f7022e88-09d0-4478-b05c-8fe2ad20c8b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoeFnFinsetSumSmul
import Theorems.Thm_GlobalTheory_FinsetSumSmulCoe_coeFn_finset_sum_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.FinsetSumSmulCoe
namespace GlobalTheory.FinsetSumSmulCoe
theorem _root_.solution : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by
  intro α _ μ ι _ c u
  exact coeFn_finset_sum_smul c u Finset.univ
end GlobalTheory.FinsetSumSmulCoe
