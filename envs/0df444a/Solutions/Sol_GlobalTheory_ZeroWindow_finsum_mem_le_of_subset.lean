-- Prove2me | solution 1 for GlobalTheory.ZeroWindow.finsum_mem_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:59.046594+00:00
-- url     : https://prove2.me/submissions/95892ebf-d513-437a-8fec-dc5f23be0784

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroWindow
namespace GlobalTheory.ZeroWindow
theorem _root_.solution {S T : Set ℂ} (hT : T.Finite) (h : S ⊆ T) (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ᶠ x ∈ S, f x ≤ ∑ᶠ x ∈ T, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f hT, finsum_mem_eq_finite_toFinset_sum f (hT.subset h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hf i
  intro x hx
  simp only [Set.Finite.mem_toFinset] at hx ⊢
  exact h hx
end GlobalTheory.ZeroWindow
