-- Prove2me | solution 1 for GlobalTheory.CondRescale.norm_le_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:36.690694+00:00
-- url     : https://prove2.me/submissions/f263b40f-e499-45fd-bf8d-8465ec4c711c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalCharacterConductorExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open scoped Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CondRescale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CondRescale
theorem _root_.solution (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : ‖z‖ ≤ 1 := by
  by_contra hz
  push_neg at hz
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hz
  have h1 := h n
  have h2 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖z ^ n‖ = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_pow, norm_one] at h2
  linarith
end GlobalTheory.CondRescale
