-- Prove2me | solution 1 for GlobalTheory.DiagBlock.diagMon_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:27.407716+00:00
-- url     : https://prove2.me/submissions/a30fc3f4-5238-47fa-98fb-2154a2ec7d10

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution (n0 n L y : ℕ) (ρ c : Fin n) :
    diagMon n0 n L y (Sum.inl (ρ, c)) = if n0 ≤ ρ.val ∧ c = ρ then L * y else 0 := by
  rw [diagMon, Finsupp.finsetSum_apply]
  by_cases hρ : n0 ≤ ρ.val
  · rw [Finset.sum_eq_single ρ]
    · by_cases hc : c = ρ
      · subst hc; simp [hρ]
      · simp [hc]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ρ, hρ⟩) h
  · rw [if_neg (fun h => hρ h.1)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ≠ ρ := fun h => hρ (h ▸ (Finset.mem_filter.1 hb).2)
    simp [hb']
end GlobalTheory.DiagBlock
