-- Prove2me | solution 1 for GlobalTheory.LatticeIneq.exists_int_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:29.775591+00:00
-- url     : https://prove2.me/submissions/034ee442-1bd3-4e39-bf16-74741a653af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsReducedCombination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.LatticeIneq
variable {X : Type} [AddCommGroup X]
namespace GlobalTheory.LatticeIneq
theorem _root_.solution {I : Type} [Fintype I] (N : ℕ) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), z + N • μ = ∑ x, k x • w x := by
  classical
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩ | ⟨μ, rfl⟩
    · obtain ⟨μ, hμ⟩ := hw i
      refine ⟨Pi.single i 1, μ, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [hμ]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    · exact ⟨0, -μ, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, μ, h⟩ := ha
    obtain ⟨k', μ', h'⟩ := hb
    refine ⟨k + k', μ + μ', ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← h, ← h', smul_add]
    abel
  | neg a _ ha =>
    obtain ⟨k, μ, h⟩ := ha
    refine ⟨-k, -μ, ?_⟩
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← h, smul_neg]
    abel
end GlobalTheory.LatticeIneq
