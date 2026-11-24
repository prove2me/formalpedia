-- Prove2me | solution 1 for GlobalTheory.LatticeIneq.exists_reduced_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:14.530096+00:00
-- url     : https://prove2.me/submissions/2ac75955-f58a-4957-9718-f8269351225d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsReducedCombination
import Theorems.Thm_GlobalTheory_LatticeIneq_exists_int_combination

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
theorem _root_.solution {I : Type} [Fintype I] (N : ℕ) (hN : 1 ≤ N) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), (∀ x, 0 ≤ k x ∧ k x ≤ N) ∧ z + N • μ = ∑ x, k x • w x := by
  obtain ⟨k, μ, h⟩ := exists_int_combination N yy w hw z hz
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨fun x => k x % N, μ - ∑ x, (k x / N) • w x,
    fun x => ⟨Int.emod_nonneg _ hN'.ne', (Int.emod_lt_of_pos _ hN').le⟩, ?_⟩
  rw [smul_sub, ← add_sub_assoc, h, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← natCast_zsmul, smul_smul, ← sub_smul]
  simp only [Int.emod_def]
end GlobalTheory.LatticeIneq
