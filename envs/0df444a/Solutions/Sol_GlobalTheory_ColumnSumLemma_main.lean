-- Prove2me | solution 1 for GlobalTheory.ColumnSumLemma.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:25.443831+00:00
-- url     : https://prove2.me/submissions/1adcaf20-2bb4-4322-b688-4abe7ccd6037

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColSum
import Theorems.Thm_GlobalTheory_ColumnSumLemma_colSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ColumnSumLemma
open Matrix
namespace GlobalTheory.ColumnSumLemma
theorem _root_.solution : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by
  intro A _ n r C I y
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact Finsupp.notMem_support_iff.mp (fun h => hk (hl h))
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩
    · by_contra h
      exact (Finsupp.mem_support_iff.mp hk) (ha k h)
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; simp
end GlobalTheory.ColumnSumLemma
