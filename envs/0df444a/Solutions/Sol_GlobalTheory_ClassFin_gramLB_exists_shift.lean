-- Prove2me | solution 1 for GlobalTheory.ClassFin.gramLB_exists_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:12.42426+00:00
-- url     : https://prove2.me/submissions/cf2cdcdd-0bfb-430c-a4b6-bf2e9956d2b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ (A - k • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hA.1.eigenvalues
      exact ⟨_, hA.eigenvalues_pos i0, hi0⟩
  refine ⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩
  obtain ⟨U, -, hEq⟩ := gramLB_shift hA.1 (-(min 1 m))
  rw [sub_eq_add_neg, ← neg_smul, hEq]
  exact (posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U
end GlobalTheory.ClassFin
