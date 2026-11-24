-- Prove2me | solution 1 for GlobalTheory.ClassFin.unipotent_size_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:44.995826+00:00
-- url     : https://prove2.me/submissions/7f25904a-f50a-4f6c-8798-8416d22907c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReduction
import Theorems.Thm_GlobalTheory_ClassFin_unipotent_size_reduction_column

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
theorem _root_.solution :
    ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) →
      ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧
        ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  intro N n h1 h0
  choose z hz1 hz0 hz using fun j => unipotent_size_reduction_column n h1 h0 j N
  refine ⟨Matrix.of fun i j => z j i, fun i => hz1 i, fun i j h => hz0 j i h, ?_⟩
  intro i j hij
  rw [Matrix.mul_apply]
  exact hz j i hij (by have := j.2; omega)
end GlobalTheory.ClassFin
