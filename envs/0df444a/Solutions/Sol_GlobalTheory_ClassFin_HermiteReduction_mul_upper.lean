-- Prove2me | solution 1 for GlobalTheory.ClassFin.HermiteReduction.mul_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:11.607397+00:00
-- url     : https://prove2.me/submissions/a0c73a93-369c-4363-9b06-78e64443db10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IwasawaDecompositionRealMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DetLeadingMinorGramIwasawaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramMinorSwapAdjacentColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis

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
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HermiteReduction
namespace GlobalTheory.ClassFin.HermiteReduction
theorem _root_.solution {N : ℕ} (n m : Matrix (Fin N) (Fin N) ℝ) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hm1 : ∀ i, m i i = 1) (hm0 : ∀ i j, j < i → m i j = 0) :
    (∀ i, (n * m) i i = 1) ∧ ∀ i j, j < i → (n * m) i j = 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hn1, hm1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hn0 i l h, zero_mul]
      · rw [hm0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hn0 i l h, zero_mul]
    · rw [hm0 l j (lt_of_lt_of_le hij h), mul_zero]
end GlobalTheory.ClassFin.HermiteReduction
