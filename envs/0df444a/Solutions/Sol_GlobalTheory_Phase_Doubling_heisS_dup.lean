-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.heisS_dup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:41:26.463737+00:00
-- url     : https://prove2.me/submissions/ab271365-bbab-4d13-aad9-37c9b9f52996

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_dup_apply
import Theorems.Thm_GlobalTheory_Phase_Doubling_rowM_sub
import Theorems.Thm_GlobalTheory_Phase_Doubling_dot_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}
namespace GlobalTheory.Phase.Doubling
theorem _root_.solution (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ)
    (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    heisS y.1 y.2 (dup φ) x = heisS (comp 0 y).1 (comp 0 y).2 φ (rowM 0 x) *
      heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x) := by
  have h : (∑ k, (2 * (x k ⬝ᵥ y.1 k) - y.1 k ⬝ᵥ y.2 k) : ℚ) =
      (∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) +
      (∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) := by
    simp only [Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib, Finset.mul_sum]
    exact add_sub_add_comm _ _ _ _
  unfold heisS
  rw [h, Rat.cast_add, mul_add, Complex.exp_add, dup_apply, rowM_sub, rowM_sub]
  show _ = (φ (rowM 0 x - rowM 0 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) : ℂ))) *
    (φ (rowM 1 x - rowM 1 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) : ℂ)))
  ring
end GlobalTheory.Phase.Doubling
