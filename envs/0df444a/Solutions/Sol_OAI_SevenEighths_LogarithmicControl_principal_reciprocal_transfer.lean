-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.principal_reciprocal_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:21.322206+00:00
-- url     : https://prove2.me/submissions/33e46ba1-0b0b-4aaa-a60f-5b50bc9d1b7f

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_principal_regularizer_norm_le_one

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {s Z L : ℂ} (hs : 0 ≤ s.re)
    (hL : L = ((s - 1) / (s + 1)) * Z) (h0 : L ≠ 0) : ‖Z⁻¹‖ ≤ ‖L⁻¹‖ := by
  have hf0 : (s - 1) / (s + 1) ≠ 0 := by
    intro hf
    apply h0
    rw [hL, hf, zero_mul]
  have heq : Z⁻¹ = ((s - 1) / (s + 1)) * L⁻¹ := by
    rw [hL, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (principal_regularizer_norm_le_one hs)
    (norm_nonneg _)).trans_eq (one_mul _)
end OAI.SevenEighths.LogarithmicControl
