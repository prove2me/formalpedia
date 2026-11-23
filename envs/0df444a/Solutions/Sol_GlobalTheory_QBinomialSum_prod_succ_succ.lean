-- Prove2me | solution 1 for GlobalTheory.QBinomialSum.prod_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:20.897921+00:00
-- url     : https://prove2.me/submissions/a89a74d2-1a19-43bc-9be1-2eaf46b421fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.QBinomialSum
namespace GlobalTheory.QBinomialSum
theorem _root_.solution (x : ℂ) (n a : ℕ) :
    ∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)
      = (x ^ (n + 1) - 1) * x ^ a * ∏ i ∈ Finset.range a, (x ^ n - x ^ i) := by
  rw [Finset.prod_range_succ']
  have : ∀ i, x ^ (n + 1) - x ^ (i + 1) = x * (x ^ n - x ^ i) := fun i => by ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring
end GlobalTheory.QBinomialSum
