-- Prove2me | solution 1 for GlobalTheory.ClassParam.trLk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:45:22.814802+00:00
-- url     : https://prove2.me/submissions/941911c0-b5b9-4f7d-aee5-0f5d5cf100ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_map_smul_tensor
import Theorems.Thm_GlobalTheory_ClassParam_exists_basis_tensor
import Theorems.Thm_GlobalTheory_ClassParam_trace_tmul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P))
    (y : AdjoinRoot P ⊗[F] k) : trLk k P y = Algebra.trace (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) y := by
  obtain ⟨b', hb'⟩ := exists_basis_tensor (F := F) k b
  rw [← b'.sum_repr y, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trLk, map_smul_tensor, map_smul, hb', trace_tmul_one k b]
  simp
end GlobalTheory.ClassParam
