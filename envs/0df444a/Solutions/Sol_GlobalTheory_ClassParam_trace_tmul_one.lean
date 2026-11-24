-- Prove2me | solution 1 for GlobalTheory.ClassParam.trace_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:46.221962+00:00
-- url     : https://prove2.me/submissions/5e87c3f3-135d-4dcc-8f30-4f6dbb77c2cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_trace_transfer
import Theorems.Thm_GlobalTheory_ClassParam_exists_basis_tensor

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
    (l : AdjoinRoot P) : Algebra.trace (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) (l ⊗ₜ 1)
      = Algebra.trace E (AdjoinRoot P) l ⊗ₜ 1 := by
  classical
  obtain ⟨b', hb'⟩ := exists_basis_tensor (F := F) k b
  exact trace_transfer (inclE (F := F) k) (inclE (F := F) k) (fun _ => rfl) b b'
    (fun i => (hb' i).symm) l
end GlobalTheory.ClassParam
