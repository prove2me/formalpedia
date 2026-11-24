-- Prove2me | solution 1 for GlobalTheory.ClassParam.sig_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:30.379005+00:00
-- url     : https://prove2.me/submissions/4c6d4a35-32cd-4baf-a5c5-3a403313e96b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_fixed_tensor

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
theorem _root_.solution (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) (z : E ⊗[F] k)
    (hz : sigR (c : E →ₐ[F] E) k z = z) : ∃ d : k, (1 : E) ⊗ₜ[F] d = z := by
  obtain ⟨w, rfl⟩ := (fixed_tensor k (Algebra.linearMap F E) c.toLinearMap
    (fun v => ⟨hF v, by rintro ⟨w, rfl⟩; simp⟩) z).1 hz
  refine ⟨TensorProduct.lid F k w, ?_⟩
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add y y' h h' => rw [map_add, map_add, tmul_add, h, h']
  | tmul a t => simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
end GlobalTheory.ClassParam
