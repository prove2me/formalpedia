-- Prove2me | solution 1 for GlobalTheory.ClassParam.sigR_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:29.492299+00:00
-- url     : https://prove2.me/submissions/ef529d17-b1ca-4ef3-b989-b32701cb77d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

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
theorem _root_.solution {L : Type} [CommRing L] [Algebra F L] (s : L →ₐ[F] L) (hs : ∀ l, s (s l) = l)
    (y : L ⊗[F] k) : sigR s k (sigR s k y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' h h' => rw [map_add, map_add, h, h']
  | tmul l t => simp [sigR, hs]
end GlobalTheory.ClassParam
