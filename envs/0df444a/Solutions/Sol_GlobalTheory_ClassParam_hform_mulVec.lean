-- Prove2me | solution 1 for GlobalTheory.ClassParam.hform_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:16.770828+00:00
-- url     : https://prove2.me/submissions/e026e07b-c98a-46d7-899c-a0154e8f8584

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
variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)
namespace GlobalTheory.ClassParam
theorem _root_.solution (J g : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ (cT σ g * J * g) x y := by
  have h2 : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [hform_eq, hform_eq, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cT,
    Matrix.dotProduct_mulVec _ (g.map σ)ᵀ, Matrix.vecMul_transpose]
end GlobalTheory.ClassParam
