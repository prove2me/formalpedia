-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.map_mul_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:13.986499+00:00
-- url     : https://prove2.me/submissions/f0eaf738-2ff1-42d6-95e0-c99dafb0a2e1

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
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}
namespace GlobalTheory.ClassParam
namespace HidaSetting
theorem _root_.solution (S : HidaSetting σ τ α b) (ψ : B →ₗ[A] B)
    (h : ∀ y, ψ (α * y) = α * ψ y) (y : B) : ψ y = ψ 1 * y := by
  have hp : ∀ n : ℕ, ψ (α ^ n) = ψ 1 * α ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', h, ih]; ring
  have : ψ = LinearMap.mulLeft A (ψ 1) := b.ext fun i => by rw [S.pow, hp]; rfl
  exact LinearMap.congr_fun this y
end HidaSetting
end GlobalTheory.ClassParam
