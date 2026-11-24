-- Prove2me | solution 1 for GlobalTheory.ClassParam.charpoly_of_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:14.897533+00:00
-- url     : https://prove2.me/submissions/4fd400a0-47fb-44d3-952d-f843642a53ac

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
theorem _root_.solution {g : Matrix (Fin r) (Fin r) A} {φ : B ≃ₗ[A] (Fin r → A)}
    (b : Module.Basis (Fin r) A B)
    (hg : Intw α g φ) : g.charpoly = (Algebra.leftMulMatrix b α).charpoly := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  have h1 : Matrix.toLin' g = φ.conj (Algebra.lmul A B α) := LinearMap.ext fun u => by
    simpa [LinearEquiv.conj_apply] using hg u
  rw [← Matrix.charpoly_toLin', h1, LinearEquiv.charpoly_conj, Algebra.leftMulMatrix_apply,
    LinearMap.charpoly_toMatrix]
end GlobalTheory.ClassParam
