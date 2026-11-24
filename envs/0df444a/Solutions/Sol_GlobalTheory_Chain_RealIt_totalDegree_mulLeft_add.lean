-- Prove2me | solution 1 for GlobalTheory.Chain.RealIt.totalDegree_mulLeft_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:32.398859+00:00
-- url     : https://prove2.me/submissions/54dd13a8-8f41-446b-b94a-79e0b314f49a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotLocallyFiniteQuadraticMulAddDegreeNonraising

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open MvPolynomial
namespace GlobalTheory.Chain.RealIt
theorem _root_.solution {σ : Type} (Q : MvPolynomial σ ℂ)
    (L : Module.End ℂ (MvPolynomial σ ℂ)) (hQ : Q ≠ 0) (hh : Q.IsHomogeneous 2)
    (hL : ∀ P, (L P).totalDegree ≤ P.totalDegree) (φ : MvPolynomial σ ℂ) (hφ : φ ≠ 0) :
    ((LinearMap.mulLeft ℂ Q + L) φ).totalDegree = φ.totalDegree + 2 := by
  have h1 : (Q * φ).totalDegree = φ.totalDegree + 2 := by
    rw [totalDegree_mul_of_isDomain hQ hφ, hh.totalDegree hQ, add_comm]
  have h2 : (L φ).totalDegree < (Q * φ).totalDegree := by
    have := hL φ
    omega
  rw [LinearMap.add_apply, LinearMap.mulLeft_apply, totalDegree_add_eq_left_of_totalDegree_lt h2, h1]
end GlobalTheory.Chain.RealIt
