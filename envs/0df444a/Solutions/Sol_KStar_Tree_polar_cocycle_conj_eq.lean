-- Prove2me | solution 1 for KStar.Tree.polar_cocycle_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:43.129408+00:00
-- url     : https://prove2.me/submissions/f2326e37-72e2-4d1a-8474-8e1cbd1132a9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TwistTrace
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_PolarTraceMulVecMulVecEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
open Matrix
namespace KStar.Tree
theorem _root_.solution {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ}
    (T : Γ →* Matrix (Fin r) (Fin r) A) (L : Subgroup Γ) (hL : L.Normal)
    (hT : ∀ h ∈ L, T h = 1) (x : Γ → Fin r → A)
    (hx : ∀ g h, x (g * h) = x g + (T g).mulVec (x h)) (g h : Γ) (hh : h ∈ L) :
    x (g * h * g⁻¹) = (T g).mulVec (x h) := by
  have h1 : x 1 = 0 := by
    have e := hx 1 1
    rw [mul_one, map_one, Matrix.one_mulVec] at e
    simpa using e
  have hinv : x g + (T g).mulVec (x g⁻¹) = 0 := by
    rw [← hx, mul_inv_cancel, h1]
  rw [mul_assoc, hx, hx h, hT h hh, Matrix.one_mulVec, Matrix.mulVec_add, add_left_comm, hinv,
    add_zero]
end KStar.Tree
