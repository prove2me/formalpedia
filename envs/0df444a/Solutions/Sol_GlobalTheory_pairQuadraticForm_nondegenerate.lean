-- Prove2me | solution 1 for GlobalTheory.pairQuadraticForm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:21.385674+00:00
-- url     : https://prove2.me/submissions/63eaac74-f865-4e94-9888-74db0b7f9d2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    (x : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)
    (hx : ∀ y, QuadraticMap.polar (pairQuadraticForm hd hs he) x y = 0) : x = 0 := by
  obtain ⟨ν, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨u, v, huv⟩ := hc
  have hu := isUnit_det_map_ratCast hd
  have hint : ∀ i, ∃ k : ℤ, (k : ℚ) = ((b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
      fun i => (ν i : ℚ)) i := by
    intro i
    have h : QuadraticMap.polar
        (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)) ν (Pi.single i 1) = 0 :=
      hx (Submodule.Quotient.mk (Pi.single i 1))
    rw [polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), AddCircle.coe_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    simpa [dotProduct, Pi.single_apply] using hk
  choose w hw using hint
  have huv' : u.map ((↑) : ℤ → ℚ) * b.map (↑) + v.map (↑) * d.map (↑) = 1 := by
    have := congrArg (Int.castRingHom ℚ).mapMatrix huv
    rwa [map_add, map_mul, map_mul, map_one] at this
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨u *ᵥ w + v *ᵥ ν, ?_⟩
  have h1 : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) =
      (d.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun i => (ν i : ℚ) := by
    have : (fun i => ((u *ᵥ w + v *ᵥ ν) i : ℚ)) =
        (fun i => ((u *ᵥ w) i : ℚ)) + fun i => ((v *ᵥ ν) i : ℚ) := by ext; simp
    rw [this, intCast_mulVec, intCast_mulVec, funext hw, mulVec_mulVec, ← add_mulVec]
    congr 1
    conv_rhs => rw [← Matrix.one_mul (d.map ((↑) : ℤ → ℚ))⁻¹, ← huv', Matrix.add_mul,
      Matrix.mul_assoc _ (d.map _), mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.mul_assoc]
  have h2 := intCast_mulVec d (u *ᵥ w + v *ᵥ ν)
  rw [h1, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec] at h2
  ext i
  exact_mod_cast congrFun h2 i
end GlobalTheory
