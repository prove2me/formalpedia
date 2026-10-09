-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.exists_scaled_pade_graph
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:02:33.423715+00:00
-- url     : https://prove2.me/submissions/3a31ead9-216d-4b08-8cf9-e2be7b70df92

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
/-!
# The remaining identity fibre of the N13 full Kummer map

The target algebra already shows that the N13 full Kummer map has one
kernel fibre.  This file unfolds that fibre instead of treating it as an
opaque equality:

* triviality in the full target is equivalent to an explicit full-gauge
  witness `(β,q)`;
* divisibility by two in the oriented Picard quotient is equivalent to an
  explicit square root of the raw oriented fractional ideal.

The remaining geometric seam is closed here by a dimension-theoretic Padé
numerator, homogeneous resultants, quadratic-algebra rigidity, and Cantor
ideal identities.  No representative enumeration or finite certificate is
used.
-/
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
/-! ## Unfolding the full-gauge fibre -/
/-! ## The canonical polynomial square-root witness -/
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
/-- A rational graph scalar rescales the Padé cubic into the actual graph
polynomial used by Cantor's identity.  The same construction works for
both the linear and quadratic quotient branches. -/
theorem exists_scaled_pade_graph
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X])
    (c b : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hb : b ≠ 0)
    (hbSq : b ^ 2 = c / (q : ℚ))
    (hgraph :
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v)
    (hc : c ≠ 0) :
    ∃ L₀ : ℚ[X], ∃ κ : ℚˣ,
      N13Mumford.f ℚ - L₀ ^ 2 =
          a ^ 2 *
            (Polynomial.C (κ : ℚ) * D.toSemi.u) ∧
      D.toSemi.u ∣ L₀ - D.toSemi.v := by
  let L₀ : ℚ[X] :=
    Polynomial.C (b⁻¹) * l
  let κ : ℚˣ :=
    Units.mk0 (-c⁻¹)
      (neg_ne_zero.mpr (inv_ne_zero hc))
  have hscale :
      (b⁻¹) ^ 2 = (q : ℚ) / c := by
    rw [inv_pow, hbSq]
    field_simp [hc, Units.ne_zero q]
  have hcScale :
      c * (b⁻¹) ^ 2 = (q : ℚ) := by
    rw [hscale]
    field_simp [hc]
  have hCb :
      Polynomial.C (b⁻¹) * Polynomial.C b = 1 := by
    rw [← Polynomial.C_mul]
    simp [hb]
  have hgraphScaled :
      D.toSemi.u ∣ L₀ - D.toSemi.v := by
    obtain ⟨t, ht⟩ := hgraph
    refine
      ⟨Polynomial.C (b⁻¹) * t, ?_⟩
    calc
      L₀ - D.toSemi.v =
          Polynomial.C (b⁻¹) *
            (l - Polynomial.C b * D.toSemi.v) := by
              dsimp only [L₀]
              rw [mul_sub]
              rw [← mul_assoc, hCb, one_mul]
      _ =
          Polynomial.C (b⁻¹) *
            (D.toSemi.u * t) := by
              rw [ht]
      _ =
          D.toSemi.u *
            (Polynomial.C (b⁻¹) * t) := by
              ring
  have hscaledSquare :
      Polynomial.C c * L₀ ^ 2 =
        Polynomial.C (q : ℚ) * l ^ 2 := by
    calc
      Polynomial.C c * L₀ ^ 2 =
          (Polynomial.C c *
              Polynomial.C ((b⁻¹) ^ 2)) *
            l ^ 2 := by
              dsimp only [L₀]
              rw [mul_pow, ← Polynomial.C_pow]
              ring
      _ =
          Polynomial.C (q : ℚ) * l ^ 2 := by
            rw [← Polynomial.C_mul, hcScale]
  have hscaledFactor :
      Polynomial.C c *
          (a ^ 2 *
            (Polynomial.C (κ : ℚ) *
              D.toSemi.u)) =
        -(a ^ 2 * D.toSemi.u) := by
    have hcInv :
        c * (-c⁻¹) = (-1 : ℚ) := by
      field_simp [hc]
    calc
      Polynomial.C c *
            (a ^ 2 *
              (Polynomial.C (κ : ℚ) *
                D.toSemi.u)) =
          (Polynomial.C c *
              Polynomial.C (-c⁻¹)) *
            (a ^ 2 * D.toSemi.u) := by
              change
                Polynomial.C c *
                    (a ^ 2 *
                      (Polynomial.C (-c⁻¹) *
                        D.toSemi.u)) =
                  (Polynomial.C c *
                      Polynomial.C (-c⁻¹)) *
                    (a ^ 2 * D.toSemi.u)
              ring
      _ =
          Polynomial.C (-1 : ℚ) *
            (a ^ 2 * D.toSemi.u) := by
              rw [← Polynomial.C_mul, hcInv]
      _ = -(a ^ 2 * D.toSemi.u) := by
        simp
  refine ⟨L₀, κ, ?_, hgraphScaled⟩
  apply mul_left_cancel₀
    (Polynomial.C_ne_zero.mpr hc)
  rw [mul_sub, hscaledSquare, hscaledFactor]
  linear_combination -hrelation
/-! ## Closing the finite ideal square -/
namespace FinitePadeGraphRootData
end FinitePadeGraphRootData
namespace FiniteIdealGraphRootData
end FiniteIdealGraphRootData
/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
/-! ## Squares in the oriented fractional-ideal quotient -/
/-! ## Absorbing the remaining infinity coordinate -/
/-! ## The structural full-gauge bridge -/
/-! ## Compatibility with the earlier abstract bridge interface -/
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end

end

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.exists_scaled_pade_graph := @MazurProof.N13MumfordFullKummerIdentityFiber.exists_scaled_pade_graph
