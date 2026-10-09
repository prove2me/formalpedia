-- Prove2me | solution 1 for MazurProof.N13Infinity.coordinateToAlgebraic_injective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:52:13.728707+00:00
-- url     : https://prove2.me/submissions/4ab68ce0-f66a-4a66-bf0e-4517b1eb1261

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-! ## The formal positive square root -/
/-! ## An algebraic model of the function field -/
theorem curvePolyRat_monic : (curvePolyRat K).Monic := by
  exact (SexticMumford.curvePoly_monic (N13Mumford.model K)).map _
theorem coordinateToAlgebraic_injective :
    Function.Injective (coordinateToAlgebraic K) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    let r : K[X][X] := g %ₘ SexticMumford.curvePoly (N13Mumford.model K)
    have hrz : AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) r =
        AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g := by
      simpa only [r, AdjoinRoot.modByMonicHom_mk] using
        (AdjoinRoot.mk_leftInverse (SexticMumford.curvePoly_monic (N13Mumford.model K))
          (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g))
    have hmap : AdjoinRoot.mk (curvePolyRat K)
        (r.map (algebraMap K[X] (RatFunc K))) = 0 := by
      rw [← coordinateToAlgebraic_mk, hrz, hz]
    have hrdeg : r.degree < (SexticMumford.curvePoly (N13Mumford.model K)).degree := by
      exact Polynomial.degree_modByMonic_lt g
        (SexticMumford.curvePoly_monic (N13Mumford.model K))
    have hbase : Function.Injective
        (algebraMap K[X] (RatFunc K)) :=
      IsFractionRing.injective K[X] (RatFunc K)
    have hmapdeg :
        (r.map (algebraMap K[X] (RatFunc K))).degree <
          (curvePolyRat K).degree := by
      rw [curvePolyRat, Polynomial.degree_map_eq_of_injective hbase,
        Polynomial.degree_map_eq_of_injective hbase]
      exact hrdeg
    have hrmapzero : r.map (algebraMap K[X] (RatFunc K)) = 0 := by
      by_contra hr0
      exact (curvePolyRat_monic K).not_dvd_of_degree_lt hr0 hmapdeg
        (AdjoinRoot.mk_eq_zero.mp hmap)
    have hrzero : r = 0 :=
      (Polynomial.map_eq_zero_iff hbase).mp hrmapzero
    rw [← hrz, hrzero, map_zero]
    exact Submodule.zero_mem _
  · exact bot_le
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
end
end MazurProof.N13Infinity
end

end

theorem solution : type_of% @MazurProof.N13Infinity.coordinateToAlgebraic_injective := @MazurProof.N13Infinity.coordinateToAlgebraic_injective
