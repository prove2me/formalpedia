-- Prove2me | solution 1 for MazurProof.N13LaurentPolynomialOrder.order_ofPowerSeries_of_coeff_zero_ne
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:29:55.340642+00:00
-- url     : https://prove2.me/submissions/d2445a4f-698f-487c-8715-a3f026fecde8

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof
namespace N13LaurentPolynomialOrder
noncomputable section
universe u
variable (K : Type u) [Field K]
lemma order_ofPowerSeries_of_coeff_zero_ne (p : K[X]) (hp : p.coeff 0 ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ K p).order = 0 := by
  have hcoeff : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 ≠ 0 := by
    have hcoeff_eq : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = p.coeff 0 := by
      calc
        (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = PowerSeries.coeff 0 (p : K⟦X⟧) :=
          HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (p : K⟦X⟧) 0
        _ = p.coeff 0 := Polynomial.coeff_coe p 0
    rwa [hcoeff_eq]
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hcoeff
  · rw [← HahnSeries.zero_le_orderTop_iff]
    apply HahnSeries.le_orderTop_iff_forall.mpr
    intro j hj
    rw [HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n, -, rfl⟩
    have hnonneg : (0 : ℤ) ≤ (Nat.castOrderEmbedding (α := ℤ) n : ℤ) := by
      simp
    exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hnonneg)) hj
end
end N13LaurentPolynomialOrder
end MazurProof
end

end

theorem solution : type_of% @MazurProof.N13LaurentPolynomialOrder.order_ofPowerSeries_of_coeff_zero_ne := @MazurProof.N13LaurentPolynomialOrder.order_ofPowerSeries_of_coeff_zero_ne
