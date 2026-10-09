-- Prove2me | solution 1 for MazurProof.N13Infinity.ratToLaurent_comp_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:35.129115+00:00
-- url     : https://prove2.me/submissions/2269b522-ec3d-457c-8953-cdb1f037faec

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

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
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
omit [CharZero K] in
omit [CharZero K] in
@[simp] theorem ratInvAlgHom_X :
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
      (RatFunc.X : RatFunc K)⁻¹ := by
  calc
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
        ratInvAlgHom K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = invPolyAlgHom K Polynomial.X := by
      change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
          (algebraMap K[X] (RatFunc K) Polynomial.X) = _
      exact RatFunc.liftRingHom_algebraMap _ _ _
    _ = (RatFunc.X : RatFunc K)⁻¹ := by simp [invPolyAlgHom]
omit [CharZero K] in
@[simp] theorem standardRatToLaurent_X :
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
      HahnSeries.single 1 1 := by
  calc
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
        standardRatToLaurent K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = algebraMap K[X] (LaurentSeries K) Polynomial.X := by
      exact IsFractionRing.lift_algebraMap
        (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) _
    _ = HahnSeries.single 1 1 := by simp
omit [CharZero K] in
@[simp] theorem standardRatToLaurent_algebraMap (p : K[X]) :
    standardRatToLaurent K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (LaurentSeries K) p := by
  exact IsFractionRing.lift_algebraMap
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) p
omit [CharZero K] in
omit [CharZero K] in
@[simp] theorem ratInvAlgHom_algebraMap (p : K[X]) :
    ratInvAlgHom K (algebraMap K[X] (RatFunc K) p) =
      invPolyAlgHom K p := by
  change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
      (algebraMap K[X] (RatFunc K) p) = _
  exact RatFunc.liftRingHom_algebraMap _ _ _
omit [CharZero K] in
@[simp] theorem ratToLaurent_X :
    ratToLaurent K (RatFunc.X : RatFunc K) = (parameter K)⁻¹ := by
  simp [ratToLaurent, parameter]
omit [CharZero K] in
@[simp] theorem ratToLaurent_C (a : K) :
    ratToLaurent K (RatFunc.C a) =
      algebraMap K (LaurentSeries K) a := by
  rw [← RatFunc.algebraMap_C]
  change standardRatToLaurent K
      (ratInvAlgHom K (algebraMap K[X] (RatFunc K) (C a))) = _
  rw [ratInvAlgHom_algebraMap]
  simp only [invPolyAlgHom, Polynomial.aeval_C]
  change standardRatToLaurent K (RatFunc.C a) = _
  rw [← RatFunc.algebraMap_C]
  rw [standardRatToLaurent_algebraMap]
  rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C,
    HahnSeries.ofPowerSeries_C]
  rw [HahnSeries.algebraMap_apply' (Γ := ℤ)]
  simp
omit [CharZero K] in
theorem ratToLaurent_comp_algebraMap :
    (ratToLaurent K).comp (algebraMap K[X] (RatFunc K)) =
      Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp
end
end MazurProof.N13Infinity
end

end

theorem solution : type_of% @MazurProof.N13Infinity.ratToLaurent_comp_algebraMap := @MazurProof.N13Infinity.ratToLaurent_comp_algebraMap
