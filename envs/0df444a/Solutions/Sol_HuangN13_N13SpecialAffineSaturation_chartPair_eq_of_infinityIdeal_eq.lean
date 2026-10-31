-- Prove2me | solution 1 for HuangN13.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:56:01.940047+00:00
-- url     : https://prove2.me/submissions/7722245e-3312-4b44-8290-31c4d96f2473

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_infinityCoeffMap_hPoly

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
theorem infinityCurve_relation :
    N13SpecialInfinityChart.curvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13SpecialInfinityChart.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hPoly,
    infinityCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- Restriction of the infinity coordinate ring to the special affine
principal open. -/
def infinityToAffineOverlap :
    CoordinateRing →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13SpecialInfinityChart.curvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13SpecialInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13SpecialInfinityChart.tClass, infinityCoeffMap]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13SpecialInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13SpecialInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13SpecialInfinityChart.tClass
    infinity_tClass_mapsToUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : CoordinateRing) :
    infinityOverlapToAffineOverlap
        (algebraMap CoordinateRing InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13SpecialInfinityChart.tClass
      infinity_tClass_mapsToUnit z
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_tOverlap :
    infinityOverlapToAffineOverlap tOverlap = tAffineOverlap := by
  rw [tOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_tClass]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The reverse overlap map sends `t⁻¹` back to `x`. -/
@[simp] theorem infinityOverlapToAffineOverlap_xOverlap :
    infinityOverlapToAffineOverlap xOverlap = xAffineOverlap := by
  have hinv :
      tAffineOverlap *
          infinityOverlapToAffineOverlap xOverlap = 1 := by
    calc
      tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap =
          infinityOverlapToAffineOverlap tOverlap *
            infinityOverlapToAffineOverlap xOverlap := by
              rw [infinityOverlapToAffineOverlap_tOverlap]
      _ =
          infinityOverlapToAffineOverlap
            (tOverlap * xOverlap) := by
              rw [map_mul]
      _ = 1 := by rw [tOverlap_mul_xOverlap, map_one]
  calc
    infinityOverlapToAffineOverlap xOverlap =
        1 * infinityOverlapToAffineOverlap xOverlap := by simp
    _ =
        (xAffineOverlap * tAffineOverlap) *
          infinityOverlapToAffineOverlap xOverlap := by
            rw [xAffineOverlap_mul_tAffineOverlap]
    _ =
        xAffineOverlap *
          (tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap) := by
              rw [mul_assoc]
    _ = xAffineOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The forward overlap map sends `x⁻¹` back to `t`. -/
@[simp] theorem affineOverlapToInfinityOverlap_tAffineOverlap :
    affineOverlapToInfinityOverlap tAffineOverlap = tOverlap := by
  have hinv :
      xOverlap *
          affineOverlapToInfinityOverlap tAffineOverlap = 1 := by
    calc
      xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap =
          affineOverlapToInfinityOverlap xAffineOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap := by
              rw [affineOverlapToInfinityOverlap_xAffineOverlap]
      _ =
          affineOverlapToInfinityOverlap
            (xAffineOverlap * tAffineOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [xAffineOverlap_mul_tAffineOverlap, map_one]
  calc
    affineOverlapToInfinityOverlap tAffineOverlap =
        1 * affineOverlapToInfinityOverlap tAffineOverlap := by simp
    _ =
        (tOverlap * xOverlap) *
          affineOverlapToInfinityOverlap tAffineOverlap := by
            rw [tOverlap_mul_xOverlap]
    _ =
        tOverlap *
          (xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap) := by
              rw [mul_assoc]
    _ = tOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_vOverlap :
    infinityOverlapToAffineOverlap vOverlap =
      tAffineOverlap ^ 3 * yAffineOverlap := by
  rw [vOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_vClass]
  rfl
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] private theorem xCube_cancel
    (z : AffineOverlap) :
    xAffineOverlap ^ 3 * (tAffineOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    xAffineOverlap_mul_tAffineOverlap, one_pow, one_mul]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] private theorem tCube_cancel
    (z : InfinityOverlap) :
    tOverlap ^ 3 * (xOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    tOverlap_mul_xOverlap, one_pow, one_mul]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The reverse special overlap map is a left inverse of the forward map. -/
theorem infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap :
    infinityOverlapToAffineOverlap.comp
        affineOverlapToInfinityOverlap =
      RingHom.id AffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers xClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        infinityOverlapToAffineOverlap
            (affineOverlapToInfinityOverlap xAffineOverlap) =
          xAffineOverlap
      simp
  · change
      infinityOverlapToAffineOverlap
          (affineOverlapToInfinityOverlap yAffineOverlap) =
        yAffineOverlap
    simp
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The forward special overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13SpecialInfinityChart.tClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        affineOverlapToInfinityOverlap
            (infinityOverlapToAffineOverlap tOverlap) =
          tOverlap
      simp
  · change
      affineOverlapToInfinityOverlap
          (infinityOverlapToAffineOverlap vOverlap) =
        vOverlap
    simp
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The special principal opens of the affine and infinity charts agree. -/
noncomputable def overlapEquiv :
    AffineOverlap ≃+* InfinityOverlap where
  toEquiv :=
    { toFun := affineOverlapToInfinityOverlap
      invFun := infinityOverlapToAffineOverlap
      left_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap z
      right_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap z }
  map_mul' := affineOverlapToInfinityOverlap.map_mul
  map_add' := affineOverlapToInfinityOverlap.map_add
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
/-- Compatible chart pairs are equal once their two chart ideals agree.

The overlap field is a proposition, so proof irrelevance removes it after
the affine and infinity ideals have been identified. -/
@[ext] theorem ChartPair.ext
    {L M : ChartPair}
    (haffine : L.affineIdeal = M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by
  cases L
  cases M
  simp_all
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- Multiplication by `x` can be cancelled modulo an ideal in which `x`
is already a unit. -/
theorem mem_of_x_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    {z : AffineCurve}
    (hz : N13SpecialCurveOverlap.xClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := hx
  have h₁ := Ideal.mul_mem_left I z hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1
  all_goals ring
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- Every power of `x` can be cancelled modulo an ideal in which `x`
is already a unit. -/
theorem mem_of_x_pow_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    (n : ℕ)
    {z : AffineCurve}
    (hz : N13SpecialCurveOverlap.xClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_x_mul_mem hx
      convert hz using 1
      all_goals simp only [pow_succ]
      all_goals ring
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- Localizing a special affine ideal at `x` and contracting it back returns
the original ideal whenever `x` is a unit modulo that ideal. -/
theorem comap_map_affineOverlap_eq_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        (algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap)
        (Ideal.map
          (algebraMap AffineCurve
            N13SpecialCurveOverlap.AffineOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap z ∈
        Ideal.map
          (algebraMap AffineCurve
            N13SpecialCurveOverlap.AffineOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13SpecialCurveOverlap.xClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_x_pow_mul_mem hx n hmz
  · exact Ideal.le_comap_map
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- The direct special affine-to-infinity map factors through localization
at `x` followed by the explicit overlap equivalence. -/
private theorem affineToInfinityOverlap_eq_comp :
    N13SpecialCurveOverlap.affineToInfinityOverlap =
      N13SpecialCurveOverlap.overlapEquiv.toRingHom.comp
        (algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap) := by
  apply DFunLike.ext _ _
  intro z
  change
    N13SpecialCurveOverlap.affineToInfinityOverlap z =
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap z)
  exact
    (N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap
      z).symm
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- Restricting to the actual special overlap loses no information from an
affine ideal in which `x` is already invertible. -/
theorem affineOverlapContracted_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (Ideal.map
          N13SpecialCurveOverlap.affineToInfinityOverlap I) =
      I := by
  let loc :
      AffineCurve →+* N13SpecialCurveOverlap.AffineOverlap :=
    algebraMap AffineCurve
      N13SpecialCurveOverlap.AffineOverlap
  let e :
      N13SpecialCurveOverlap.AffineOverlap →+* InfinityOverlap :=
    N13SpecialCurveOverlap.overlapEquiv.toRingHom
  have he :
      Ideal.comap e (Ideal.map e (Ideal.map loc I)) =
        Ideal.map loc I := by
    rw [Ideal.comap_map_of_surjective e
      N13SpecialCurveOverlap.overlapEquiv.surjective]
    have hker : RingHom.ker e = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e).mp
        N13SpecialCurveOverlap.overlapEquiv.injective
    rw [← RingHom.ker_eq_comap_bot, hker, sup_bot_eq]
  rw [affineToInfinityOverlap_eq_comp,
    ← Ideal.map_map, ← Ideal.comap_comap, he]
  exact comap_map_affineOverlap_eq_of_xUnitMod hx
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- Compatible special chart pairs with the same infinity ideal and
`x`-saturated affine ideals are equal.  Their overlap extensions agree by
compatibility, and saturation contracts that common extension back to the
two original affine ideals. -/
theorem chartPair_eq_of_infinityIdeal_eq
    (L M : N13TwoChartSpecialRestriction.ChartPair)
    (hL : XUnitMod L.affineIdeal)
    (hM : XUnitMod M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · have hoverlap :
        Ideal.map
            N13SpecialCurveOverlap.affineToInfinityOverlap
            L.affineIdeal =
          Ideal.map
            N13SpecialCurveOverlap.affineToInfinityOverlap
            M.affineIdeal := by
      rw [L.overlap_eq, M.overlap_eq, hinfinity]
    rw [← affineOverlapContracted_of_xUnitMod hL,
      ← affineOverlapContracted_of_xUnitMod hM, hoverlap]
  · exact hinfinity
end
end MazurProof.N13SpecialAffineSaturation
end
end


set_option autoImplicit false
open Polynomial
theorem solution
    (L M : MazurProof.N13TwoChartSpecialRestriction.ChartPair)
    (hL : MazurProof.N13SpecialAffineSaturation.XUnitMod L.affineIdeal)
    (hM : MazurProof.N13SpecialAffineSaturation.XUnitMod M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by
  exact MazurProof.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq L M hL hM hinfinity
