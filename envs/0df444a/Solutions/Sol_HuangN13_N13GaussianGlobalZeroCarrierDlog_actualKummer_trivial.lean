-- Prove2me | solution 1 for HuangN13.N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T09:04:32.718256+00:00
-- url     : https://prove2.me/submissions/ddbf866b-351f-4a24-a854-5fb55c3ebb13

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_GaussianUnitLogCore
import Theorems.Thm_HuangN13_N13GaussianGlobalZeroCarrierDlog_factorizationUnit_dlog_eq_zero
import Theorems.Thm_HuangN13_N13GaussianNamedUnitSquareclasses_globalDlogAdd_namedWord
import Theorems.Thm_MazurProof_N13GaussianDifferentSupport_normalizedKummerInteger_eq_unit_mul_sq
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_gaussian_cubic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_root_sextic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_sexticToGaussian_bijective
import Theorems.Thm_MazurProof_N13GaussianNamedUnitTransport_orderToGaussian_apply
import Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_normalizedKummerInteger_ne_zero
import Theorems.Thm_MazurProof_N13LocalDlogTwo_residueCubic_natDegree

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.FakeSquareClass
variable {K L : Type*} [CommRing K] [CommRing L]
/-- A scalar is trivial in the fake square-class target. -/
theorem scalar_eq_one (e : K →+* L) (q : Kˣ) :
    ((scalarUnitsMap e q : Lˣ) : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_right
  exact Subgroup.mem_map_of_mem (scalarUnitsMap e)
    (show q ∈ (⊤ : Subgroup Kˣ) from trivial)
end MazurProof.FakeSquareClass
end
end

section
section
set_option autoImplicit false
namespace MazurProof.FakeSquareClass
variable {K L : Type*} [CommRing K] [CommRing L]
/-- A square is trivial in the fake square-class target. -/
theorem square_eq_one (e : K →+* L) (s : Lˣ) :
    ((s ^ 2 : Lˣ) : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_left
  exact Subgroup.mem_square.mpr ⟨s, by simp [pow_two]⟩
end MazurProof.FakeSquareClass
end
end

section
section
set_option autoImplicit false
namespace MazurProof.FakeSquareClass
variable {K L : Type*} [CommRing K] [CommRing L]
/-- Every element of the fake square-class target has exponent two. -/
@[simp] theorem target_sq_eq_one (e : K →+* L) (z : Target e) :
    z ^ 2 = 1 := by
  refine QuotientGroup.induction_on z ?_
  intro s
  exact square_eq_one e s
end MazurProof.FakeSquareClass
end
end

section
section
set_option autoImplicit false
namespace MazurProof.FakeSquareClass
variable {K L : Type*} [CommRing K] [CommRing L]
/-- If `z` differs from a scalar by a square, its fake class is trivial. -/
theorem eq_one_of_mul_sq_eq_scalar
    (e : K →+* L) (z s : Lˣ) (q : Kˣ)
    (h : z * s ^ 2 = scalarUnitsMap e q) :
    (z : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have hscalar : scalarUnitsMap e q ∈ fakeSquareClassSubgroup e := by
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_map_of_mem (scalarUnitsMap e)
      (show q ∈ (⊤ : Subgroup Kˣ) from trivial)
  have hprod : z * s ^ 2 ∈ fakeSquareClassSubgroup e := by
    rw [h]
    exact hscalar
  have hsq : s ^ 2 ∈ fakeSquareClassSubgroup e := by
    apply Subgroup.mem_sup_left
    exact Subgroup.mem_square.mpr ⟨s, by simp [pow_two]⟩
  have hdiv := (fakeSquareClassSubgroup e).div_mem hprod hsq
  simpa using hdiv
end MazurProof.FakeSquareClass
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
theorem gaussian_cubic_reduction :
    2 * cubicA - Z * cubicB = f * (-4 * X - 2) := by
  simp [cubicA, cubicB, f, N13Mumford.f, Z]
  ring
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
theorem e1_short_reduction :
    E₁ - (2 * (1 - X ^ 2) + (Z - 2) * X) =
      f * (-2) := by
  simp [f, N13Mumford.f, Z, E₁]
  ring
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
theorem e2_short_reduction :
    E₂ -
        (2 + Z * X ^ 2 + (2 + 2 * Z) * X) =
      f * (-(2 * X + 3)) := by
  simp [f, N13Mumford.f, Z, E₂]
  ring
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
private theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
theorem halfOfPoly_eq (p : ℚ[X]) :
    halfOfPoly p =
      AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly p := by
  simp [halfOfPoly, ofPoly, map_mul]
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
theorem zeta_eq_half_mul_Z :
    zeta = AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z := by
  exact halfOfPoly_eq Z
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
private theorem of_two :
    AdjoinRoot.of f (2 : ℚ) = (2 : L) :=
  map_ofNat (AdjoinRoot.of f) 2
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
private theorem of_half_mul_two :
    AdjoinRoot.of f (1 / 2 : ℚ) * (2 : L) = 1 := by
  rw [← of_two, ← map_mul]
  norm_num
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
/-- The sextic root satisfies a cubic equation over `ℚ(i)`. -/
theorem gaussian_cubic :
    theta ^ 3 + 2 * theta ^ 2 - theta - 1 -
        zeta * (2 * theta * (theta + 1)) = 0 := by
  have h := ofPoly_eq_of_sub_eq_mul
    (2 * cubicA - Z * cubicB) 0 (-4 * X - 2)
    (by simpa using gaussian_cubic_reduction)
  have h' :
      2 * (theta ^ 3 + 2 * theta ^ 2 - theta - 1) -
          ofPoly Z * (2 * theta * (theta + 1)) = 0 := by
    simpa [theta, cubicA, cubicB, ofPoly, map_sub, map_mul, map_add,
      map_pow, map_ofNat] using h
  rw [zeta_eq_half_mul_Z]
  let Aθ := theta ^ 3 + 2 * theta ^ 2 - theta - 1
  let Bθ := 2 * theta * (theta + 1)
  calc
    Aθ - (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * Bθ =
        (AdjoinRoot.of f (1 / 2 : ℚ) * 2) * Aθ -
          AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z * Bθ := by
            rw [of_half_mul_two]
            ring
    _ = AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 * Aθ - ofPoly Z * Bθ) := by ring
    _ = 0 := by rw [show 2 * Aθ - ofPoly Z * Bθ = 0 from h']; ring
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
/-- The first fundamental unit in the Gaussian cubic basis. -/
theorem e1_short :
    e1 = 1 - theta ^ 2 + (zeta - 1) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    E₁ (2 * (1 - X ^ 2) + (Z - 2) * X) (-2)
    e1_short_reduction
  have h' :
      ofPoly E₁ =
        2 * (1 - theta ^ 2) + (ofPoly Z - 2) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show e1 = halfOfPoly E₁ from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly E₁ =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 * (1 - theta ^ 2) + (ofPoly Z - 2) * theta) := by
            rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) *
          (1 - theta ^ 2) +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z -
          AdjoinRoot.of f (1 / 2 : ℚ) * 2) * theta := by ring
    _ = 1 - theta ^ 2 +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z - 1) * theta := by
          simp only [of_half_mul_two, one_mul]
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianCubic
noncomputable section
open N13SexticSquareclass
/-- The second fundamental unit in the Gaussian cubic basis. -/
theorem e2_short :
    e2 = 1 + zeta * theta ^ 2 + (1 + 2 * zeta) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    E₂ (2 + Z * X ^ 2 + (2 + 2 * Z) * X)
    (-(2 * X + 3))
    e2_short_reduction
  have h' :
      ofPoly E₂ =
        2 + ofPoly Z * theta ^ 2 +
          (2 + 2 * ofPoly Z) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show e2 = halfOfPoly E₂ from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly E₂ =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 + ofPoly Z * theta ^ 2 +
            (2 + 2 * ofPoly Z) * theta) := by rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 +
        ((AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
          2 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z)) * theta := by
            ring
    _ = 1 + (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 +
        (1 + 2 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z)) * theta := by
          rw [of_half_mul_two]
end
end MazurProof.N13GaussianCubic
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticToGaussian_theta :
    sexticToGaussian N13GaussianCubic.theta =
      gaussianTheta :=
  AdjoinRoot.liftAlgHom_root
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
def sexticEquivGaussian : Ls ≃ₐ[ℚ] Lg :=
  AlgEquiv.ofBijective sexticToGaussian
    sexticToGaussian_bijective
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticEquivGaussian_theta :
    sexticEquivGaussian N13GaussianCubic.theta =
      gaussianTheta :=
  sexticToGaussian_theta
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticEquivGaussian_ofPoly
    (p : ℚ[X]) :
    sexticEquivGaussian
        (N13SexticSquareclass.ofPoly p) =
      eval₂ (algebraMap ℚ Lg) gaussianTheta p := by
  change
    sexticToGaussian
        (AdjoinRoot.mk N13SexticSquareclass.f p) =
      eval₂ (algebraMap ℚ Lg) gaussianTheta p
  exact AdjoinRoot.liftAlgHom_mk
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic p
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg
theorem gaussianTheta_isUnit :
    IsUnit gaussianTheta :=
  isUnit_iff_exists_inv.mpr
    ⟨gaussianTheta ^ 2 +
      (2 - 2 * gaussianI) * gaussianTheta +
      (-1 - 2 * gaussianI),
      gaussianTheta_mul_inverse⟩
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg
theorem gaussianTheta_add_one_isUnit :
    IsUnit (gaussianTheta + 1) :=
  isUnit_iff_exists_inv.mpr
    ⟨-(gaussianTheta ^ 2 +
        (1 - 2 * gaussianI) * gaussianTheta - 2),
      gaussianTheta_add_one_mul_inverse⟩
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg
theorem gaussianCubicImaginaryFactor_isUnit :
    IsUnit (2 * gaussianTheta * (gaussianTheta + 1)) :=
  ((isUnit_iff_ne_zero.mpr
      (by
        intro htwo
        have htwoK : (2 : K) = 0 :=
          (algebraMap K Lg).injective (by
            simpa only [map_ofNat, map_zero] using htwo)
        norm_num at htwoK)).mul
    gaussianTheta_isUnit).mul gaussianTheta_add_one_isUnit
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticEquivGaussian_zeta :
    sexticEquivGaussian N13SexticSquareclass.zeta =
      gaussianI := by
  let zI : Lg :=
    sexticEquivGaussian N13SexticSquareclass.zeta
  let Bθ : Lg :=
    2 * gaussianTheta * (gaussianTheta + 1)
  have hz :
      gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 - zI * Bθ = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_one, map_zero, sexticEquivGaussian_theta]
      using
        congrArg sexticEquivGaussian
          N13GaussianCubic.gaussian_cubic
  have hi :
      gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 - gaussianI * Bθ = 0 := by
    simpa only [Bθ] using gaussianTheta_gaussian_cubic
  apply gaussianCubicImaginaryFactor_isUnit.mul_right_cancel
  calc
    zI * Bθ =
        gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 :=
      (sub_eq_zero.mp hz).symm
    _ = gaussianI * Bθ :=
      sub_eq_zero.mp hi
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticEquivGaussian_e1 :
    sexticEquivGaussian N13SexticSquareclass.e1 =
      1 - gaussianTheta ^ 2 +
        (gaussianI - 1) * gaussianTheta := by
  simpa only [map_add, map_sub, map_mul, map_pow,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.e1_short
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticEquivGaussian_e2 :
    sexticEquivGaussian N13SexticSquareclass.e2 =
      1 + gaussianI * gaussianTheta ^ 2 +
        (1 + 2 * gaussianI) * gaussianTheta := by
  simpa only [map_add, map_mul, map_pow, map_ofNat,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.e2_short
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
theorem integralNormalization_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    integralNormalization p ≠ 0 := by
  exact
    (IsFractionRing.integerNormalization_eq_zero_iff
      (A := ℤ) (K := ℚ)).not.mpr hp
end
end MazurProof.N13GlobalKummerNormalization
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizedGCDMonoid
theorem integralNormalization_content_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    (integralNormalization p).content ≠ 0 := by
  exact
    Polynomial.content_eq_zero_iff.not.mpr
      (integralNormalization_ne_zero hp)
end
end MazurProof.N13GlobalKummerNormalization
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizedGCDMonoid
theorem primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      (primitiveNormalization p).map
          (algebraMap ℤ ℚ) =
        C c * p := by
  let U₀ : ℤ[X] := integralNormalization p
  let U : ℤ[X] := primitiveNormalization p
  obtain ⟨b, hb, hclear⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  have hb0 : b ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbc :
      algebraMap ℤ ℚ b ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne hb0
  have hcontent :
      algebraMap ℤ ℚ U₀.content ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne
      (integralNormalization_content_ne_zero hp)
  let c : ℚ :=
    (algebraMap ℤ ℚ U₀.content)⁻¹ *
      algebraMap ℤ ℚ b
  refine
    ⟨c, mul_ne_zero (inv_ne_zero hcontent) hbc, ?_⟩
  have hdecomp :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ U₀.content) *
          U.map (algebraMap ℤ ℚ) := by
    simpa only [U₀, U, integralNormalization,
      primitiveNormalization, Polynomial.map_mul,
      Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap ℤ ℚ))
        U₀.eq_C_content_mul_primPart
  have hcleared :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
    simpa only [U₀, integralNormalization,
      Algebra.smul_def, Polynomial.algebraMap_apply] using
      hclear
  calc
    U.map (algebraMap ℤ ℚ) =
        1 * U.map (algebraMap ℤ ℚ) := by rw [one_mul]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
            C (algebraMap ℤ ℚ U₀.content)) *
          U.map (algebraMap ℤ ℚ) := by
      rw [← C_mul, inv_mul_cancel₀ hcontent,
        C_1, one_mul]
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ U₀.content) *
            U.map (algebraMap ℤ ℚ)) := by ring
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ b) * p) := by
      rw [← hdecomp, hcleared]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          C (algebraMap ℤ ℚ b)) * p := by ring
    _ = C c * p := by rw [← C_mul]
end
end MazurProof.N13GlobalKummerNormalization
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GlobalKummerNormalization.fieldL
theorem integralEval_primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((integralEval (primitiveNormalization p) :
          integralClosure ℤ L) : L) =
        algebraMap ℚ L c *
          eval₂ (algebraMap ℚ L) gaussianTheta p := by
  obtain ⟨c, hc, hpoly⟩ :=
    primitiveNormalization_spec hp
  refine ⟨c, hc, ?_⟩
  calc
    ((integralEval (primitiveNormalization p) :
        integralClosure ℤ L) : L) =
        eval₂ (algebraMap ℤ L) gaussianTheta
          (primitiveNormalization p) := by
      rw [coe_integralEval]
    _ =
        eval₂ (algebraMap ℚ L) gaussianTheta
          ((primitiveNormalization p).map
            (algebraMap ℤ ℚ)) := by
      rw [Polynomial.eval₂_map,
        IsScalarTower.algebraMap_eq ℤ ℚ L]
    _ =
        eval₂ (algebraMap ℚ L) gaussianTheta
          (C c * p) := by rw [hpoly]
    _ =
        algebraMap ℚ L c *
          eval₂ (algebraMap ℚ L) gaussianTheta p := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
end
end MazurProof.N13GlobalKummerNormalization
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GlobalKummerNormalization.fieldL
theorem normalizedKummerInteger_spec
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((normalizedKummerInteger D :
          integralClosure ℤ L) : L) =
        algebraMap ℚ L c *
          sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) := by
  have hu : D.toSemi.u ≠ 0 :=
    D.toSemi.u_monic.ne_zero
  obtain ⟨c, hc, hspec⟩ :=
    integralEval_primitiveNormalization_spec hu
  refine ⟨c, hc, ?_⟩
  rw [normalizedKummerInteger]
  rw [N13MumfordKummerValue.uTheta_eq_mk]
  change
    ((integralEval
        (primitiveNormalization D.toSemi.u) :
        integralClosure ℤ L) : L) =
      algebraMap ℚ L c *
        sexticEquivGaussian
          (N13SexticSquareclass.ofPoly D.toSemi.u)
  rw [sexticEquivGaussian_ofPoly]
  exact hspec
end
end MazurProof.N13GlobalKummerNormalization
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianSignature
noncomputable section
attribute [local instance] MazurProof.N13GaussianSignature.fieldL
@[simp] theorem nrRealPlaces_eq_zero :
    NumberField.InfinitePlace.nrRealPlaces L = 0 :=
  NumberField.IsTotallyComplex.nrRealPlaces_eq_zero L
end
end MazurProof.N13GaussianSignature
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianSignature
noncomputable section
attribute [local instance] MazurProof.N13GaussianSignature.fieldL
@[simp] theorem infinitePlace_card_eq_three :
    Fintype.card (NumberField.InfinitePlace L) = 3 := by
  rw [
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L,
    nrRealPlaces_eq_zero,
    nrComplexPlaces_eq_three
  ]
end
end MazurProof.N13GaussianSignature
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianSignature
noncomputable section
attribute [local instance] MazurProof.N13GaussianSignature.fieldL
@[simp] theorem units_rank_eq_two :
    NumberField.Units.rank L = 2 := by
  simp [NumberField.Units.rank]
end
end MazurProof.N13GaussianSignature
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GlobalKummerPID.fieldL
private def integralClosureToClassNumberOrder (x : O) :
    N13GaussianClassNumberOne.O :=
  ⟨x.val, isIntegralElem_int_of x.property⟩
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
private theorem subtypeConstructor_val {A : Type*} {p : A → Prop}
    (a : A) (ha : p a) :
    (⟨a, ha⟩ : Subtype p).val = a := rfl
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GlobalKummerPID.fieldL MazurProof.N13GlobalKummerPID.intAlgebraL
private theorem integralClosureToClassNumberOrder_val (x : O) :
    (integralClosureToClassNumberOrder x).val = x.val :=
  subtypeConstructor_val x.val
    (isIntegralElem_int_of (g := algebraMap ℤ L) x.property)
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL
/-- The normalization order and the class-number order have literally the
same underlying element of the ambient number field.  Exporting this small
carrier theorem prevents downstream proofs from unfolding the full ring
equivalence. -/
@[simp] theorem coe_integralClosureEquivClassNumberOrder
    (x : O) :
    (integralClosureEquivClassNumberOrder.toEquiv.toFun x).val =
      x.val :=
  integralClosureToClassNumberOrder_val x
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
/--
No nonzero polynomial of degree at most two can vanish at `α`, whose
minimal polynomial has degree three.
-/
private theorem coeffs_zero_of_power_sum_zero
    (c0 c1 c2 : ZMod 2)
    (h :
      (c0 : F8) + (c1 : F8) * alpha +
          (c2 : F8) * alpha ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  let p : (ZMod 2)[X] :=
    C c0 + C c1 * X + C c2 * X ^ 2
  have hm : AdjoinRoot.mk residueCubic p = 0 := by
    simpa [p, alpha, map_add, map_mul, map_pow] using h
  have hdvd : residueCubic ∣ p :=
    AdjoinRoot.mk_eq_zero.mp hm
  have hpdeg : p.natDegree ≤ 2 := by
    dsimp [p]
    compute_degree
  have hdeg : p.natDegree < residueCubic.natDegree := by
    rw [residueCubic_natDegree]
    omega
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  have h0 := congrArg (fun q : (ZMod 2)[X] => q.coeff 0) hpzero
  have h1 := congrArg (fun q : (ZMod 2)[X] => q.coeff 1) hpzero
  have h2 := congrArg (fun q : (ZMod 2)[X] => q.coeff 2) hpzero
  simp [p, coeff_X_pow] at h0 h1 h2
  exact ⟨h0, h1, h2⟩
end
end MazurProof.N13LocalDlogTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
/--
The first ramified character kills exactly two of the sixteen binary
candidates: the identity and `e₂(aq)`.
-/
theorem candidateDlog_eq_zero_iff
    (i j k s : ZMod 2) :
    candidateDlog i j k s = 0 ↔
      i = 0 ∧ j = 0 ∧ k = s := by
  constructor
  · intro h
    obtain ⟨hi, hks, hjks⟩ :=
      coeffs_zero_of_power_sum_zero i (k + s) (j + k + s)
        (by simpa only [candidateDlog] using h)
    have hkeqs : k = s :=
      CharTwo.add_eq_zero.mp hks
    have hj : j = 0 := by
      rw [hkeqs] at hjks
      exact (CharTwo.add_cancel_right j s).symm.trans hjks
    exact ⟨hi, hj, hkeqs⟩
  · rintro ⟨rfl, rfl, hks⟩
    rw [hks]
    simp [candidateDlog]
end
end MazurProof.N13LocalDlogTwo
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
/-- Transporting the range of the square map across a multiplicative
equivalence. -/
private theorem map_powTwo_range_equiv
    {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) :
    ((powMonoidHom 2 : G →* G).range).map
        e.toMonoidHom =
      (powMonoidHom 2 : H →* H).range := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    refine ⟨e z, ?_⟩
    change z ^ 2 = x at hz
    change (e z) ^ 2 = e x
    simpa only [map_pow] using congrArg e hz
  · rintro ⟨z, hz⟩
    refine ⟨(e.symm z) ^ 2, ⟨e.symm z, rfl⟩, ?_⟩
    change z ^ 2 = y at hz
    change e ((e.symm z) ^ 2) = y
    rw [map_pow, e.apply_symm_apply, hz]
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
/-- The square-map index is invariant under multiplicative equivalence. -/
private theorem index_powTwo_range_equiv
    {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) :
    (powMonoidHom 2 : G →* G).range.index =
      (powMonoidHom 2 : H →* H).range.index := by
  calc
    (powMonoidHom 2 : G →* G).range.index =
        (((powMonoidHom 2 : G →* G).range).map
          e.toMonoidHom).index :=
      (Subgroup.index_map_equiv
        (H := (powMonoidHom 2 : G →* G).range) e).symm
    _ = (powMonoidHom 2 : H →* H).range.index := by
      rw [map_powTwo_range_equiv e]
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
/-- The range of squaring on a product is the product of the two ranges. -/
private theorem powTwo_range_prod
    (A B : Type*) [CommGroup A] [CommGroup B] :
    (powMonoidHom 2 : A × B →* A × B).range =
      ((powMonoidHom 2 : A →* A).range).prod
        (powMonoidHom 2 : B →* B).range := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    exact Prod.ext ha hb
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
private theorem index_powTwo_range_cyclic
    (C : Type*) [CommGroup C] [Finite C] [IsCyclic C] :
    (powMonoidHom 2 : C →* C).range.index =
      (Nat.card C).gcd 2 :=
  IsCyclic.index_powMonoidHom_range C 2
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
private theorem index_powTwo_range_multiplicative
    (F : Type*) [AddCommGroup F]
    [Module.Free ℤ F] [Module.Finite ℤ F] :
    (powMonoidHom 2 :
        Multiplicative F →* Multiplicative F).range.index =
      2 ^ Module.finrank ℤ F := by
  rw [← Subgroup.index_toAddSubgroup]
  rw [← MonoidHom.coe_toAdditive_range]
  change
    (nsmulAddMonoidHom (α := F) 2).range.index =
      2 ^ Module.finrank ℤ F
  exact AddSubgroup.index_range_nsmul F 2
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
/-- Exact square-map index for a finite cyclic factor times a finite free
abelian factor. -/
theorem index_powTwo_range_eq_gcd_mul_pow
    {G C F : Type*}
    [CommGroup G]
    [CommGroup C] [Finite C] [IsCyclic C]
    [AddCommGroup F]
    [Module.Free ℤ F] [Module.Finite ℤ F]
    (e : G ≃* C × Multiplicative F) :
    (powMonoidHom 2 : G →* G).range.index =
      (Nat.card C).gcd 2 *
        2 ^ Module.finrank ℤ F := by
  calc
    (powMonoidHom 2 : G →* G).range.index =
        (powMonoidHom 2 :
          C × Multiplicative F →*
            C × Multiplicative F).range.index :=
      index_powTwo_range_equiv e
    _ = (((powMonoidHom 2 : C →* C).range).prod
          (powMonoidHom 2 :
            Multiplicative F →*
              Multiplicative F).range).index := by
      rw [powTwo_range_prod]
    _ = (powMonoidHom 2 : C →* C).range.index *
          (powMonoidHom 2 :
            Multiplicative F →*
              Multiplicative F).range.index := by
      rw [Subgroup.index_prod]
    _ = (Nat.card C).gcd 2 *
          2 ^ Module.finrank ℤ F := by
      rw [index_powTwo_range_cyclic,
        index_powTwo_range_multiplicative]
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
/-- Even torsion contributes one additional binary squareclass. -/
theorem index_powTwo_range_eq_pow_succ_of_even
    {G C F : Type*}
    [CommGroup G]
    [CommGroup C] [Finite C] [IsCyclic C]
    [AddCommGroup F]
    [Module.Free ℤ F] [Module.Finite ℤ F]
    (e : G ≃* C × Multiplicative F)
    (hC : Even (Nat.card C)) :
    (powMonoidHom 2 : G →* G).range.index =
      2 ^ (Module.finrank ℤ F + 1) := by
  rw [index_powTwo_range_eq_gcd_mul_pow e,
    Nat.gcd_eq_right_iff_dvd.mpr hC.two_dvd]
  simp [pow_succ']
end MazurProof.UnitSquareClass
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace NumberField.Units
variable (K : Type*) [Field K] [NumberField K]
/-- Exact square-map index for the unit group of a number field. -/
theorem unit_powTwo_range_index :
    (powMonoidHom 2 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range.index =
      2 ^ (rank K + 1) := by
  classical

  letI : Module.Free ℤ (Fin (rank K) → ℤ) :=
    Module.Free.of_basis
      (Pi.basisFun ℤ (Fin (rank K)))
  letI : Module.Finite ℤ (Fin (rank K) → ℤ) :=
    Module.Finite.of_basis
      (Pi.basisFun ℤ (Fin (rank K)))

  have hfinrank :
      Module.finrank ℤ (Fin (rank K) → ℤ) =
        rank K := by
    simpa using
      Module.finrank_eq_card_basis
        (Pi.basisFun ℤ (Fin (rank K)))

  have hEven :
      Even (Nat.card (torsion K)) := by
    simpa only [torsionOrder] using even_torsionOrder K

  have h :=
    MazurProof.UnitSquareClass.index_powTwo_range_eq_pow_succ_of_even
        (e := (dirichletMulEquiv K).symm) hEven
  simpa [hfinrank] using h
end NumberField.Units
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace NumberField.Units
variable (K : Type*) [Field K] [NumberField K]
/-- Cardinality of the quotient of units by squares. -/
theorem natCard_unit_quotient_squares :
    Nat.card
      (((NumberField.RingOfIntegers K)ˣ) ⧸
        (powMonoidHom 2 :
          (NumberField.RingOfIntegers K)ˣ →*
            (NumberField.RingOfIntegers K)ˣ).range) =
      2 ^ (rank K + 1) := by
  change
    (powMonoidHom 2 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range.index =
      2 ^ (rank K + 1)
  exact unit_powTwo_range_index K
end NumberField.Units
end
end
end

section
section
set_option autoImplicit false
open Finset Module
noncomputable section
namespace MazurProof.N13GaussianUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianSignature.fieldL MazurProof.N13GaussianUnitSquareclasses.fieldL
/-- The N13 unit squareclass group has exactly eight elements. -/
theorem unit_squareclass_natCard :
    Nat.card
      (((NumberField.RingOfIntegers L)ˣ) ⧸
        (powMonoidHom 2 :
          (NumberField.RingOfIntegers L)ˣ →*
            (NumberField.RingOfIntegers L)ˣ).range) =
      8 := by
  rw [NumberField.Units.natCard_unit_quotient_squares L,
    N13GaussianSignature.units_rank_eq_two]
  norm_num
end MazurProof.N13GaussianUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- The corresponding unit squareclass. -/
def namedExponentClass : Exp3 → UnitModSq :=
  fun c => unitClassHom (namedWord c)
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- In characteristic two, the global logarithm kills every square. -/
theorem globalDlogAdd_sq (u : Oˣ) :
    globalDlogAdd (Additive.ofMul (u ^ 2)) = 0 := by
  simpa only [pow_two, ofMul_mul, map_add] using
    CharTwo.add_self_eq_zero
      (globalDlogAdd (Additive.ofMul u))
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- Equal literal unit squareclasses have equal logarithms.  This direct
quotient argument avoids constructing any list of representatives. -/
theorem globalDlogAdd_eq_of_unitClass_eq
    {x y : Oˣ}
    (hxy : unitClassHom x = unitClassHom y) :
    globalDlogAdd (Additive.ofMul x) =
      globalDlogAdd (Additive.ofMul y) := by
  have hsquare :
      x / y ∈ (powMonoidHom 2 : Oˣ →* Oˣ).range :=
    (QuotientGroup.eq_iff_div_mem
      (N := (powMonoidHom 2 : Oˣ →* Oˣ).range)).mp hxy
  rcases hsquare with ⟨u, hu⟩
  have hzero :
      globalDlogAdd (Additive.ofMul (x / y)) = 0 := by
    rw [← hu]
    exact globalDlogAdd_sq u
  have hsub :
      globalDlogAdd (Additive.ofMul x) -
          globalDlogAdd (Additive.ofMul y) = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- The logarithm of a named word, expanded in the structural power basis
`1, α, α²` of the residue field. -/
theorem globalDlogAdd_namedWord (c : Exp3) :
    globalDlogAdd (Additive.ofMul (namedWord c)) =
      (c.1 : F8) +
        (c.2.2 : F8) * N13LocalDlogTwo.alpha +
        (c.2.1 + c.2.2 : F2) *
          N13LocalDlogTwo.alpha ^ 2 := by
  exact HuangN13.N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord c
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
/-- No polynomial of degree below three vanishes at the residue generator.
This is the only independence input; it uses divisibility by the defining
cubic, not an enumeration of `F₈`. -/
private theorem residue_coeffs_zero
    (c0 c1 c2 : F2)
    (h :
      (c0 : F8) + (c1 : F8) * N13LocalDlogTwo.alpha +
          (c2 : F8) * N13LocalDlogTwo.alpha ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  let p : F2[X] :=
    C c0 + C c1 * X + C c2 * X ^ 2
  have hm :
      AdjoinRoot.mk N13LocalDlogTwo.residueCubic p = 0 := by
    simpa [p, N13LocalDlogTwo.alpha, map_add, map_mul,
      map_pow] using h
  have hdvd : N13LocalDlogTwo.residueCubic ∣ p :=
    AdjoinRoot.mk_eq_zero.mp hm
  have hpdeg : p.natDegree ≤ 2 := by
    dsimp [p]
    compute_degree
  have hdeg :
      p.natDegree <
        N13LocalDlogTwo.residueCubic.natDegree := by
    rw [N13LocalDlogTwo.residueCubic_natDegree]
    omega
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  have h0 :=
    congrArg (fun q : F2[X] => q.coeff 0) hpzero
  have h1 :=
    congrArg (fun q : F2[X] => q.coeff 1) hpzero
  have h2 :=
    congrArg (fun q : F2[X] => q.coeff 2) hpzero
  simp [p, coeff_X_pow] at h0 h1 h2
  exact ⟨h0, h1, h2⟩
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- The three named exponent bits give distinct unit squareclasses. -/
theorem namedExponentClass_injective :
    Function.Injective namedExponentClass := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hclass
  have hclass' :
      unitClassHom (namedWord (i, j, k)) =
        unitClassHom (namedWord (i', j', k')) := by
    simpa [namedExponentClass] using hclass
  have hdlog :=
    globalDlogAdd_eq_of_unitClass_eq hclass'
  have hdlog' :
      (i : F8) + (k : F8) * N13LocalDlogTwo.alpha +
          (j + k : F2) * N13LocalDlogTwo.alpha ^ 2 =
        (i' : F8) + (k' : F8) * N13LocalDlogTwo.alpha +
          (j' + k' : F2) *
            N13LocalDlogTwo.alpha ^ 2 := by
    simpa [namedExponentClass, globalDlogAdd_namedWord]
      using hdlog
  simp only [map_add] at hdlog'
  have hzero :
      ((i - i' : F2) : F8) +
          ((k - k' : F2) : F8) *
            N13LocalDlogTwo.alpha +
          (((j + k) - (j' + k') : F2) : F8) *
            N13LocalDlogTwo.alpha ^ 2 = 0 := by
    simp only [map_sub, map_add]
    linear_combination hdlog'
  obtain ⟨hi0, hk0, hjk0⟩ :=
    residue_coeffs_zero
      (i - i') (k - k') ((j + k) - (j' + k'))
      hzero
  have hi : i = i' := sub_eq_zero.mp hi0
  have hk : k = k' := sub_eq_zero.mp hk0
  have hjk : j + k = j' + k' := sub_eq_zero.mp hjk0
  have hj : j = j' := by
    calc
      j = (j + k) - k := by simp
      _ = (j' + k') - k := by rw [hjk]
      _ = (j' + k) - k := by rw [hk]
      _ = j' := by simp
  exact Prod.ext hi (Prod.ext hj hk)
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
@[simp] theorem unitModSq_natCard :
    Nat.card UnitModSq = 8 :=
  N13GaussianUnitSquareclasses.unit_squareclass_natCard
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
/-- Cardinality eight turns the structural independence theorem into
generation of every unit squareclass. -/
theorem namedExponentClass_bijective :
    Function.Bijective namedExponentClass := by
  have hcard0 : Nat.card UnitModSq ≠ 0 := by
    rw [unitModSq_natCard]
    norm_num
  letI : Finite UnitModSq :=
    Nat.finite_of_card_ne_zero hcard0
  apply
    (Nat.bijective_iff_injective_and_card
      namedExponentClass).2
  refine ⟨namedExponentClass_injective, ?_⟩
  calc
    Nat.card Exp3 = 8 := by
      norm_num [Exp3, F2, Nat.card_prod, Nat.card_zmod]
    _ = Nat.card UnitModSq := unitModSq_natCard.symm
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- Every maximal-order unit is a named binary product times a square.
The proof never examines the eight possible exponent triples. -/
theorem unit_modSq_decompose_named (ε : Oˣ) :
    ∃ i j k : F2, ∃ η : Oˣ,
      ε =
        zetaUnit ^ i.val *
          e1Unit ^ j.val *
          e2Unit ^ k.val * η ^ 2 := by
  obtain ⟨c, hc⟩ :=
    namedExponentClass_bijective.2 (unitClassHom ε)
  rcases c with ⟨i, j, k⟩
  have hq :
      (ε : UnitModSq) =
        (namedWord (i, j, k) : UnitModSq) := by
    simpa [namedExponentClass, unitClassHom] using hc.symm
  have hsquare :
      ε / namedWord (i, j, k) ∈
        (powMonoidHom 2 : Oˣ →* Oˣ).range :=
    (QuotientGroup.eq_iff_div_mem
      (N := (powMonoidHom 2 : Oˣ →* Oˣ).range)).mp hq
  rcases hsquare with ⟨η, hη⟩
  refine ⟨i, j, k, η, ?_⟩
  calc
    ε =
        (ε / namedWord (i, j, k)) *
          namedWord (i, j, k) := by simp
    _ = η ^ 2 * namedWord (i, j, k) := by
      rw [← hη]
      rfl
    _ = namedWord (i, j, k) * η ^ 2 := mul_comm _ _
    _ =
        zetaUnit ^ i.val *
          e1Unit ^ j.val *
          e2Unit ^ k.val * η ^ 2 := by rfl
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
def e1Unit : Lˣ := e1_isUnit.unit
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
def e2Unit : Lˣ := e2_isUnit.unit
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
def survivorUnit : Lˣ :=
  e2Unit * primeAUnit * primeQUnit
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
def squareFactorUnit : Lˣ :=
  zetaUnit * e1Unit * primeAUnit
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
/-- The nonzero first-jet survivor is already trivial in the fake target. -/
theorem survivorUnit_fake_class_eq_one :
    ((survivorUnit : Lˣ) :
      FakeSquareClass.Target (algebraMap ℚ L)) = 1 := by
  apply FakeSquareClass.eq_one_of_mul_sq_eq_scalar
    (algebraMap ℚ L) survivorUnit squareFactorUnit thirteenUnit
  apply Units.ext
  change survivor * squareFactor ^ 2 = algebraMap ℚ L (13 : ℚ)
  exact survivor_mul_square
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
/-- The global candidate attached to four binary exponents. -/
def candidateUnit (i j k s : ZMod 2) : Lˣ :=
  zetaUnit ^ i.val * e1Unit ^ j.val * e2Unit ^ k.val *
    (primeAUnit * primeQUnit) ^ s.val
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
def candidateClass (i j k s : ZMod 2) :
    FakeSquareClass.Target (algebraMap ℚ L) :=
  candidateUnit i j k s
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
namespace MazurProof.N13CandidateCollapse
noncomputable section
open N13SexticSquareclass
/-- One `F₈` equation plus the scalar identity kills every candidate. -/
theorem candidateClass_eq_one_of_dlog_eq_zero
    (i j k s : ZMod 2)
    (hlocal : N13LocalDlogTwo.candidateDlog i j k s = 0) :
    candidateClass i j k s = 1 := by
  obtain ⟨hi, hj, hks⟩ :=
    (N13LocalDlogTwo.candidateDlog_eq_zero_iff i j k s).mp hlocal
  subst i
  subst j
  subst k
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hs with rfl | rfl
  · simp [candidateClass, candidateUnit]
    rfl
  · simp only [candidateClass, candidateUnit, ZMod.val_zero,
      ZMod.val_one 2, pow_zero, pow_one, one_mul]
    simpa [survivorUnit, mul_assoc] using survivorUnit_fake_class_eq_one
end
end MazurProof.N13CandidateCollapse
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- The carrier-preserving ring map from the maximal order directly to the
sextic presentation.  No additional algebra instance is introduced. -/
def orderToSextic : O →+* Ls :=
  N13GaussianFieldEquiv.sexticEquivGaussian.symm.toRingEquiv.toRingHom.comp
    orderToGaussian
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitTransport.fieldLg
@[simp] theorem orderToSextic_apply (x : O) :
    orderToSextic x =
      N13GaussianFieldEquiv.sexticEquivGaussian.symm (x : Lg) := by
  simp [orderToSextic, MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply]
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem orderToSextic_injective :
    Function.Injective orderToSextic :=
  N13GaussianFieldEquiv.sexticEquivGaussian.symm.injective.comp
    orderToGaussian_injective
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- Transport maximal-order units through the proved equivalence between the
sextic and Gaussian cubic presentations. -/
def orderUnitsToSextic : Oˣ →* Lsˣ :=
  (Units.map
      N13GaussianFieldEquiv.sexticEquivGaussian.symm.toMonoidHom).comp
    orderUnitsToGaussian
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- The previously defined unit transport is exactly the unit map induced by
the direct carrier-preserving ring homomorphism. -/
theorem unitsMap_orderToSextic_eq :
    Units.map orderToSextic.toMonoidHom =
      orderUnitsToSextic := by
  ext u
  rfl
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem map_relativeTheta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianGlobalReductionTwo.relativeTheta =
      N13GaussianFieldEquiv.gaussianTheta := by
  change
    ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
        N13GaussianGlobalReductionTwo.RelativeO) : Lg) + 9 =
      N13GaussianCubicField.alpha + 9
  rw [N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen]
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem map_relativeZeta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeZeta =
      N13GaussianFieldEquiv.gaussianI := by
  change
    algebraMap N13GaussianGlobalArithmetic.GI Lg
        N13GaussianGlobalArithmetic.i =
      N13GaussianFieldEquiv.gaussianI
  rw [N13GaussianFieldEquiv.gaussianI,
    IsScalarTower.algebraMap_apply
      N13GaussianGlobalArithmetic.GI
      N13GaussianCubicField.K Lg]
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem orderUnitsToGaussian_zeta_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.zetaUnit : O) =
      N13GaussianFieldEquiv.gaussianI := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeZeta) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.gaussianI
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply]
  exact map_relativeZeta
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem orderUnitsToGaussian_e1_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.e1Unit : O) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1 := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeE1) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_e1]
  change
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeE1 =
      1 - N13GaussianFieldEquiv.gaussianTheta ^ 2 +
        (N13GaussianFieldEquiv.gaussianI - 1) *
          N13GaussianFieldEquiv.gaussianTheta
  simp only [N13GaussianNamedUnitSquareclasses.relativeE1,
    map_add, map_sub, map_pow, map_mul, map_one,
    map_relativeTheta, map_relativeZeta]
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem orderUnitsToGaussian_e2_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.e2Unit : O) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2 := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeE2) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_e2]
  change
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeE2 =
      1 + N13GaussianFieldEquiv.gaussianI *
          N13GaussianFieldEquiv.gaussianTheta ^ 2 +
        (1 + 2 * N13GaussianFieldEquiv.gaussianI) *
          N13GaussianFieldEquiv.gaussianTheta
  simp only [N13GaussianNamedUnitSquareclasses.relativeE2,
    map_add, map_mul, map_pow, map_one, map_ofNat,
    map_relativeTheta, map_relativeZeta]
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
@[simp] theorem orderUnitsToSextic_zeta :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.zetaUnit =
      N13CandidateCollapse.zetaUnit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.zetaUnit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.zeta
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_zeta]
  exact orderUnitsToGaussian_zeta_val
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
@[simp] theorem orderUnitsToSextic_e1 :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.e1Unit =
      N13CandidateCollapse.e1Unit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.e1Unit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply]
  exact orderUnitsToGaussian_e1_val
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
@[simp] theorem orderUnitsToSextic_e2 :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.e2Unit =
      N13CandidateCollapse.e2Unit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.e2Unit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply]
  exact orderUnitsToGaussian_e2_val
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
/-- Direct transport from the normalization order to the sextic field. -/
def normalizationOrderToSextic : Oi →+* Ls :=
  N13GaussianNamedUnitTransport.orderToSextic.comp
    normalizationOrderEquiv.toRingHom
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
/-- The direct transport preserves the underlying Gaussian field element.
The proof uses only the two small carrier interfaces and never unfolds the
integral-closure equivalence. -/
@[simp] theorem normalizationOrderToSextic_apply
    (x : Oi) :
    normalizationOrderToSextic x =
      N13GaussianFieldEquiv.sexticEquivGaussian.symm
        (x : Lg) := by
  calc
    normalizationOrderToSextic x =
        N13GaussianNamedUnitTransport.orderToSextic
          (normalizationOrderEquiv x) := rfl
    _ =
        N13GaussianFieldEquiv.sexticEquivGaussian.symm
          ((normalizationOrderEquiv x : On) : Lg) :=
      N13GaussianNamedUnitTransport.orderToSextic_apply
        (normalizationOrderEquiv x)
    _ =
        N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (x : Lg) := by
      have hfun :
          normalizationOrderEquiv x =
            N13GlobalKummerPID.integralClosureEquivClassNumberOrder.toFun x := rfl
      rw [hfun]
      exact
        congrArg N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (N13GlobalKummerPID.coe_integralClosureEquivClassNumberOrder x)
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
theorem normalizationOrderToSextic_injective :
    Function.Injective normalizationOrderToSextic :=
  N13GaussianNamedUnitTransport.orderToSextic_injective.comp
    normalizationOrderEquiv.injective
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
/-- The unit map induced by the composite order embedding factors through
the compiled maximal-order unit transport. -/
theorem unitsMap_normalizationOrderToSextic_eq :
    Units.map normalizationOrderToSextic.toMonoidHom =
      N13GaussianNamedUnitTransport.orderUnitsToSextic.comp
        (Units.map normalizationOrderEquiv.toMonoidHom) := by
  rw [← N13GaussianNamedUnitTransport.unitsMap_orderToSextic_eq]
  exact
    Units.map_comp normalizationOrderEquiv.toMonoidHom
      N13GaussianNamedUnitTransport.orderToSextic.toMonoidHom
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
@[simp] theorem unitsMap_normalizationOrderToSextic_apply
    (ε : Oiˣ) :
    Units.map normalizationOrderToSextic.toMonoidHom ε =
      N13GaussianNamedUnitTransport.orderUnitsToSextic
        (Units.map normalizationOrderEquiv.toMonoidHom ε) := by
  rw [unitsMap_normalizationOrderToSextic_eq]
  rfl
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
/-- Package a nonzero normalization-order element as a sextic-field unit. -/
def unitOfNonzero (x : Oi) (hx : x ≠ 0) : Lsˣ :=
  Units.mk0 (normalizationOrderToSextic x)
    (by
      intro hzero
      apply hx
      apply normalizationOrderToSextic_injective
      simpa using hzero)
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizationOrderTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs
/-- An exact unit-times-square identity in the normalization order transports
to an exact unit-times-square identity in the sextic field. -/
theorem exists_transportedUnit_mul_sq
    (x : Oi) (hx : x ≠ 0)
    (ε : Oiˣ) (y : Oi)
    (h : x = (ε : Oi) * y ^ 2) :
    ∃ s : Lsˣ,
      unitOfNonzero x hx =
        N13GaussianNamedUnitTransport.orderUnitsToSextic
            (Units.map normalizationOrderEquiv.toMonoidHom ε) *
          s ^ 2 := by
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    rw [h, hy0]
    simp
  refine ⟨unitOfNonzero y hy, ?_⟩
  apply Units.ext
  change
    normalizationOrderToSextic x =
      (N13GaussianNamedUnitTransport.orderUnitsToSextic
          (Units.map normalizationOrderEquiv.toMonoidHom ε) : Ls) *
        normalizationOrderToSextic y ^ 2
  rw [← unitsMap_normalizationOrderToSextic_apply]
  change
    normalizationOrderToSextic x =
      normalizationOrderToSextic (ε : Oi) *
        normalizationOrderToSextic y ^ 2
  simpa only [map_mul, map_pow] using
    congrArg normalizationOrderToSextic h
end
end MazurProof.N13GaussianNormalizationOrderTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizedSquareclassSeam
noncomputable section
open N13GaussianNormalizationOrderTransport
/-- The normalized integral representative, transported to the sextic field
and packaged as a unit. -/
def normalizedIntegralUnit (D : LowRep) : Lsˣ :=
  unitOfNonzero
    (N13GlobalKummerNormalization.normalizedKummerInteger D)
    (N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D)
end
end MazurProof.N13GaussianNormalizedSquareclassSeam
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizedSquareclassSeam
noncomputable section
open N13GaussianNormalizationOrderTransport
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GaussianNormalizationOrderTransport.fieldLs MazurProof.N13GlobalKummerNormalization.fieldL MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The normalized integral unit is the actual Mumford Kummer unit times one
rational scalar unit. -/
theorem exists_normalizedIntegralUnit_eq_uThetaUnit_mul_scalar
    (D : LowRep) :
    ∃ q : ℚˣ,
      normalizedIntegralUnit D =
        N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) *
          FakeSquareClass.scalarUnitsMap
            (algebraMap ℚ Ls) q := by
  obtain ⟨c, hc, hspec⟩ :=
    N13GlobalKummerNormalization.normalizedKummerInteger_spec D
  let q : ℚˣ := Units.mk0 c hc
  have hscalar :
      N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (algebraMap ℚ N13GaussianCubicField.L c) =
        algebraMap ℚ Ls c := by
    let φ : ℚ →+* Ls :=
      N13GaussianFieldEquiv.sexticEquivGaussian.symm.toRingEquiv.toRingHom.comp
        (algebraMap ℚ N13GaussianCubicField.L)
    have hφ : φ = algebraMap ℚ Ls :=
      RingHom.ext_rat _ _
    exact DFunLike.congr_fun hφ c
  have hvalue :
      normalizationOrderToSextic
          (N13GlobalKummerNormalization.normalizedKummerInteger D) =
        algebraMap ℚ Ls c *
          N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D) := by
    calc
      normalizationOrderToSextic
          (N13GlobalKummerNormalization.normalizedKummerInteger D) =
          N13GaussianFieldEquiv.sexticEquivGaussian.symm
            ((N13GlobalKummerNormalization.normalizedKummerInteger D :
              N13GlobalKummerIdealSquare.O) :
              N13GaussianCubicField.L) :=
        normalizationOrderToSextic_apply _
      _ =
          N13GaussianFieldEquiv.sexticEquivGaussian.symm
            (algebraMap ℚ N13GaussianCubicField.L c *
              N13GaussianFieldEquiv.sexticEquivGaussian
                (N13MumfordKummerValue.uTheta
                  (N13LowDegreeKummerHom.asMumford D))) := by
        rw [hspec]
      _ =
          N13GaussianFieldEquiv.sexticEquivGaussian.symm
              (algebraMap ℚ N13GaussianCubicField.L c) *
            N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D) := by
        rw [map_mul,
          N13GaussianFieldEquiv.sexticEquivGaussian.symm_apply_apply]
      _ =
          algebraMap ℚ Ls c *
            N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D) := by
        rw [hscalar]
  refine ⟨q, ?_⟩
  apply Units.ext
  change
    normalizationOrderToSextic
        (N13GlobalKummerNormalization.normalizedKummerInteger D) =
      N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) *
        algebraMap ℚ Ls c
  simpa [mul_comm] using hvalue
end
end MazurProof.N13GaussianNormalizedSquareclassSeam
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNormalizedSquareclassSeam
noncomputable section
open N13GaussianNormalizationOrderTransport
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Rational normalization does not alter the fake squareclass. -/
theorem normalizedIntegralUnit_fakeClass_eq_uThetaUnit
    (D : LowRep) :
    ((normalizedIntegralUnit D : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) =
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) := by
  obtain ⟨q, hq⟩ :=
    exists_normalizedIntegralUnit_eq_uThetaUnit_mul_scalar D
  rw [hq]
  change
    ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) *
        ((FakeSquareClass.scalarUnitsMap
            (algebraMap ℚ Ls) q : Lsˣ) :
          FakeSquareClass.Target (algebraMap ℚ Ls)) =
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls))
  rw [FakeSquareClass.scalar_eq_one, mul_one]
end
end MazurProof.N13GaussianNormalizedSquareclassSeam
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FakeDescentAssembly
noncomputable section
open N13SexticSquareclass
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The additive version of the four-generator fake square class. -/
def candidateValue (i j k s : ZMod 2) : Target :=
  Additive.ofMul (N13CandidateCollapse.candidateClass i j k s)
end
end MazurProof.N13FakeDescentAssembly
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FakeDescentAssembly
noncomputable section
open N13SexticSquareclass
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The actual global-to-local semantic package.  The exponents may depend on
the Jacobian class; no finite list of Jacobian generators is assumed. -/
structure CandidateLocalization (kummer : G →+ Target) : Prop where
  exists_candidate :
    ∀ P : G, ∃ i j k s : ZMod 2,
      kummer P = candidateValue i j k s ∧
      N13LocalDlogTwo.candidateDlog i j k s = 0
end
end MazurProof.N13FakeDescentAssembly
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FakeDescentAssembly
noncomputable section
open N13SexticSquareclass
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Structural candidate collapse in the additive fake-Kummer target. -/
theorem candidateValue_eq_zero_of_dlog_eq_zero
    (i j k s : ZMod 2)
    (hlocal : N13LocalDlogTwo.candidateDlog i j k s = 0) :
    candidateValue i j k s = 0 := by
  change
    Additive.ofMul
        (N13CandidateCollapse.candidateClass i j k s) =
      Additive.ofMul 1
  exact congrArg Additive.ofMul
    (N13CandidateCollapse.candidateClass_eq_one_of_dlog_eq_zero
      i j k s hlocal)
end
end MazurProof.N13FakeDescentAssembly
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FakeDescentAssembly
noncomputable section
open N13SexticSquareclass
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The two semantic bridges and the structural candidate calculation make
the genuine fake-Kummer map trivial. -/
theorem kummer_trivial_of_candidateLocalization
    (kummer : G →+ Target)
    (H : CandidateLocalization kummer) :
    ∀ P : G, kummer P = 0 := by
  intro P
  obtain ⟨i, j, k, s, hP, hlocal⟩ :=
    H.exists_candidate P
  rw [hP]
  exact candidateValue_eq_zero_of_dlog_eq_zero i j k s hlocal
end
end MazurProof.N13FakeDescentAssembly
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FakeDescentAssembly
noncomputable section
open N13SexticSquareclass
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Candidate localization makes the now-unconditional N13 Kummer map
trivial. -/
theorem actualKummer_trivial_of_candidateLocalization
    (H : CandidateLocalization actualKummer) :
    ∀ P : G, actualKummer P = 0 :=
  kummer_trivial_of_candidateLocalization actualKummer H
end
end MazurProof.N13FakeDescentAssembly
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- The unit in the factorization `x = ε y²` has zero first ramified
logarithm.  The proof is an identity of group homomorphisms: the primitive
left side has constant first jet and the square on the right contributes
twice its logarithm. -/
theorem factorizationUnit_dlog_eq_zero
    (D : LowRep)
    (ε : Oiˣ) (y : Oi)
    (hxy :
      N13GlobalKummerNormalization.normalizedKummerInteger D =
        (ε : Oi) * y ^ 2) :
    N13GaussianNamedUnitSquareclasses.globalDlogAdd
        (Additive.ofMul
          (Units.map
            N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
            ε)) = 0 := by
  exact HuangN13.N13GaussianGlobalZeroCarrierDlog.factorizationUnit_dlog_eq_zero D ε y hxy
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg MazurProof.N13GaussianNormalizationOrderTransport.fieldLs MazurProof.N13GaussianGlobalZeroCarrierDlog.fieldLg
theorem exists_normalizedCandidate_dlog_zero
    (D : LowRep) :
    ∃ i j k : ZMod 2,
      ((N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit D :
          N13SexticSquareclass.SexticAlgebraˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
          N13CandidateCollapse.candidateClass i j k 0 ∧
        N13LocalDlogTwo.candidateDlog i j k 0 = 0 := by
  let x :=
    N13GlobalKummerNormalization.normalizedKummerInteger D
  have hx : x ≠ 0 :=
    N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D
  obtain ⟨ε, y, hxy⟩ :=
    N13GaussianDifferentSupport.normalizedKummerInteger_eq_unit_mul_sq D
  let εn : Onˣ :=
    Units.map
      N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
      ε
  obtain ⟨i, j, k, η, hε⟩ :=
    N13GaussianNamedUnitSquareclasses.unit_modSq_decompose_named εn
  have hεzero :
      N13GaussianNamedUnitSquareclasses.globalDlogAdd
          (Additive.ofMul εn) = 0 := by
    exact factorizationUnit_dlog_eq_zero D ε y hxy
  have hnamedZero :
      N13GaussianNamedUnitSquareclasses.globalDlogAdd
          (Additive.ofMul
            (N13GaussianNamedUnitSquareclasses.namedWord
              (i, j, k))) = 0 := by
    rw [hε] at hεzero
    simpa only [N13GaussianNamedUnitSquareclasses.namedWord,
      ofMul_mul, map_add,
      N13GaussianNamedUnitSquareclasses.globalDlogAdd_sq,
      add_zero] using hεzero
  have hdlog :
      N13LocalDlogTwo.candidateDlog i j k 0 = 0 := by
    rw [N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord] at hnamedZero
    simpa only [N13LocalDlogTwo.candidateDlog, map_zero,
      add_zero] using hnamedZero
  obtain ⟨s, hs⟩ :=
    N13GaussianNormalizationOrderTransport.exists_transportedUnit_mul_sq
      x hx ε y hxy
  have hεSextic :
      N13GaussianNamedUnitTransport.orderUnitsToSextic εn =
        N13CandidateCollapse.zetaUnit ^ i.val *
          N13CandidateCollapse.e1Unit ^ j.val *
          N13CandidateCollapse.e2Unit ^ k.val *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η) ^ 2 := by
    simpa only [map_mul, map_pow,
      N13GaussianNamedUnitTransport.orderUnitsToSextic_zeta,
      N13GaussianNamedUnitTransport.orderUnitsToSextic_e1,
      N13GaussianNamedUnitTransport.orderUnitsToSextic_e2] using
      congrArg
        N13GaussianNamedUnitTransport.orderUnitsToSextic hε
  have hunit :
      N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit D =
        N13CandidateCollapse.candidateUnit i j k 0 *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η * s) ^ 2 := by
    change
      N13GaussianNormalizationOrderTransport.unitOfNonzero x hx =
        N13CandidateCollapse.candidateUnit i j k 0 *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η * s) ^ 2
    rw [hs, hεSextic]
    simp only [N13CandidateCollapse.candidateUnit,
      ZMod.val_zero, pow_zero, mul_one, mul_pow]
    simp only [mul_comm]
    exact mul_left_comm _ _ _
  refine ⟨i, j, k, ?_, hdlog⟩
  rw [hunit]
  change
    ((N13CandidateCollapse.candidateUnit i j k 0 *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η * s) ^ 2 :
        N13SexticSquareclass.SexticAlgebraˣ) :
      FakeSquareClass.Target
        (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
      ((N13CandidateCollapse.candidateUnit i j k 0 :
          N13SexticSquareclass.SexticAlgebraˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13SexticSquareclass.SexticAlgebra))
  simp
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The same aligned coordinates represent the actual Mumford value; the
rational scalar separating it from the globally primitive value disappears
only after the local logarithm has already been proved from the integral
factorization. -/
theorem exists_actualCandidate_dlog_zero
    (D : LowRep) :
    ∃ i j k : ZMod 2,
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) :
          N13SexticSquareclass.SexticAlgebraˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
          N13CandidateCollapse.candidateClass i j k 0 ∧
        N13LocalDlogTwo.candidateDlog i j k 0 = 0 := by
  obtain ⟨i, j, k, hclass, hdlog⟩ :=
    exists_normalizedCandidate_dlog_zero D
  exact
    ⟨i, j, k,
      (N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit_fakeClass_eq_uThetaUnit
        D).symm.trans
          hclass,
      hdlog⟩
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The actual structural Kummer homomorphism admits aligned zero-carrier
coordinates with vanishing first logarithm for every rational class. -/
def actualCandidateLocalization :
    N13FakeDescentAssembly.CandidateLocalization
      N13FakeDescentAssembly.actualKummer where
  exists_candidate P := by
    let D : LowRep :=
      N13LowDegreeKummerHom.representative P
    obtain ⟨i, j, k, hclass, hdlog⟩ :=
      exists_actualCandidate_dlog_zero D
    refine ⟨i, j, k, 0, ?_, hdlog⟩
    change
      Additive.ofMul
          (((N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) :
              N13SexticSquareclass.SexticAlgebraˣ)) :
            FakeSquareClass.Target
              (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
        Additive.ofMul
          (N13CandidateCollapse.candidateClass i j k 0)
    exact congrArg Additive.ofMul hclass
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The genuine N13 fake-Kummer homomorphism is unconditionally trivial. -/
theorem actualKummer_trivial :
    ∀ P : N13FakeDescentAssembly.G,
      N13FakeDescentAssembly.actualKummer P = 0 :=
  N13FakeDescentAssembly.actualKummer_trivial_of_candidateLocalization
    actualCandidateLocalization
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
theorem solution :
    ∀ P : MazurProof.N13FakeDescentAssembly.G,
      MazurProof.N13FakeDescentAssembly.actualKummer P = 0 := by
  exact MazurProof.N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial
