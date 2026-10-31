-- Prove2me | solution 1 for MazurProof.N13GaussianDifferentSupport.normalizedKummerInteger_eq_unit_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T06:42:04.03549+00:00
-- url     : https://prove2.me/submissions/185eddb2-652e-4fb3-aa31-a39d34719ec3

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_HuangN13_N13GaussianDifferentSupport_coe_algebraNorm_int
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianDifferentSupport_relativeGaussianTwoIdeal_isPrime
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianI_sq
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_gaussian_cubic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_root_sextic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_sexticToGaussian_bijective
import Theorems.Thm_MazurProof_N13GlobalKummerIdealSquare_exists_scaledIntegralMumford
import Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_localF_derivative_isUnit
import Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_localU_coeff_two_isUnit_of_mem_nonsimple
import Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_normalizedKummerInteger_multiplicity_even_of_simpleRoot
import Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_normalizedKummerInteger_ne_zero
import Theorems.Thm_MazurProof_N13QuadraticAlgebraDoubleRoot_multiplicity_even_of_completion_quadratic_doubleRoot

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
/-- The power basis on the generated Gaussian order, transported to the
proved relative integral closure. -/
def relativeIntegralPowerBasis :
    PowerBasis GI (integralClosure GI L) :=
  (Algebra.adjoin.powerBasis' (R := GI) alpha_integral).map
    (Subalgebra.equivOfEq _ _
      integralClosure_eq_adjoin.symm)
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
@[simp] theorem relativeIntegralPowerBasis_dim :
    relativeIntegralPowerBasis.dim = 3 := by
  simp [relativeIntegralPowerBasis, minpoly_alpha,
    h_natDegree]
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
@[simp] theorem coe_relativeIntegralPowerBasis_gen :
    ((relativeIntegralPowerBasis.gen :
        integralClosure GI L) : L) = alpha := by
  simp [relativeIntegralPowerBasis]
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL
/-- The literal relative integral basis `(1, α, α²)`. -/
def relativeIntegralBasis :
    Basis (Fin 3) GI (integralClosure GI L) :=
  relativeIntegralPowerBasis.basis.reindex
    (finCongr relativeIntegralPowerBasis_dim)
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL
@[simp] theorem coe_relativeIntegralBasis_apply
    (j : Fin 3) :
    ((relativeIntegralBasis j :
        integralClosure GI L) : L) =
      alpha ^ (j : ℕ) := by
  rw [relativeIntegralBasis, Basis.reindex_apply,
    relativeIntegralPowerBasis.basis_eq_pow]
  have hindex :
      (((finCongr relativeIntegralPowerBasis_dim).symm j) :
        ℕ) = (j : ℕ) := rfl
  change
    ((relativeIntegralPowerBasis.gen :
      integralClosure GI L) : L) ^
        (((finCongr relativeIntegralPowerBasis_dim).symm j) :
          ℕ) =
      alpha ^ (j : ℕ)
  rw [coe_relativeIntegralPowerBasis_gen]
  rw [hindex]
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianCubicField.integralClosureLocalization
/-- Localizing the relative integral basis gives the literal relative field
basis. -/
def localizedRelativeIntegralBasis :
    Basis (Fin 3) K L :=
  Basis.localizationLocalization
    K (nonZeroDivisors GI) L relativeIntegralBasis
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianCubicField.integralClosureLocalization
theorem localizedRelativeIntegralBasis_eq :
    localizedRelativeIntegralBasis = relativeFieldBasis := by
  ext j
  simp [localizedRelativeIntegralBasis]
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianCubicField.integralClosureLocalization
/-- The relative integral basis has discriminant `π²`. -/
theorem relativeIntegralBasis_discr :
    Algebra.discr GI relativeIntegralBasis = pi ^ 2 := by
  apply IsFractionRing.injective GI K
  calc
    algebraMap GI K
        (Algebra.discr GI relativeIntegralBasis) =
        Algebra.discr K localizedRelativeIntegralBasis :=
      (Algebra.discr_localizationLocalization
        GI (nonZeroDivisors GI) L
        relativeIntegralBasis).symm
    _ = Algebra.discr K relativeFieldBasis := by
      rw [localizedRelativeIntegralBasis_eq]
    _ = algebraMap GI K (pi ^ 2) :=
      relativeFieldBasis_discr
end
end MazurProof.N13GaussianCubicField
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
namespace MazurProof.N13GaussianFractionField
noncomputable section
open N13GaussianGlobalArithmetic
theorem finrank_K :
    Module.finrank ℚ K = 2 := by
  rw [Module.finrank_eq_card_basis gaussianBasis]
  simp
end
end MazurProof.N13GaussianFractionField
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
namespace MazurProof.N13GaussianFractionField
noncomputable section
open N13GaussianGlobalArithmetic
/-- Localization identifies the field norm on `K/ℚ` with the same Gaussian
norm. -/
theorem fieldNorm_algebraMap (z : GI) :
    Algebra.norm ℚ (algebraMap GI K z) =
      algebraMap ℤ ℚ (Zsqrtd.norm z) := by
  rw [Algebra.norm_localization
    ℤ (nonZeroDivisors ℤ) z,
    algebraNorm_eq_gaussianNorm]
end
end MazurProof.N13GaussianFractionField
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
namespace MazurProof.N13GaussianFractionField
noncomputable section
open N13GaussianGlobalArithmetic
@[simp] theorem fieldNorm_pi :
    Algebra.norm ℚ (algebraMap GI K pi) = 13 := by
  rw [fieldNorm_algebraMap, pi_norm]
  norm_num
end
end MazurProof.N13GaussianFractionField
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.finiteKL
theorem finrank_Lg :
    Module.finrank ℚ Lg = 6 := by
  calc
    Module.finrank ℚ Lg =
        Module.finrank ℚ K * Module.finrank K Lg :=
      (Module.finrank_mul_finrank ℚ K Lg).symm
    _ = 2 * 3 := by
      rw [N13GaussianFractionField.finrank_K]
      congr 1
      rw [Module.finrank_eq_card_basis
        N13GaussianCubicField.powerBasis.basis]
      simp [N13GaussianCubicField.powerBasis_dim]
    _ = 6 := by norm_num
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
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GlobalKummerNormalization.fieldL
/-- The integral representative retains the square-norm condition; its
square root is simply rescaled by the cube of the rational normalization
factor. -/
theorem normalizedKummerInteger_norm_isSquare
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ s : ℚ,
      Algebra.norm ℚ
          (((normalizedKummerInteger D :
              integralClosure ℤ L) : L)) =
        s ^ 2 := by
  obtain ⟨c, hc, hspec⟩ :=
    normalizedKummerInteger_spec D
  refine
    ⟨c ^ 3 * N13MumfordKummerNorm.normRoot D, ?_⟩
  have hnorm :
      Algebra.norm ℚ
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) =
        N13MumfordKummerNorm.normRoot D ^ 2 :=
    N13MumfordKummerNorm.norm_uTheta_eq_normRoot_sq D
  have hnormGaussian :
      Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) =
        N13MumfordKummerNorm.normRoot D ^ 2 := by
    calc
      Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) =
          Algebra.norm ℚ
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) :=
        Algebra.norm_eq_of_algEquiv
          N13GaussianFieldEquiv.sexticEquivGaussian _
      _ = _ := hnorm
  rw [hspec, map_mul, Algebra.norm_algebraMap,
    N13GaussianFieldEquiv.finrank_Lg,
    hnormGaussian]
  ring
end
end MazurProof.N13GlobalKummerNormalization
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerIdealSquare
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
/-- A fixed structural choice of the homogeneous integral Mumford data. -/
def scaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) :
    ScaledIntegralMumford D :=
  Classical.choice (exists_scaledIntegralMumford D)
end
end MazurProof.N13GlobalKummerIdealSquare
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerIdealSquare
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
/-- The homogeneously scaled integral curve polynomial. -/
def scaledCurve
    (D : N13LowDegreeKummerHom.LowRep) : ℤ[X] :=
  C ((scaledIntegralMumford D).scale ^ 2) *
    N13SexticIrreducible.fInt
end
end MazurProof.N13GlobalKummerIdealSquare
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerIdealSquare
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
theorem scaledCurve_relation
    (D : N13LowDegreeKummerHom.LowRep) :
    scaledCurve D -
        (scaledIntegralMumford D).v ^ 2 =
      primitiveNormalization D.toSemi.u *
        (scaledIntegralMumford D).w :=
  (scaledIntegralMumford D).curve
end
end MazurProof.N13GlobalKummerIdealSquare
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerIdealSquare
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
attribute [local instance] MazurProof.N13GlobalKummerNormalization.fieldL MazurProof.N13GlobalKummerIdealSquare.fieldL
/-- The integral branch point is a root of the original sextic. -/
@[simp] theorem integralTheta_root_fInt :
    aeval integralTheta N13SexticIrreducible.fInt = 0 := by
  change
    integralEval N13SexticIrreducible.fInt = 0
  apply Subtype.ext
  have hrat :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.map
          (algebraMap ℤ ℚ)) = 0 := by
    rw [N13SexticIrreducible.fInt_map_rat]
    exact gaussianTheta_root_sextic
  rw [coe_integralEval]
  change
    eval₂ (algebraMap ℤ L) gaussianTheta
      N13SexticIrreducible.fInt = (0 : L)
  simpa only [eval₂_map,
      IsScalarTower.algebraMap_eq ℤ ℚ L] using hrat
end
end MazurProof.N13GlobalKummerIdealSquare
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring
namespace MazurProof.N13GoodPrimeSimpleRoot
noncomputable section
@[simp] theorem quadratic_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).eval x =
      a * x ^ 2 + b * x + c := by
  simp [quadratic]
end
end MazurProof.N13GoodPrimeSimpleRoot
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring
namespace MazurProof.N13GoodPrimeSimpleRoot
noncomputable section
@[simp] theorem quadratic_derivative_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).derivative.eval x =
      2 * a * x + b := by
  simp [quadratic]
  ring
end
end MazurProof.N13GoodPrimeSimpleRoot
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring
namespace MazurProof.N13GoodPrimeSimpleRoot
noncomputable section
/-- Every polynomial of degree at most two is recovered from its first
three coefficients. -/
theorem eq_quadratic_of_natDegree_le_two
    {R : Type*} [CommRing R]
    (p : R[X]) (hdeg : p.natDegree ≤ 2) :
    p = quadratic (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [quadratic]
  by_cases hn1 : n = 1
  · subst n
    simp [quadratic]
  by_cases hn2 : n = 2
  · subst n
    simp [quadratic]
  have hn : 2 < n := by omega
  have hpzero :
      p.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (hdeg.trans_lt hn)
  rw [hpzero]
  simp [quadratic, coeff_C, coeff_X, coeff_X_pow,
    hn0, hn2, Ne.symm hn1]
end
end MazurProof.N13GoodPrimeSimpleRoot
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL
@[simp] theorem finrank_K_L :
    Module.finrank K L = 3 := by
  rw [Module.finrank_eq_card_basis relativeBasis]
  simp
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianNumberField.intAlgebraL
/-- The absolute integral basis obtained by composing the Gaussian integral
basis with the relative cubic integral basis. -/
def absoluteIntegralBasis :
    Basis (Fin 2 × Fin 3) ℤ (integralClosure ℤ L) :=
  (N13GaussianFractionField.gaussianIntBasis.smulTower
      N13GaussianCubicField.relativeIntegralBasis).map
    relativeToAbsoluteLinearEquiv
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianNumberField.intAlgebraAbsoluteIntegers MazurProof.N13GaussianNumberField.intAlgebraL
/-- The explicit integral basis, transported to Mathlib's performance-oriented
`RingOfIntegers` wrapper. -/
def absoluteRingOfIntegersBasis :
    Basis (Fin 2 × Fin 3) ℤ
      (NumberField.RingOfIntegers L) :=
  absoluteIntegralBasis.map
    integralClosureToRingOfIntegersAlgEquiv.toAddEquiv.toIntLinearEquiv
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianNumberField.intAlgebraGI MazurProof.N13GaussianNumberField.intAlgebraRelativeIntegers
/-- The tower basis before changing the integral-closure subtype has the
absolute discriminant `-10816`. -/
theorem relativeTowerBasis_discr :
    Algebra.discr ℤ
      (N13GaussianFractionField.gaussianIntBasis.smulTower
        N13GaussianCubicField.relativeIntegralBasis) =
      -10816 := by
  rw [TowerDiscriminant.discr_smulTower,
    N13GaussianFractionField.discr_gaussianIntBasis,
    N13GaussianCubicField.relativeIntegralBasis_discr]
  simp only [Fintype.card_fin,
    N13GaussianFractionField.algebraNorm_pi_sq]
  norm_num
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianNumberField.intAlgebraAbsoluteIntegers MazurProof.N13GaussianNumberField.intAlgebraL MazurProof.N13GaussianNumberField.intAlgebraRelativeIntegers
/-- Discriminant of the explicit absolute integral basis. -/
@[simp] theorem absoluteIntegralBasis_discr :
    Algebra.discr ℤ absoluteIntegralBasis = -10816 := by
  calc
    Algebra.discr ℤ absoluteIntegralBasis =
        Algebra.discr ℤ
          (N13GaussianFractionField.gaussianIntBasis.smulTower
            N13GaussianCubicField.relativeIntegralBasis) := by
      symm
      have hfun :
          (relativeToAbsoluteAlgEquiv ∘
              (N13GaussianFractionField.gaussianIntBasis.smulTower
                N13GaussianCubicField.relativeIntegralBasis :
                Fin 2 × Fin 3 →
                  integralClosure GI L)) =
            (absoluteIntegralBasis :
              Fin 2 × Fin 3 → integralClosure ℤ L) := by
        funext ij
        rfl
      have hdisc :=
        Algebra.discr_eq_discr_of_algEquiv
          (N13GaussianFractionField.gaussianIntBasis.smulTower
            N13GaussianCubicField.relativeIntegralBasis)
          relativeToAbsoluteAlgEquiv
      rw [hfun] at hdisc
      exact hdisc
    _ = -10816 := relativeTowerBasis_discr
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianNumberField.intAlgebraAbsoluteIntegers MazurProof.N13GaussianNumberField.intAlgebraL
/-- Discriminant of the same basis in Mathlib's `RingOfIntegers` wrapper. -/
@[simp] theorem absoluteRingOfIntegersBasis_discr :
    Algebra.discr ℤ absoluteRingOfIntegersBasis = -10816 := by
  calc
    Algebra.discr ℤ absoluteRingOfIntegersBasis =
        Algebra.discr ℤ absoluteIntegralBasis := by
      symm
      have hfun :
          (integralClosureToRingOfIntegersAlgEquiv ∘
              (absoluteIntegralBasis :
                Fin 2 × Fin 3 → integralClosure ℤ L)) =
            (absoluteRingOfIntegersBasis :
              Fin 2 × Fin 3 →
                NumberField.RingOfIntegers L) := by
        funext ij
        rfl
      have hdisc :=
        Algebra.discr_eq_discr_of_algEquiv
          absoluteIntegralBasis
          integralClosureToRingOfIntegersAlgEquiv
      rw [hfun] at hdisc
      exact hdisc
    _ = -10816 := absoluteIntegralBasis_discr
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL
/-- The absolute number-field discriminant. -/
@[simp] theorem numberField_discr :
    NumberField.discr L = -10816 := by
  have hcanonical :=
    NumberField.discr_eq_discr L
      absoluteRingOfIntegersBasis
  rw [← hcanonical]
  exact absoluteRingOfIntegersBasis_discr
end
end MazurProof.N13GaussianNumberField
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
def localV
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P (scaledIntegralMumford D).v
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
def localW
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P (scaledIntegralMumford D).w
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
def localScale
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    LocalIntegers P :=
  algebraMap ℤ (LocalIntegers P)
    (scaledIntegralMumford D).scale
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
/-- Evaluation at the local branch point commutes with the map from the
global ring of integers. -/
theorem localPolynomial_eval_localTheta
    (P : HeightOneSpectrum O) (p : ℤ[X]) :
    (localPolynomial P p).eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (integralEval p) := by
  rw [localPolynomial, Polynomial.eval_map]
  change
    eval₂ (algebraMap ℤ (LocalIntegers P))
        (algebraMap O (LocalIntegers P) integralTheta) p =
      algebraMap O (LocalIntegers P)
        (eval₂ (algebraMap ℤ O) integralTheta p)
  have h :=
    (Polynomial.hom_eval₂ p
      (algebraMap ℤ O)
      (algebraMap O (LocalIntegers P))
      integralTheta).symm
  have hmaps :
      (algebraMap O (LocalIntegers P)).comp
          (algebraMap ℤ O) =
        algebraMap ℤ (LocalIntegers P) :=
    RingHom.ext_int _ _
  rw [← hmaps]
  exact h
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
theorem localU_eval_localTheta
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (normalizedKummerInteger D) := by
  exact localPolynomial_eval_localTheta P _
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
theorem localF_eval_localTheta
    (P : HeightOneSpectrum O) :
    (localF P).eval (localTheta P) = 0 := by
  rw [localF, localPolynomial_eval_localTheta]
  have hzero :
      integralEval N13SexticIrreducible.fInt = 0 :=
    integralTheta_root_fInt
  rw [hzero, map_zero]
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
/-- The completion ideal lies over the original height-one prime. -/
theorem algebraMap_mem_completionIdeal_iff
    (P : HeightOneSpectrum O) (x : O) :
    algebraMap O (LocalIntegers P) x ∈
        P.completionIdeal L ↔
      x ∈ P.asIdeal := by
  change
    x ∈ Ideal.comap
        (algebraMap O (LocalIntegers P))
        (P.completionIdeal L) ↔
      x ∈ P.asIdeal
  have hover :
      Ideal.comap
          (algebraMap O (LocalIntegers P))
          (P.completionIdeal L) =
        P.asIdeal :=
    by
      simpa only [Ideal.under_def] using
        (inferInstance :
          (P.completionIdeal L).LiesOver P.asIdeal).over.symm
  rw [hover]
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
theorem localU_natDegree_le
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans
    (normalizedKummerInteger_degree D)
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
/-- The mapped homogeneous Mumford relation. -/
theorem local_relation
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    C (localScale D P ^ 2) * localF P -
        localV D P ^ 2 =
      localU D P * localW D P := by
  have h :=
    congrArg
      (Polynomial.map
        (algebraMap ℤ (LocalIntegers P)))
      (scaledCurve_relation D)
  simpa [scaledCurve, localScale, localF, localV,
    localU, localW, localPolynomial,
    Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C,
    map_pow] using h
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroCompletion MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
theorem localScale_ne_zero
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    localScale D P ≠ 0 := by
  unfold localScale
  intro hzero
  apply (scaledIntegralMumford D).scale_ne_zero
  have hzero' :=
    congrArg
      (fun z : LocalIntegers P =>
        (z : P.adicCompletion L))
      hzero
  have hmaps :
      (algebraMap
          (LocalIntegers P)
          (P.adicCompletion L)).comp
          (algebraMap ℤ (LocalIntegers P)) =
        algebraMap ℤ (P.adicCompletion L) :=
    RingHom.ext_int _ _
  change
    ((algebraMap
        (LocalIntegers P)
        (P.adicCompletion L)).comp
      (algebraMap ℤ (LocalIntegers P)))
        (scaledIntegralMumford D).scale =
      0 at hzero'
  rw [hmaps] at hzero'
  apply
    (algebraMap ℤ
      (P.adicCompletion L)).injective_int
  simpa only [map_zero] using hzero'
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
/-- For a nonzero integral generator, the fractional-ideal count is the
ordinary height-one multiplicity of its principal ideal. -/
theorem count_spanSingleton_eq_int_multiplicity
    (P : HeightOneSpectrum O)
    {x : O} (hx : x ≠ 0) :
    FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          ((x : O) : L)) =
      (multiplicity P.asIdeal
        (Ideal.span ({x} : Set O)) : ℤ) := by
  have hspan :
      Ideal.span ({x} : Set O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hx
  change
    FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          (algebraMap O L x)) =
      (multiplicity P.asIdeal
        (Ideal.span ({x} : Set O)) : ℤ)
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  rw [FractionalIdeal.count_coe L P hspan]
  norm_cast
  rw [Ideal.count_associates_factors_eq
      hspan P.isPrime P.ne_bot,
    P.count_normalizedFactors_eq_multiplicity hspan]
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerAwayDifferentParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
open N13GlobalKummerSimpleRootParity
open N13QuadraticAlgebraDoubleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL MazurProof.N13GlobalKummerAwayDifferentParity.dedekindO MazurProof.N13GlobalKummerAwayDifferentParity.fieldL MazurProof.N13GlobalKummerAwayDifferentParity.fractionRingOL
/-- The double-root branch has even multiplicity at every prime away from
the different. -/
theorem normalizedKummerInteger_multiplicity_even_of_doubleRoot
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hmem :
      normalizedKummerInteger D ∈ P.asIdeal)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal)
    (hnonsimple :
      ¬ IsUnit
        ((localU D P).derivative.eval
          (localTheta P))) :
    Even
      (multiplicity P.asIdeal
        (Ideal.span
          {normalizedKummerInteger D})) := by
  let a := (localU D P).coeff 2
  let b := (localU D P).coeff 1
  let c := (localU D P).coeff 0
  have hU :
      localU D P = quadratic a b c := by
    simpa only [a, b, c] using
      eq_quadratic_of_natDegree_le_two
        (localU D P)
        (localU_natDegree_le D P)
  have ha : IsUnit a := by
    exact
      localU_coeff_two_isUnit_of_mem_nonsimple
        D P hmem hnonsimple
  have hsmall :
      a * localTheta P ^ 2 +
          b * localTheta P + c ∈
        P.completionIdeal L := by
    rw [← quadratic_eval, ← hU,
      localU_eval_localTheta]
    exact
      (algebraMap_mem_completionIdeal_iff P _).mpr
        hmem
  have hquadNonsimple :
      ¬ IsUnit
        (2 * a * localTheta P + b) := by
    rw [← quadratic_derivative_eval, ← hU]
    exact hnonsimple
  have hglobal :
      algebraMap O (P.adicCompletion L)
          (normalizedKummerInteger D) =
        ((a * localTheta P ^ 2 +
              b * localTheta P + c :
            LocalIntegers P) :
          P.adicCompletion L) := by
    have heval :
        a * localTheta P ^ 2 +
              b * localTheta P + c =
          algebraMap O (LocalIntegers P)
            (normalizedKummerInteger D) := by
      rw [← quadratic_eval, ← hU,
        localU_eval_localTheta]
    change
      ((algebraMap O (LocalIntegers P)
          (normalizedKummerInteger D) :
        LocalIntegers P) :
          P.adicCompletion L) =
        ((a * localTheta P ^ 2 +
              b * localTheta P + c :
            LocalIntegers P) :
          P.adicCompletion L)
    exact
      congrArg
        (fun z : LocalIntegers P =>
          (z : P.adicCompletion L))
        heval.symm
  apply
    multiplicity_even_of_completion_quadratic_doubleRoot
      P
      (normalizedKummerInteger_ne_zero D)
      a b c (localTheta P) (localScale D P)
      (localF P) (localV D P) (localW D P)
      hglobal
      (localScale_ne_zero D P)
      ha hsmall hquadNonsimple
      (localF_eval_localTheta P)
      (localF_derivative_isUnit P hdifferent)
      (by
        rw [← hU]
        exact local_relation D P)
end
end MazurProof.N13GlobalKummerAwayDifferentParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerAwayDifferentParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
open N13GlobalKummerSimpleRootParity
open N13QuadraticAlgebraDoubleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL MazurProof.N13GlobalKummerAwayDifferentParity.dedekindO MazurProof.N13GlobalKummerAwayDifferentParity.fieldL
/-- At a prime away from the different, every normalized N13 Kummer
integer has even multiplicity. -/
theorem normalizedKummerInteger_multiplicity_even_of_not_mem_different
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal) :
    Even
      (multiplicity P.asIdeal
        (Ideal.span
          {normalizedKummerInteger D})) := by
  by_cases hmem :
      normalizedKummerInteger D ∈ P.asIdeal
  · by_cases hsimple :
        IsUnit
          ((localU D P).derivative.eval
            (localTheta P))
    · exact
        normalizedKummerInteger_multiplicity_even_of_simpleRoot
          D P hmem hdifferent hsimple
    · exact
        normalizedKummerInteger_multiplicity_even_of_doubleRoot
          D P hmem hdifferent hsimple
  · have hmult :
        multiplicity P.asIdeal
            (Ideal.span
              {normalizedKummerInteger D}) = 0 := by
      apply multiplicity_eq_zero.mpr
      exact
        (Ideal.dvd_span_singleton.not).mpr hmem
    rw [hmult]
    exact ⟨0, by simp⟩
end
end MazurProof.N13GlobalKummerAwayDifferentParity
end
end

section
section
set_option autoImplicit false
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerAwayDifferentParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
open N13GlobalKummerSimpleRootParity
open N13QuadraticAlgebraDoubleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL MazurProof.N13GlobalKummerAwayDifferentParity.dedekindO MazurProof.N13GlobalKummerAwayDifferentParity.fieldL MazurProof.N13GlobalKummerAwayDifferentParity.fractionRingOL
/-- Fractional-ideal count form: all support away from the different has
even exponent, independently of the denominator-clearing scale. -/
theorem normalizedKummerInteger_count_even_of_not_mem_different
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal) :
    Even
      (FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) := by
  rw [count_spanSingleton_eq_int_multiplicity
    P (normalizedKummerInteger_ne_zero D)]
  exact
    (Int.even_coe_nat _).mpr
      (normalizedKummerInteger_multiplicity_even_of_not_mem_different
        D P hdifferent)
end
end MazurProof.N13GlobalKummerAwayDifferentParity
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial Nat
open scoped nonZeroDivisors Real
namespace MazurProof.N13GaussianClassNumberOne
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianSignature.fieldL MazurProof.N13GaussianClassNumberOne.fieldL
/-- The numerical Minkowski expression for the N13 field is strictly
smaller than four. -/
private theorem minkowskiBound_lt_four :
    (4 / Real.pi) ^
          NumberField.InfinitePlace.nrComplexPlaces L *
        ((Module.finrank ℚ L)! /
            (Module.finrank ℚ L) ^
              (Module.finrank ℚ L) *
          Real.sqrt |NumberField.discr L|) < 4 := by
  have hsqrt :
      Real.sqrt (|(-10816 : ℤ)| : ℝ) = 104 := by
    norm_num
  have hpi : (4 / Real.pi : ℝ) < 4 / 3 := by
    rw [div_lt_div_iff₀ Real.pi_pos
      (by norm_num : (0 : ℝ) < 3)]
    nlinarith [Real.pi_gt_three]
  have hpi3 :
      (4 / Real.pi : ℝ) ^ 3 <
        (4 / 3 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi (by positivity) (by norm_num)
  calc
    (4 / Real.pi) ^
            NumberField.InfinitePlace.nrComplexPlaces L *
          ((Module.finrank ℚ L)! /
              (Module.finrank ℚ L) ^
                (Module.finrank ℚ L) *
            Real.sqrt |NumberField.discr L|) =
        (4 / Real.pi : ℝ) ^ 3 *
          ((((6 : ℕ)! : ℝ) / (6 : ℝ) ^ 6) * 104) := by
      rw [N13GaussianSignature.nrComplexPlaces_eq_three,
        N13GaussianNumberField.finrank_Q_L,
        N13GaussianNumberField.numberField_discr,
        hsqrt]
      norm_num
    _ = (4 / Real.pi : ℝ) ^ 3 *
          (130 / 81 : ℝ) := by
      norm_num [Nat.factorial]
    _ < (4 / 3 : ℝ) ^ 3 *
          (130 / 81 : ℝ) := by
      exact mul_lt_mul_of_pos_right hpi3 (by norm_num)
    _ < 4 := by
      norm_num
end
end MazurProof.N13GaussianClassNumberOne
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial Nat
open scoped nonZeroDivisors Real
namespace MazurProof.N13GaussianClassNumberOne
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL
/-- The N13 ring of integers is a PID.  The only possible prime norms under
the Minkowski bound are two and three, both excluded by Frobenius. -/
instance isPrincipalIdealRingO :
    IsPrincipalIdealRing O := by
  refine
    _root_.RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
      (K := L) ?_
  intro I hI hnorm
  exfalso

  have hI0 : (I : Ideal O) ≠ ⊥ := by
    simpa only [Ideal.zero_eq_bot] using
      nonZeroDivisors.coe_ne_zero I
  have hNpos : 0 < Ideal.absNorm (I : Ideal O) :=
    Ideal.absNorm_pos_of_nonZeroDivisors I
  have hNlt : Ideal.absNorm (I : Ideal O) < 4 := by
    exact_mod_cast
      (lt_of_le_of_lt hnorm minkowskiBound_lt_four)
  have hNneOne :
      Ideal.absNorm (I : Ideal O) ≠ 1 := by
    intro hN
    exact hI.ne_top
      (Ideal.absNorm_eq_one_iff.mp hN)
  have hNcases :
      Ideal.absNorm (I : Ideal O) = 2 ∨
        Ideal.absNorm (I : Ideal O) = 3 := by
    omega
  rcases hNcases with hN2 | hN3
  · exact no_prime_absNorm_eq_of_noRoot
      (q := 2) (by norm_num)
      fInt_noRoot_card_two
      (I : Ideal O) hI hI0 hN2
  · exact no_prime_absNorm_eq_of_noRoot
      (q := 3) (by norm_num)
      fInt_noRoot_card_three
      (I : Ideal O) hI hI0 hN3
end
end MazurProof.N13GaussianClassNumberOne
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
/-- Principality transports across a ring equivalence. -/
theorem isPrincipalIdealRing_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    [IsPrincipalIdealRing S]
    (e : R ≃+* S) :
    IsPrincipalIdealRing R := by
  constructor
  intro I
  let J : Ideal S := I.map e
  obtain ⟨y, hy⟩ :=
    Submodule.IsPrincipal.principal
      (J : Submodule S S)
  have hyIdeal :
      J = Ideal.span ({y} : Set S) :=
    hy
  let x : R := e.symm y
  refine ⟨x, ?_⟩
  apply e.idealComapOrderIso.symm.injective
  change
    I.map e =
      (Ideal.span ({x} : Set R)).map e
  calc
    I.map e = J := rfl
    _ = Ideal.span ({y} : Set S) := hyIdeal
    _ =
        Ideal.map e
          (Ideal.span ({x} : Set R)) := by
      rw [Ideal.map_span, Set.image_singleton]
      simp only [x, e.apply_symm_apply]
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.EvenPrincipalIdeal
/-- In a unique factorization monoid with no nontrivial units, an element
whose factorization multiplicities are all even is literally a square. -/
theorem exists_sq_eq_of_all_factorization_even
    {A : Type*}
    [CommMonoidWithZero A]
    [Nontrivial A]
    [UniqueFactorizationMonoid A]
    [NormalizationMonoid A]
    [DecidableEq A]
    [Subsingleton Aˣ]
    (a : A)
    (ha : a ≠ 0)
    (hEven : ∀ p : A, Even (factorization a p)) :
    ∃ b : A, b ^ 2 = a := by
  let f : A →₀ ℕ := factorization a
  let g : A →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 2) (by simp) f

  have hfg : f = g + g := by
    ext p
    simp only [f, g, Finsupp.add_apply, Finsupp.mapRange_apply]
    obtain ⟨k, hk⟩ := hEven p
    omega

  let s : Multiset A := Finsupp.toMultiset g
  let b : A := s.prod

  have hsPrime : ∀ p ∈ s, Prime p := by
    intro p hp
    have hpsupp : p ∈ g.support :=
      (Finsupp.mem_toMultiset g p).mp
        (by simpa [s] using hp)
    have hpg : g p ≠ 0 :=
      Finsupp.mem_support_iff.mp hpsupp
    have hpf : f p ≠ 0 := by
      intro hzero
      apply hpg
      simp [g, hzero]
    have hpnf : p ∈ normalizedFactors a := by
      rw [← Multiset.count_ne_zero]
      simpa [f, factorization_eq_count] using hpf
    exact prime_of_normalized_factor p hpnf

  have hb0 : b ≠ 0 := by
    dsimp [b]
    exact s.prod_ne_zero_of_prime hsPrime

  have hnf_b : normalizedFactors b = s := by
    dsimp [b]
    exact normalizedFactors_prod_of_prime hsPrime

  have hfac_b : factorization b = g := by
    change Multiset.toFinsupp (normalizedFactors b) = g
    rw [hnf_b]
    exact Finsupp.toMultiset_toFinsupp g

  have hfac_sq :
      factorization (b ^ 2) = factorization a := by
    rw [factorization_pow, hfac_b]
    change 2 • g = f
    simpa [two_nsmul] using hfg.symm

  have hassoc : Associated (b ^ 2) a :=
    associated_of_factorization_eq
      (b ^ 2) a (pow_ne_zero 2 hb0) ha hfac_sq

  exact ⟨b, associated_iff_eq.mp hassoc⟩
end MazurProof.EvenPrincipalIdeal
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
/-- Fractional-ideal count agrees with the factorization multiplicity of the
corresponding integral principal ideal. -/
theorem principalCount_eq_factorization_span
    (x : O) (hx : x ≠ 0)
    (P : HeightOneSpectrum O) :
    principalCount (L := L) P x =
      (factorization
        (Ideal.span ({x} : Set O)) P.asIdeal : ℤ) := by
  classical

  let I : Ideal O := Ideal.span ({x} : Set O)
  have hI : I ≠ 0 := by
    simpa [I, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using hx

  have hnat :
      (Associates.mk P.asIdeal).count
          (Associates.mk I).factors =
        factorization I P.asIdeal := by
    rw [factorization_eq_count,
      Associates.factors_mk _ hI,
      Associates.count_some
        (Associates.irreducible_mk.mpr P.irreducible),
      ← Multiset.count_map_eq_count' _ _
        Subtype.val_injective,
      Associates.map_subtype_coe_factors',
      factors_eq_normalizedFactors,
      ← Multiset.count_map_eq_count' _ _
        (Associates.mk_injective (M := Ideal O))]

  calc
    principalCount (L := L) P x =
      FractionalIdeal.count L P
        ((Ideal.span ({x} : Set O) : Ideal O) :
          FractionalIdeal O⁰ L) := by
            unfold principalCount
            rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
      ((Associates.mk P.asIdeal).count
        (Associates.mk
          (Ideal.span ({x} : Set O))).factors : ℤ) := by
          simpa [I] using
            FractionalIdeal.count_coe L P hI
    _ =
      (factorization
        (Ideal.span ({x} : Set O)) P.asIdeal : ℤ) := by
          simpa [I] using
            congrArg (fun n : ℕ => (n : ℤ)) hnat
end MazurProof.EvenPrincipalIdeal
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
variable [IsPrincipalIdealRing O]
/-- If every height-one count of a nonzero principal ideal is even, its
generator is a unit times a square in the integral ring. -/
theorem exists_unit_mul_sq_of_all_principalCounts_even
    (x : O) (hx : x ≠ 0)
    (hcount : ∀ P : HeightOneSpectrum O,
      Even (principalCount (L := L) P x)) :
    ∃ ε : Oˣ, ∃ y : O,
      x = (ε : O) * y ^ 2 := by
  classical

  let I : Ideal O := Ideal.span ({x} : Set O)
  have hI : I ≠ 0 := by
    simpa [I, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using hx

  have hfacEven :
      ∀ q : Ideal O, Even (factorization I q) := by
    intro q
    by_cases hq0 : factorization I q = 0
    · simp [hq0]
    · have hqmem : q ∈ normalizedFactors I := by
        rw [← Multiset.count_ne_zero]
        simpa [factorization_eq_count] using hq0
      have hqprime : Prime q :=
        prime_of_normalized_factor q hqmem
      let P : HeightOneSpectrum O :=
        ⟨q, Ideal.isPrime_of_prime hqprime,
          hqprime.ne_zero⟩
      have hc := hcount P
      rw [principalCount_eq_factorization_span
        x hx P] at hc
      have hcNat :
          Even
            (factorization
              (Ideal.span ({x} : Set O))
              P.asIdeal) :=
        (Int.even_coe_nat _).mp hc
      simpa [I, P] using hcNat

  obtain ⟨J, hJ_sq⟩ :=
    exists_sq_eq_of_all_factorization_even
      I hI hfacEven

  let y : O := Submodule.IsPrincipal.generator J
  have hJy :
      Ideal.span ({y} : Set O) = J :=
    Ideal.span_singleton_generator J

  have hspan :
      Ideal.span ({y ^ 2} : Set O) =
        Ideal.span ({x} : Set O) := by
    calc
      Ideal.span ({y ^ 2} : Set O) =
          (Ideal.span ({y} : Set O)) ^ 2 := by
            simp [pow_two,
              Ideal.span_singleton_mul_span_singleton]
      _ = J ^ 2 := by rw [hJy]
      _ = I := hJ_sq
      _ = Ideal.span ({x} : Set O) := rfl

  have hassoc_yx : Associated (y ^ 2) x :=
    Ideal.span_singleton_eq_span_singleton.mp hspan

  rcases hassoc_yx with ⟨ε, hε⟩
  refine ⟨ε, y, ?_⟩
  simpa [mul_comm] using hε.symm
end MazurProof.EvenPrincipalIdeal
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
variable [IsPrincipalIdealRing O]
/-- Remove an explicit integral carrier from a principal element.  If all
corrected height-one counts are even, the residual factor is a unit times a
square.  The divisibility hypothesis is essential for the square root to
remain integral. -/
theorem exists_unit_mul_correction_mul_sq
    (a x : O)
    (ha : a ≠ 0) (hx : x ≠ 0)
    (hdiv : a ∣ x)
    (hparity : ∀ P : HeightOneSpectrum O,
      Even
        (principalCount (L := L) P x -
          principalCount (L := L) P a)) :
    ∃ ε : Oˣ, ∃ y : O,
      x = (ε : O) * a * y ^ 2 := by
  obtain ⟨z, hz⟩ := hdiv
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hx
    simpa [hz0] using hz

  have hcount_z :
      ∀ P : HeightOneSpectrum O,
        Even (principalCount (L := L) P z) := by
    intro P
    have haL : algebraMap O L a ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne ha
    have hzL : algebraMap O L z ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne hz0
    have hmul :
        principalCount (L := L) P x =
          principalCount (L := L) P a +
            principalCount (L := L) P z := by
      unfold principalCount
      rw [hz, map_mul,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        FractionalIdeal.count_mul L P
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            haL)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            hzL)]
    have hp := hparity P
    rw [hmul] at hp
    simpa only [add_sub_cancel_left] using hp

  obtain ⟨ε, y, hzy⟩ :=
    exists_unit_mul_sq_of_all_principalCounts_even
      z hz0 hcount_z

  refine ⟨ε, y, ?_⟩
  rw [hz, hzy]
  ring
end MazurProof.EvenPrincipalIdeal
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
theorem factorization_heightOne_self
    (P : HeightOneSpectrum O) :
    factorization P.asIdeal P.asIdeal = 1 := by
  classical
  rw [factorization_eq_count,
    normalizedFactors_irreducible P.irreducible]
  simp
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
theorem factorization_heightOne_apply_of_ne
    (P R : HeightOneSpectrum O)
    (hRP : R ≠ P) :
    factorization P.asIdeal R.asIdeal = 0 := by
  classical
  rw [factorization_eq_count,
    normalizedFactors_irreducible P.irreducible]
  have hideal : R.asIdeal ≠ P.asIdeal := by
    intro h
    apply hRP
    exact HeightOneSpectrum.ext h
  simp [hideal]
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
theorem principalCount_mul
    {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (R : HeightOneSpectrum O) :
    principalCount (L := L) R (a * b) =
      principalCount (L := L) R a +
        principalCount (L := L) R b := by
  have haL : algebraMap O L a ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne ha
  have hbL : algebraMap O L b ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne hb
  unfold principalCount
  rw [map_mul,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul L R
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr haL)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbL)]
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
theorem principalCount_pow
    (a : O) (n : ℕ)
    (R : HeightOneSpectrum O) :
    principalCount (L := L) R (a ^ n) =
      (n : ℤ) * principalCount (L := L) R a := by
  unfold principalCount
  rw [map_pow, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_pow]
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
theorem principalCount_generator_self
    {A : O} (P : HeightOneSpectrum O)
    (hA : P.asIdeal =
      Ideal.span ({A} : Set O))
    (hA0 : A ≠ 0) :
    principalCount (L := L) P A = 1 := by
  rw [principalCount_eq_factorization_span A hA0 P,
    ← hA, factorization_heightOne_self]
  norm_num
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
theorem principalCount_generator_of_ne
    {A : O} (P R : HeightOneSpectrum O)
    (hA : P.asIdeal =
      Ideal.span ({A} : Set O))
    (hA0 : A ≠ 0)
    (hRP : R ≠ P) :
    principalCount (L := L) R A = 0 := by
  rw [principalCount_eq_factorization_span A hA0 R,
    ← hA, factorization_heightOne_apply_of_ne P R hRP]
  norm_num
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
section
set_option autoImplicit false
open scoped nonZeroDivisors
open IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace MazurProof.ExceptionalPrincipalIdeal
open EvenPrincipalIdeal
variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]
/-- If every height-one count away from two explicit principal primes is
even, only the two parity bits of those primes remain. -/
theorem exists_unit_two_carriers_mul_sq_of_even_away
    [IsPrincipalIdealRing O]
    (P Q : HeightOneSpectrum O)
    (hPQ : P ≠ Q)
    (A Qelt x : O)
    (hPgen :
      P.asIdeal = Ideal.span ({A} : Set O))
    (hQgen :
      Q.asIdeal = Ideal.span ({Qelt} : Set O))
    (hx : x ≠ 0)
    (hAway :
      ∀ R : HeightOneSpectrum O,
        R ≠ P → R ≠ Q →
          Even (principalCount (L := L) R x)) :
    ∃ r q : ZMod 2, ∃ ε : Oˣ, ∃ y : O,
      x =
        (ε : O) * A ^ r.val *
          Qelt ^ q.val * y ^ 2 := by
  classical
  let I : Ideal O :=
    Ideal.span ({x} : Set O)
  let nP : ℕ := factorization I P.asIdeal
  let nQ : ℕ := factorization I Q.asIdeal
  let rN : ℕ := nP % 2
  let qN : ℕ := nQ % 2
  have hrN_lt : rN < 2 := by
    exact Nat.mod_lt _ (by omega)
  have hqN_lt : qN < 2 := by
    exact Nat.mod_lt _ (by omega)
  have hA0 : A ≠ 0 := by
    intro hzero
    apply P.ne_bot
    rw [hPgen, hzero]
    simp
  have hQ0 : Qelt ≠ 0 := by
    intro hzero
    apply Q.ne_bot
    rw [hQgen, hzero]
    simp
  have hxP_of_rN_eq_one
      (hr : rN = 1) :
      x ∈ P.asIdeal := by
    have hnP : nP ≠ 0 := by
      intro hzero
      simp [rN, hzero] at hr
    have hPmem :
        P.asIdeal ∈ normalizedFactors I := by
      rw [← Multiset.count_ne_zero]
      simpa [nP, factorization_eq_count] using hnP
    have hPdvd :
        P.asIdeal ∣ I :=
      dvd_of_mem_normalizedFactors hPmem
    exact
      (Ideal.dvd_span_singleton.mp
        (by simpa only [I] using hPdvd))
  have hxQ_of_qN_eq_one
      (hq : qN = 1) :
      x ∈ Q.asIdeal := by
    have hnQ : nQ ≠ 0 := by
      intro hzero
      simp [qN, hzero] at hq
    have hQmem :
        Q.asIdeal ∈ normalizedFactors I := by
      rw [← Multiset.count_ne_zero]
      simpa [nQ, factorization_eq_count] using hnQ
    have hQdvd :
        Q.asIdeal ∣ I :=
      dvd_of_mem_normalizedFactors hQmem
    exact
      (Ideal.dvd_span_singleton.mp
        (by simpa only [I] using hQdvd))
  have hdiv :
      A ^ rN * Qelt ^ qN ∣ x := by
    rcases Nat.mod_two_eq_zero_or_one nP with hr | hr
    · have hrN : rN = 0 := by
        exact hr
      rcases Nat.mod_two_eq_zero_or_one nQ with hq | hq
      · have hqN : qN = 0 := by
          exact hq
        simp [hrN, hqN]
      · have hqN : qN = 1 := by
          exact hq
        have hxQ : x ∈ Q.asIdeal :=
          hxQ_of_qN_eq_one hqN
        have hQdiv : Qelt ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← hQgen]
          exact hxQ
        simpa [hrN, hqN] using hQdiv
    · have hrN : rN = 1 := by
        exact hr
      rcases Nat.mod_two_eq_zero_or_one nQ with hq | hq
      · have hqN : qN = 0 := by
          exact hq
        have hxP : x ∈ P.asIdeal :=
          hxP_of_rN_eq_one hrN
        have hAdiv : A ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← hPgen]
          exact hxP
        simpa [hrN, hqN] using hAdiv
      · have hqN : qN = 1 := by
          exact hq
        have hxP : x ∈ P.asIdeal :=
          hxP_of_rN_eq_one hrN
        have hxQ : x ∈ Q.asIdeal :=
          hxQ_of_qN_eq_one hqN
        have hPQideal :
            P.asIdeal ≠ Q.asIdeal := by
          intro h
          apply hPQ
          exact HeightOneSpectrum.ext h
        have hcoprime :
            P.asIdeal ⊔ Q.asIdeal = ⊤ :=
          (P.isPrime.isMaximal P.ne_bot).coprime_of_ne
            (Q.isPrime.isMaximal Q.ne_bot) hPQideal
        have hxMul :
            x ∈ P.asIdeal * Q.asIdeal := by
          rw [Ideal.mul_eq_inf_of_coprime hcoprime]
          exact ⟨hxP, hxQ⟩
        have hAQdiv : A * Qelt ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← Ideal.span_singleton_mul_span_singleton,
            ← hPgen, ← hQgen]
          exact hxMul
        simpa [hrN, hqN] using hAQdiv
  have hcorrect0 :
      A ^ rN * Qelt ^ qN ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hA0)
      (pow_ne_zero _ hQ0)
  have hparity :
      ∀ R : HeightOneSpectrum O,
        Even
          (principalCount (L := L) R x -
            principalCount (L := L) R
              (A ^ rN * Qelt ^ qN)) := by
    intro R
    have hcountCorrection :
        principalCount (L := L) R
            (A ^ rN * Qelt ^ qN) =
          (rN : ℤ) *
              principalCount (L := L) R A +
            (qN : ℤ) *
              principalCount (L := L) R Qelt := by
      rw [principalCount_mul
          (pow_ne_zero _ hA0) (pow_ne_zero _ hQ0),
        principalCount_pow, principalCount_pow]
    by_cases hRP : R = P
    · subst R
      have hQP : P ≠ Q := hPQ
      rw [hcountCorrection,
        principalCount_generator_self P hPgen hA0,
        principalCount_generator_of_ne
          Q P hQgen hQ0 hQP]
      rw [principalCount_eq_factorization_span
        x hx P]
      change Even ((nP : ℤ) - ((rN : ℤ) * 1 + (qN : ℤ) * 0))
      refine ⟨(nP / 2 : ℕ), ?_⟩
      have hdivmod := Nat.mod_add_div nP 2
      dsimp only [rN]
      omega
    · by_cases hRQ : R = Q
      · subst R
        have hPQ' : Q ≠ P := Ne.symm hPQ
        rw [hcountCorrection,
          principalCount_generator_of_ne
            P Q hPgen hA0 hPQ',
          principalCount_generator_self Q hQgen hQ0]
        rw [principalCount_eq_factorization_span
          x hx Q]
        change Even ((nQ : ℤ) - ((rN : ℤ) * 0 + (qN : ℤ) * 1))
        refine ⟨(nQ / 2 : ℕ), ?_⟩
        have hdivmod := Nat.mod_add_div nQ 2
        dsimp only [qN]
        omega
      · rw [hcountCorrection,
          principalCount_generator_of_ne
            P R hPgen hA0 hRP,
          principalCount_generator_of_ne
            Q R hQgen hQ0 hRQ]
        simpa using hAway R hRP hRQ
  obtain ⟨ε, y, hxy⟩ :=
    exists_unit_mul_correction_mul_sq
      (L := L)
      (A ^ rN * Qelt ^ qN) x
      hcorrect0 hx hdiv hparity
  let r : ZMod 2 := rN
  let q : ZMod 2 := qN
  have hrval : r.val = rN := by
    exact ZMod.val_cast_of_lt hrN_lt
  have hqval : q.val = qN := by
    exact ZMod.val_cast_of_lt hqN_lt
  refine ⟨r, q, ε, y, ?_⟩
  simpa only [hrval, hqval, mul_assoc] using hxy
end MazurProof.ExceptionalPrincipalIdeal
end
end
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianDifferentSupport.fieldL
def absoluteBasisO :
    Basis (Fin 2 × Fin 3) ℤ O :=
  N13GaussianNumberField.absoluteRingOfIntegersBasis.map
    classNumberOrderToOIntLinearEquiv
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
local instance freeO : Module.Free ℤ O :=
  Module.Free.of_basis absoluteBasisO
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
local instance finiteO : Module.Finite ℤ O :=
  Module.Finite.of_basis absoluteBasisO
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianDifferentSupport.fieldL
/-- Cubing the ramified carrier extracts the Gaussian prime `3-2i`. -/
theorem primeAInteger_cube :
    primeAInteger ^ 3 =
      gaussianPiInteger * primeACubeCofactor := by
  apply Subtype.ext
  change
    (1 - gaussianI * gaussianTheta ^ 2 -
        (1 + gaussianI) * gaussianTheta) ^ 3 =
      (3 - 2 * gaussianI) *
        (gaussianTheta *
          (-gaussianI * gaussianTheta - 1 - 2 * gaussianI))
  have hi : gaussianI ^ 2 + 1 = 0 := by
    rw [gaussianI_sq]
    ring
  rw [← sub_eq_zero]
  linear_combination
    (gaussianI * gaussianTheta ^ 3 +
        (1 + gaussianI) * gaussianTheta ^ 2 +
        (-3 + gaussianI) * gaussianTheta - 1) *
        gaussianTheta_gaussian_cubic +
      (-gaussianI * gaussianTheta ^ 6 -
        3 * gaussianI * gaussianTheta ^ 5 -
        3 * gaussianI * gaussianTheta ^ 4 -
        gaussianI * gaussianTheta ^ 3 -
        gaussianTheta ^ 5 + gaussianTheta ^ 4 +
        7 * gaussianTheta ^ 3 + 3 * gaussianTheta ^ 2 -
        4 * gaussianTheta) * hi
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GlobalKummerNormalization.fieldL MazurProof.N13GaussianDifferentSupport.fieldL
/-- Direct factorization of the sextic derivative at its integral root. -/
theorem differentInteger_eq :
    integralEval N13SexticIrreducible.fInt.derivative =
      4 * (differentUnit : O) * primeAInteger ^ 2 := by
  apply Subtype.ext
  rw [coe_integralEval]
  change
    eval₂ (algebraMap ℤ L) gaussianTheta
        N13SexticIrreducible.fInt.derivative =
      4 *
        (gaussianI * gaussianTheta ^ 2 *
          (gaussianTheta + 1)) *
        (1 - gaussianI * gaussianTheta ^ 2 -
          (1 + gaussianI) * gaussianTheta) ^ 2
  have hderivative :
      N13SexticIrreducible.fInt.derivative =
        6 * X ^ 5 + 20 * X ^ 4 + 24 * X ^ 3 +
          6 * X ^ 2 + 2 * X + 2 := by
    simp [N13SexticIrreducible.fInt]
    ring
  rw [hderivative]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_ofNat]
  rw [← sub_eq_zero]
  have hi : gaussianI ^ 2 + 1 = 0 := by
    rw [gaussianI_sq]
    ring
  linear_combination
    (4 * gaussianI * gaussianTheta ^ 4 +
        4 * gaussianI * gaussianTheta ^ 3 +
        4 * gaussianI * gaussianTheta ^ 2 +
        4 * gaussianI * gaussianTheta -
        2 * gaussianTheta ^ 2 - 2) *
        gaussianTheta_gaussian_cubic +
      (-4 * gaussianI * gaussianTheta ^ 7 -
        12 * gaussianI * gaussianTheta ^ 6 -
        12 * gaussianI * gaussianTheta ^ 5 -
        4 * gaussianI * gaussianTheta ^ 4 +
        8 * gaussianTheta ^ 5 + 24 * gaussianTheta ^ 4 +
        24 * gaussianTheta ^ 3 + 8 * gaussianTheta ^ 2) * hi
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
/-- The factor `1-i` squares to `2` times a unit. -/
theorem primeTwoInteger_sq :
    primeTwoInteger ^ 2 =
      2 * (-(integralIUnit : O)) := by
  simp only [primeTwoInteger]
  calc
    (1 - integralI) ^ 2 =
        1 - 2 * integralI + integralI ^ 2 := by ring
    _ = 2 * (-integralI) := by
      rw [integralI_sq]
      ring
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
set_option maxHeartbeats 800000 in
theorem span_two_eq :
    Ideal.span ({(2 : O)} : Set O) = primeTwoIdeal ^ 2 := by
  have hnegI : IsUnit (-(integralIUnit : O)) :=
    (-integralIUnit).isUnit
  rw [primeTwoIdeal, Ideal.span_singleton_pow]
  calc
    Ideal.span ({(2 : O)} : Set O) =
        Ideal.span
          ({2 * (-(integralIUnit : O))} : Set O) :=
      (Ideal.span_singleton_mul_right_unit
        hnegI (2 : O)).symm
    _ = Ideal.span ({primeTwoInteger ^ 2} : Set O) :=
      congrArg (fun x : O => Ideal.span ({x} : Set O))
        primeTwoInteger_sq.symm
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
set_option maxHeartbeats 800000 in
theorem span_differentInteger_eq :
    Ideal.span
        ({integralEval
          N13SexticIrreducible.fInt.derivative} : Set O) =
      primeTwoIdeal ^ 4 * primeAIdeal ^ 2 := by
  rw [differentInteger_eq]
  calc
    Ideal.span
          ({4 * (differentUnit : O) * primeAInteger ^ 2} :
            Set O) =
        Ideal.span ({4 * primeAInteger ^ 2} : Set O) := by
      convert
        Ideal.span_singleton_mul_left_unit
          differentUnit.isUnit (4 * primeAInteger ^ 2) using 1 <;>
        ring
    _ =
        Ideal.span ({(4 : O)} : Set O) *
          Ideal.span ({primeAInteger ^ 2} : Set O) :=
      (Ideal.span_singleton_mul_span_singleton _ _).symm
    _ =
        (Ideal.span ({(2 : O)} : Set O)) ^ 2 *
          primeAIdeal ^ 2 := by
      simp only [primeAIdeal, Ideal.span_singleton_pow]
      rw [show (4 : O) = (2 : O) ^ 2 by norm_num,
        ← Ideal.span_singleton_pow]
    _ = (primeTwoIdeal ^ 2) ^ 2 * primeAIdeal ^ 2 := by
      rw [span_two_eq]
    _ = primeTwoIdeal ^ 4 * primeAIdeal ^ 2 := by
      rw [← pow_mul]
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianNumberField.fieldL MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.numberFieldL
/-- In the absolute degree-six field, the Gaussian prime `3-2i` has norm
`13³`: its Gaussian norm is `13`, and the relative extension has degree
three. -/
theorem fieldNorm_gaussianPiInteger :
    Algebra.norm ℚ ((gaussianPiInteger : O) : L) =
      13 ^ 3 := by
  letI : Module.Free ℚ K :=
    Module.Free.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Finite ℚ K :=
    Module.Finite.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Free K L :=
    Module.Free.of_basis
      N13GaussianCubicField.powerBasis.basis
  letI : Module.Finite K L :=
    Module.Finite.of_basis
      N13GaussianCubicField.powerBasis.basis
  have hpi :
      ((gaussianPiInteger : O) : L) =
        algebraMap K L
          (algebraMap GI K
            N13GaussianGlobalArithmetic.pi) := by
    change
      3 - 2 * gaussianI =
        algebraMap K L
          (algebraMap GI K
            N13GaussianGlobalArithmetic.pi)
    simp only [N13GaussianGlobalArithmetic.pi,
      N13GaussianFieldEquiv.gaussianI,
      IsScalarTower.algebraMap_apply GI
        N13GaussianCubicField.K L,
      map_sub, map_mul, map_ofNat]
  rw [hpi, ← Algebra.norm_norm (R := ℚ) (S := K)]
  rw [Algebra.norm_algebraMap,
    N13GaussianNumberField.finrank_K_L,
    map_pow, N13GaussianFractionField.fieldNorm_pi]
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.intAlgebraO MazurProof.N13GaussianDifferentSupport.numberFieldL
theorem algebraNorm_gaussianPiInteger :
    Algebra.norm ℤ gaussianPiInteger = 13 ^ 3 := by
  let gpi : N13GaussianClassNumberOne.O :=
    OToClassNumberOrderAlgEquiv gaussianPiInteger
  have hfield :
      Algebra.norm ℚ
          ((gpi : N13GaussianClassNumberOne.O) : L) =
        13 ^ 3 := by
    have hcoe :
        ((gpi : N13GaussianClassNumberOne.O) : L) =
          ((gaussianPiInteger : O) : L) := by
      rfl
    rw [hcoe]
    exact fieldNorm_gaussianPiInteger
  have hnormStd :
      Algebra.norm ℤ gpi = 13 ^ 3 := by
    apply IsFractionRing.injective ℤ ℚ
    calc
      algebraMap ℤ ℚ (Algebra.norm ℤ gpi) =
          Algebra.norm ℚ
            ((gpi : N13GaussianClassNumberOne.O) : L) :=
        Algebra.coe_norm_int gpi
      _ = 13 ^ 3 := hfield
      _ = algebraMap ℤ ℚ (13 ^ 3 : ℤ) := by norm_num
  calc
    Algebra.norm ℤ gaussianPiInteger =
        Algebra.norm ℤ gpi :=
      (Algebra.norm_eq_of_algEquiv
        OToClassNumberOrderAlgEquiv
        gaussianPiInteger).symm
    _ = 13 ^ 3 := hnormStd
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.finiteO MazurProof.N13GaussianDifferentSupport.freeO MazurProof.N13GaussianDifferentSupport.intAlgebraO
theorem absNorm_gaussianPiIdeal :
    Ideal.absNorm
        (Ideal.span ({gaussianPiInteger} : Set O)) =
      13 ^ 3 := by
  rw [Ideal.absNorm_span_singleton]
  change
    (Algebra.norm ℤ gaussianPiInteger).natAbs = 13 ^ 3
  rw [algebraNorm_gaussianPiInteger]
  norm_num
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
theorem primeAIdeal_pow_three :
    primeAIdeal ^ 3 =
      Ideal.span ({gaussianPiInteger} : Set O) := by
  rw [primeAIdeal, Ideal.span_singleton_pow,
    primeAInteger_cube]
  exact Ideal.span_singleton_mul_right_unit
    primeACubeCofactorUnit.isUnit gaussianPiInteger
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.freeO
/-- The ramified carrier has residue norm `13`. -/
theorem absNorm_primeAIdeal :
    Ideal.absNorm primeAIdeal = 13 := by
  apply Nat.pow_left_injective (by norm_num : 3 ≠ 0)
  change
    Ideal.absNorm primeAIdeal ^ 3 = 13 ^ 3
  rw [← map_pow, primeAIdeal_pow_three,
    absNorm_gaussianPiIdeal]
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.freeO
/-- The ramified carrier is prime because its absolute ideal norm is the
rational prime `13`. -/
theorem primeAIdeal_isPrime :
    primeAIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_primeAIdeal]
  exact Nat.irreducible_iff_prime.mpr
    (Nat.prime_iff.mp (by norm_num : Nat.Prime 13))
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.freeO
theorem primeAIdeal_ne_bot :
    primeAIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_primeAIdeal, Ideal.absNorm_bot] at this
  norm_num at this
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
/-- The absolute integral basis has six elements. -/
theorem finrank_int_O :
    Module.finrank ℤ O = 6 := by
  rw [Module.finrank_eq_card_basis absoluteBasisO]
  norm_num
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
theorem primeTwoIdeal_isPrime :
    primeTwoIdeal.IsPrime := by
  letI : relativeGaussianTwoIdeal.IsPrime :=
    relativeGaussianTwoIdeal_isPrime
  have h :
      (relativeGaussianTwoIdeal.map
        relativeToORingEquiv).IsPrime := by
    infer_instance
  rwa [relativeGaussianTwoIdeal_map_eq] at h
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.finiteO MazurProof.N13GaussianDifferentSupport.freeO
/-- The unique prime above two has residue degree three. -/
theorem absNorm_primeTwoIdeal :
    Ideal.absNorm primeTwoIdeal = 2 ^ 3 := by
  have hnorm :=
    congrArg Ideal.absNorm span_two_eq
  have htwo :
      Ideal.absNorm
          (Ideal.span ({(2 : O)} : Set O)) =
        2 ^ 6 := by
    simpa [finrank_int_O] using
      (Ideal.absNorm_span_natCast (S := O) 2)
  rw [map_pow, htwo] at hnorm
  apply Nat.pow_left_injective (by norm_num : 2 ≠ 0)
  norm_num at hnorm ⊢
  omega
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.freeO
theorem primeTwoIdeal_ne_bot :
    primeTwoIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_primeTwoIdeal, Ideal.absNorm_bot] at this
  norm_num at this
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
def P2 : HeightOneSpectrum O :=
  ⟨primeTwoIdeal, primeTwoIdeal_isPrime,
    primeTwoIdeal_ne_bot⟩
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
def PA : HeightOneSpectrum O :=
  ⟨primeAIdeal, primeAIdeal_isPrime,
    primeAIdeal_ne_bot⟩
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
@[simp] theorem P2_asIdeal :
    P2.asIdeal = primeTwoIdeal :=
  rfl
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
@[simp] theorem PA_asIdeal :
    PA.asIdeal = primeAIdeal :=
  rfl
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.freeO
theorem P2_ne_PA :
    P2 ≠ PA := by
  intro h
  have hideal := congrArg
    (fun P : HeightOneSpectrum O => P.asIdeal) h
  have hnorm := congrArg Ideal.absNorm hideal
  simpa [absNorm_primeTwoIdeal,
    absNorm_primeAIdeal] using hnorm
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
/-- The derivative is supported at exactly the displayed primes above
two and at the ramified prime above thirteen. -/
theorem eq_P2_or_PA_of_different_mem
    (R : HeightOneSpectrum O)
    (hmem :
      integralEval
          N13SexticIrreducible.fInt.derivative ∈
        R.asIdeal) :
    R = P2 ∨ R = PA := by
  have hle :
      Ideal.span
          ({integralEval
            N13SexticIrreducible.fInt.derivative} :
            Set O) ≤ R.asIdeal := by
    rwa [Ideal.span_singleton_le_iff_mem]
  rw [span_differentInteger_eq] at hle
  rcases R.isPrime.mul_le.mp hle with htwo | hA
  · have htwo' : primeTwoIdeal ≤ R.asIdeal :=
      R.isPrime.le_of_pow_le htwo
    left
    apply HeightOneSpectrum.ext
    exact
      ((primeTwoIdeal_isPrime.isMaximal
        primeTwoIdeal_ne_bot).eq_of_le
          R.isPrime.ne_top htwo').symm
  · have hA' : primeAIdeal ≤ R.asIdeal :=
      R.isPrime.le_of_pow_le hA
    right
    apply HeightOneSpectrum.ext
    exact
      ((primeAIdeal_isPrime.isMaximal
        primeAIdeal_ne_bot).eq_of_le
          R.isPrime.ne_top hA').symm
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.fractionRingOL
/-- Away from `P2` and `PA`, the already-proved étale parity theorem
applies uniformly. -/
theorem normalizedKummerInteger_count_even_away_P2_PA
    (D : N13LowDegreeKummerHom.LowRep)
    (R : HeightOneSpectrum O)
    (hR2 : R ≠ P2)
    (hRA : R ≠ PA) :
    Even
      (FractionalIdeal.count L R
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) := by
  apply
    N13GlobalKummerAwayDifferentParity.normalizedKummerInteger_count_even_of_not_mem_different
  intro hmem
  rcases eq_P2_or_PA_of_different_mem R hmem with h2 | hA
  · exact hR2 h2
  · exact hRA hA
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.intAlgebraO MazurProof.N13GaussianDifferentSupport.numberFieldL
/-- Integral norms in the integral-closure presentation agree with the
field norm after embedding in `ℚ`. -/
theorem coe_algebraNorm_int (x : O) :
    (Algebra.norm ℤ x : ℚ) =
      Algebra.norm ℚ ((x : O) : L) := by
  exact HuangN13.N13GaussianDifferentSupport.coe_algebraNorm_int x
end
end MazurProof.N13GaussianDifferentSupport
end
end

section
section
set_option autoImplicit false
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.finiteO MazurProof.N13GaussianDifferentSupport.fractionRingOL MazurProof.N13GaussianDifferentSupport.freeO MazurProof.N13GaussianDifferentSupport.intAlgebraO MazurProof.N13GaussianDifferentSupport.numberFieldL
/-- A rational-square field norm gives even `p`-adic valuation of the
absolute norm of the principal ideal.  Rational denominators in the
square root are handled directly by `padicValRat`. -/
theorem even_padicValNat_absNorm_span_of_norm_sq
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : O) (hx : x ≠ 0)
    (hsq : ∃ s : ℚ,
      Algebra.norm ℚ ((x : O) : L) = s ^ 2) :
    Even
      (padicValNat p
        (Ideal.absNorm
          (Ideal.span ({x} : Set O)))) := by
  obtain ⟨s, hs⟩ := hsq
  have hxL : ((x : O) : L) ≠ 0 := by
    exact
      (map_ne_zero_iff (algebraMap O L)
        (IsFractionRing.injective O L)).2 hx
  have hnorm0 :
      Algebra.norm ℚ ((x : O) : L) ≠ 0 := by
    exact
      (Algebra.norm_ne_zero_iff (R := ℚ) (S := L)).mpr hxL
  have hs0 : s ≠ 0 := by
    intro hs0
    apply hnorm0
    simpa [hs0] using hs
  have hRatEven :
      Even
        (padicValRat p
          (Algebra.norm ℚ ((x : O) : L))) := by
    refine ⟨padicValRat p s, ?_⟩
    rw [hs, padicValRat.pow s]
    ring
  have hValEq :
      (padicValNat p
          (Ideal.absNorm
            (Ideal.span ({x} : Set O))) : ℤ) =
        padicValRat p
          (Algebra.norm ℚ ((x : O) : L)) := by
    have h :=
      congrArg (padicValRat p) (coe_algebraNorm_int x)
    simpa [Ideal.absNorm_span_singleton,
      padicValInt] using h
  have hIntEven :
      Even
        ((padicValNat p
          (Ideal.absNorm
            (Ideal.span ({x} : Set O))) : ℤ)) := by
    rw [hValEq]
    exact hRatEven
  exact (Int.even_coe_nat _).mp hIntEven
end
end MazurProof.N13GaussianDifferentSupport
end
end



set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianDifferentSupport
open Algebra Module Polynomial
open scoped nonZeroDivisors
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.numberFieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fractionRingOL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.intAlgebraO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindRelativeO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeGIL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeRelativeO

attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GaussianDifferentSupport.dedekindO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.finiteO MazurProof.N13GaussianDifferentSupport.fractionRingOL MazurProof.N13GaussianDifferentSupport.freeO MazurProof.N13GaussianDifferentSupport.numberFieldL
theorem solution (D : N13LowDegreeKummerHom.LowRep) : ∃ ε : MazurProof.N13GaussianDifferentSupport.Oˣ, ∃ y : MazurProof.N13GaussianDifferentSupport.O, MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D = (ε : MazurProof.N13GaussianDifferentSupport.O) * y ^ 2 := by
  letI : IsPrincipalIdealRing MazurProof.N13GaussianDifferentSupport.O :=
    @N13GlobalKummerPID.isPrincipalIdealRing_of_ringEquiv
      MazurProof.N13GaussianDifferentSupport.O N13GaussianClassNumberOne.O
      inferInstance inferInstance
      N13GaussianClassNumberOne.isPrincipalIdealRingO
      N13GlobalKummerPID.integralClosureEquivClassNumberOrder
  let x : MazurProof.N13GaussianDifferentSupport.O := MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D
  have hx : x ≠ 0 := by
    simpa only [x] using
      N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D
  have hAway :
      ∀ R : HeightOneSpectrum MazurProof.N13GaussianDifferentSupport.O,
        R ≠ MazurProof.N13GaussianDifferentSupport.P2 → R ≠ MazurProof.N13GaussianDifferentSupport.PA →
          Even
            (EvenPrincipalIdeal.principalCount
              (L := MazurProof.N13GaussianDifferentSupport.L) R x) := by
    intro R hR2 hRA
    simpa [EvenPrincipalIdeal.principalCount, x] using
      MazurProof.N13GaussianDifferentSupport.normalizedKummerInteger_count_even_away_P2_PA
        D R hR2 hRA
  obtain ⟨r, a, ε, y, hxy⟩ :=
    ExceptionalPrincipalIdeal.exists_unit_two_carriers_mul_sq_of_even_away
      (L := MazurProof.N13GaussianDifferentSupport.L) MazurProof.N13GaussianDifferentSupport.P2 MazurProof.N13GaussianDifferentSupport.PA MazurProof.N13GaussianDifferentSupport.P2_ne_PA
      MazurProof.N13GaussianDifferentSupport.primeTwoInteger MazurProof.N13GaussianDifferentSupport.primeAInteger x
      (by rfl) (by rfl) hx hAway
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    rw [hxy, hy0]
    simp
  let J : Ideal MazurProof.N13GaussianDifferentSupport.O := Ideal.span ({y} : Set MazurProof.N13GaussianDifferentSupport.O)
  have hJ : J ≠ ⊥ := by
    intro hJ0
    apply hy
    exact Ideal.span_singleton_eq_bot.mp hJ0
  have hfac :
      Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O) =
        MazurProof.N13GaussianDifferentSupport.P2.asIdeal ^ r.val *
          MazurProof.N13GaussianDifferentSupport.PA.asIdeal ^ a.val * J ^ 2 := by
    calc
      Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O) =
          Ideal.span
            ({(ε : MazurProof.N13GaussianDifferentSupport.O) * MazurProof.N13GaussianDifferentSupport.primeTwoInteger ^ r.val *
              MazurProof.N13GaussianDifferentSupport.primeAInteger ^ a.val * y ^ 2} : Set MazurProof.N13GaussianDifferentSupport.O) :=
        congrArg
          (fun z : MazurProof.N13GaussianDifferentSupport.O => Ideal.span ({z} : Set MazurProof.N13GaussianDifferentSupport.O)) hxy
      _ =
          Ideal.span ({(ε : MazurProof.N13GaussianDifferentSupport.O)} : Set MazurProof.N13GaussianDifferentSupport.O) *
            Ideal.span
              ({MazurProof.N13GaussianDifferentSupport.primeTwoInteger ^ r.val} : Set MazurProof.N13GaussianDifferentSupport.O) *
            Ideal.span
              ({MazurProof.N13GaussianDifferentSupport.primeAInteger ^ a.val} : Set MazurProof.N13GaussianDifferentSupport.O) *
            Ideal.span ({y ^ 2} : Set MazurProof.N13GaussianDifferentSupport.O) := by
        rw [Ideal.span_singleton_mul_span_singleton,
          Ideal.span_singleton_mul_span_singleton,
          Ideal.span_singleton_mul_span_singleton]
      _ =
          MazurProof.N13GaussianDifferentSupport.P2.asIdeal ^ r.val *
            MazurProof.N13GaussianDifferentSupport.PA.asIdeal ^ a.val * J ^ 2 := by
        rw [Ideal.span_singleton_eq_top.mpr ε.isUnit,
          ← Ideal.one_eq_top, one_mul,
          ← Ideal.span_singleton_pow,
          ← Ideal.span_singleton_pow,
          ← Ideal.span_singleton_pow]
        rfl
  have hNJ : Ideal.absNorm J ≠ 0 := by
    intro hzero
    exact hJ (Ideal.absNorm_eq_zero_iff.mp hzero)
  have hAbs :
      Ideal.absNorm (Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O)) =
        (2 ^ 3) ^ r.val * 13 ^ a.val *
          (Ideal.absNorm J) ^ 2 := by
    calc
      Ideal.absNorm (Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O)) =
          Ideal.absNorm
            (MazurProof.N13GaussianDifferentSupport.P2.asIdeal ^ r.val *
              MazurProof.N13GaussianDifferentSupport.PA.asIdeal ^ a.val * J ^ 2) :=
        congrArg Ideal.absNorm hfac
      _ =
          (2 ^ 3) ^ r.val * 13 ^ a.val *
            (Ideal.absNorm J) ^ 2 := by
        simp only [map_mul, map_pow, MazurProof.N13GaussianDifferentSupport.P2_asIdeal, MazurProof.N13GaussianDifferentSupport.PA_asIdeal,
          MazurProof.N13GaussianDifferentSupport.absNorm_primeTwoIdeal, MazurProof.N13GaussianDifferentSupport.absNorm_primeAIdeal]
  letI primeTwoFact : Fact (Nat.Prime 2) :=
    ⟨by norm_num⟩
  have hValTwo :
      padicValNat 2
          (Ideal.absNorm (Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O))) =
        3 * r.val +
          2 * padicValNat 2 (Ideal.absNorm J) := by
    have h2 : (2 : ℕ) ≠ 0 := by norm_num
    have h13 : (13 : ℕ) ≠ 0 := by norm_num
    rw [hAbs]
    rw [padicValNat.mul
      (mul_ne_zero
        (pow_ne_zero _ (pow_ne_zero 3 h2))
        (pow_ne_zero _ h13))
      (pow_ne_zero _ hNJ)]
    rw [padicValNat.mul
      (pow_ne_zero _ (pow_ne_zero 3 h2))
      (pow_ne_zero _ h13)]
    rw [padicValNat.pow (2 ^ 3) r.val,
      padicValNat.prime_pow,
      padicValNat.pow 13 a.val,
      padicValNat.eq_zero_of_not_dvd
        (p := 2) (n := 13) (by norm_num),
      padicValNat.pow (Ideal.absNorm J) 2]
    ring
  have hTotalEvenTwo :
      Even
        (padicValNat 2
          (Ideal.absNorm
            (Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O)))) := by
    apply MazurProof.N13GaussianDifferentSupport.even_padicValNat_absNorm_span_of_norm_sq
      2 x hx
    change
      ∃ s : ℚ,
        Algebra.norm ℚ
            (((MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D : MazurProof.N13GaussianDifferentSupport.O) : MazurProof.N13GaussianDifferentSupport.L)) =
          s ^ 2
    exact MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger_norm_isSquare D
  have hrEven : Even (3 * r.val) := by
    rcases hTotalEvenTwo with ⟨k, hk⟩
    refine
      ⟨k - padicValNat 2 (Ideal.absNorm J), ?_⟩
    rw [hValTwo] at hk
    omega
  have hr0 : r.val = 0 := by
    rcases hrEven with ⟨k, hk⟩
    have hrlt := r.val_lt
    omega
  letI primeThirteenFact : Fact (Nat.Prime 13) :=
    ⟨by norm_num⟩
  have hValThirteen :
      padicValNat 13
          (Ideal.absNorm (Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O))) =
        a.val +
          2 * padicValNat 13 (Ideal.absNorm J) := by
    have h2 : (2 : ℕ) ≠ 0 := by norm_num
    have h13 : (13 : ℕ) ≠ 0 := by norm_num
    rw [hAbs]
    rw [padicValNat.mul
      (mul_ne_zero
        (pow_ne_zero _ (pow_ne_zero 3 h2))
        (pow_ne_zero _ h13))
      (pow_ne_zero _ hNJ)]
    rw [padicValNat.mul
      (pow_ne_zero _ (pow_ne_zero 3 h2))
      (pow_ne_zero _ h13)]
    rw [padicValNat.pow (2 ^ 3) r.val,
      padicValNat.pow 2 3,
      padicValNat.eq_zero_of_not_dvd
        (p := 13) (n := 2) (by norm_num),
      padicValNat.pow 13 a.val,
      padicValNat_self,
      padicValNat.pow (Ideal.absNorm J) 2]
    ring
  have hTotalEvenThirteen :
      Even
        (padicValNat 13
          (Ideal.absNorm
            (Ideal.span ({x} : Set MazurProof.N13GaussianDifferentSupport.O)))) := by
    apply MazurProof.N13GaussianDifferentSupport.even_padicValNat_absNorm_span_of_norm_sq
      13 x hx
    change
      ∃ s : ℚ,
        Algebra.norm ℚ
            (((MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D : MazurProof.N13GaussianDifferentSupport.O) : MazurProof.N13GaussianDifferentSupport.L)) =
          s ^ 2
    exact MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger_norm_isSquare D
  have haEven : Even a.val := by
    rcases hTotalEvenThirteen with ⟨k, hk⟩
    refine
      ⟨k - padicValNat 13 (Ideal.absNorm J), ?_⟩
    rw [hValThirteen] at hk
    omega
  have ha0 : a.val = 0 := by
    rcases haEven with ⟨k, hk⟩
    have halt := a.val_lt
    omega
  refine ⟨ε, y, ?_⟩
  simpa only [x, hr0, ha0, pow_zero, mul_one] using hxy
