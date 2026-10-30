-- Prove2me | solution 1 for MazurProof.N13GlobalKummerSimpleRootParity.normalizedKummerInteger_multiplicity_even_of_simpleRoot
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:55:58.967373+00:00
-- url     : https://prove2.me/submissions/a46a0df9-7e31-438d-afc9-fd965794818a

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_root_sextic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_sexticToGaussian_bijective
import Theorems.Thm_MazurProof_N13GlobalKummerIdealSquare_exists_scaledIntegralMumford
import Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_localF_derivative_isUnit
import Theorems.Thm_MazurProof_N13GoodPrimeSimpleRoot_multiplicity_even_of_completion_quadratic_simpleRoot


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GlobalKummerSimpleRootParity
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fieldL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroCompletion

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
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GlobalKummerNormalization.fieldL MazurProof.N13GlobalKummerSimpleRootParity.charZeroL MazurProof.N13GlobalKummerSimpleRootParity.fieldL
/-- The normalized Kummer integer is nonzero. -/
theorem normalizedKummerInteger_ne_zero
    (D : N13LowDegreeKummerHom.LowRep) :
    normalizedKummerInteger D ≠ 0 := by
  obtain ⟨c, hc, hspec⟩ :=
    normalizedKummerInteger_spec D
  have hcL :
      algebraMap ℚ L c ≠ 0 :=
    by
      simpa only [map_zero] using
        (algebraMap ℚ L).injective.ne hc
  have hu :
      N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) ≠ 0 :=
    N13MumfordKummerValue.uTheta_ne_zero _
  have huL :
      N13GaussianFieldEquiv.sexticEquivGaussian
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) ≠ 0 :=
    by
      simpa only [map_zero] using
        N13GaussianFieldEquiv.sexticEquivGaussian.injective.ne
          hu
  intro hzero
  have hprod :
      algebraMap ℚ L c *
          N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) =
        0 := by
    calc
      algebraMap ℚ L c *
            N13GaussianFieldEquiv.sexticEquivGaussian
              (N13MumfordKummerValue.uTheta
                (N13LowDegreeKummerHom.asMumford D)) =
          ((normalizedKummerInteger D : O) : L) :=
        hspec.symm
      _ = ((0 : O) : L) := by rw [hzero]
      _ = 0 := rfl
  exact (mul_ne_zero hcL huL) hprod
end
end MazurProof.N13GlobalKummerSimpleRootParity
end
end

attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO MazurProof.N13GlobalKummerSimpleRootParity.fieldL MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
theorem solution (D : N13LowDegreeKummerHom.LowRep) (P : HeightOneSpectrum MazurProof.N13GlobalKummerSimpleRootParity.O) (hmem : MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D ∈ P.asIdeal) (hdifferent : MazurProof.N13GlobalKummerNormalization.integralEval N13SexticIrreducible.fInt.derivative ∉ P.asIdeal) (hsimple : IsUnit ((MazurProof.N13GlobalKummerSimpleRootParity.localU D P).derivative.eval (MazurProof.N13GlobalKummerSimpleRootParity.localTheta P))) : Even (multiplicity P.asIdeal (Ideal.span {MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D})) := by
  let a := (MazurProof.N13GlobalKummerSimpleRootParity.localU D P).coeff 2
  let b := (MazurProof.N13GlobalKummerSimpleRootParity.localU D P).coeff 1
  let c := (MazurProof.N13GlobalKummerSimpleRootParity.localU D P).coeff 0
  have hU :
      MazurProof.N13GlobalKummerSimpleRootParity.localU D P = MazurProof.N13GoodPrimeSimpleRoot.quadratic a b c := by
    simpa only [a, b, c] using
      MazurProof.N13GoodPrimeSimpleRoot.eq_quadratic_of_natDegree_le_two
        (MazurProof.N13GlobalKummerSimpleRootParity.localU D P)
        (MazurProof.N13GlobalKummerSimpleRootParity.localU_natDegree_le D P)
  have hsmall :
      a * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P ^ 2 +
          b * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P + c ∈
        P.completionIdeal MazurProof.N13GlobalKummerSimpleRootParity.L := by
    rw [← MazurProof.N13GoodPrimeSimpleRoot.quadratic_eval, ← hU,
      MazurProof.N13GlobalKummerSimpleRootParity.localU_eval_localTheta]
    exact
      (MazurProof.N13GlobalKummerSimpleRootParity.algebraMap_mem_completionIdeal_iff P _).mpr
        hmem
  have hquadDeriv :
      IsUnit
        (2 * a * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P + b) := by
    rw [← MazurProof.N13GoodPrimeSimpleRoot.quadratic_derivative_eval,
      ← hU]
    exact hsimple
  have hglobal :
      algebraMap MazurProof.N13GlobalKummerSimpleRootParity.O (P.adicCompletion MazurProof.N13GlobalKummerSimpleRootParity.L)
          (MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D) =
        ((a * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P ^ 2 +
              b * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P + c :
            MazurProof.N13GlobalKummerSimpleRootParity.LocalIntegers P) :
          P.adicCompletion MazurProof.N13GlobalKummerSimpleRootParity.L) := by
    have heval :
        a * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P ^ 2 +
              b * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P + c =
          algebraMap MazurProof.N13GlobalKummerSimpleRootParity.O (MazurProof.N13GlobalKummerSimpleRootParity.LocalIntegers P)
            (MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D) := by
      rw [← MazurProof.N13GoodPrimeSimpleRoot.quadratic_eval, ← hU,
        MazurProof.N13GlobalKummerSimpleRootParity.localU_eval_localTheta]
    change
      ((algebraMap MazurProof.N13GlobalKummerSimpleRootParity.O (MazurProof.N13GlobalKummerSimpleRootParity.LocalIntegers P)
          (MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D) :
        MazurProof.N13GlobalKummerSimpleRootParity.LocalIntegers P) :
          P.adicCompletion MazurProof.N13GlobalKummerSimpleRootParity.L) =
        ((a * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P ^ 2 +
              b * MazurProof.N13GlobalKummerSimpleRootParity.localTheta P + c :
            MazurProof.N13GlobalKummerSimpleRootParity.LocalIntegers P) :
          P.adicCompletion MazurProof.N13GlobalKummerSimpleRootParity.L)
    exact
      congrArg
        (fun z : MazurProof.N13GlobalKummerSimpleRootParity.LocalIntegers P =>
          (z : P.adicCompletion MazurProof.N13GlobalKummerSimpleRootParity.L))
        heval.symm
  apply
    MazurProof.N13GoodPrimeSimpleRoot.multiplicity_even_of_completion_quadratic_simpleRoot
      P
      (MazurProof.N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D)
      a b c (MazurProof.N13GlobalKummerSimpleRootParity.localTheta P) (MazurProof.N13GlobalKummerSimpleRootParity.localScale D P)
      (MazurProof.N13GlobalKummerSimpleRootParity.localF P) (MazurProof.N13GlobalKummerSimpleRootParity.localV D P) (MazurProof.N13GlobalKummerSimpleRootParity.localW D P)
      hglobal
      (MazurProof.N13GlobalKummerSimpleRootParity.localScale_ne_zero D P)
      hsmall hquadDeriv
      (MazurProof.N13GlobalKummerSimpleRootParity.localF_eval_localTheta P)
      (MazurProof.N13GlobalKummerSimpleRootParity.localF_derivative_isUnit P hdifferent)
      (by
        rw [← hU]
        exact MazurProof.N13GlobalKummerSimpleRootParity.local_relation D P)
