-- Prove2me | solution 1 for MazurProof.N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:15:11.592914+00:00
-- url     : https://prove2.me/submissions/ef9fffe5-17fa-4da0-8dc2-2b80d2c60b57

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_root_sextic
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_sexticToGaussian_bijective


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

namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
def sexticEquivGaussian : Ls ≃ₐ[ℚ] Lg :=
  AlgEquiv.ofBijective sexticToGaussian
    sexticToGaussian_bijective
end
end MazurProof.N13GaussianFieldEquiv

namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
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

namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
theorem integralNormalization_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    integralNormalization p ≠ 0 := by
  exact
    (IsFractionRing.integerNormalization_eq_zero_iff
      (A := ℤ) (K := ℚ)).not.mpr hp
end
end MazurProof.N13GlobalKummerNormalization

namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizedGCDMonoid
theorem integralNormalization_content_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    (integralNormalization p).content ≠ 0 := by
  exact
    Polynomial.content_eq_zero_iff.not.mpr
      (integralNormalization_ne_zero hp)
end
end MazurProof.N13GlobalKummerNormalization

namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
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

namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
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

namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
open MazurProof.N13GaussianFieldEquiv
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

attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13GlobalKummerNormalization.fieldL MazurProof.N13GlobalKummerSimpleRootParity.charZeroL MazurProof.N13GlobalKummerSimpleRootParity.fieldL
theorem solution (D : N13LowDegreeKummerHom.LowRep) : normalizedKummerInteger D ≠ 0 := by
  obtain ⟨c, hc, hspec⟩ :=
    MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger_spec D
  have hcL :
      algebraMap ℚ MazurProof.N13GlobalKummerSimpleRootParity.L c ≠ 0 :=
    by
      simpa only [map_zero] using
        (algebraMap ℚ MazurProof.N13GlobalKummerSimpleRootParity.L).injective.ne hc
  have hu :
      MazurProof.N13MumfordKummerValue.uTheta
          (MazurProof.N13LowDegreeKummerHom.asMumford D) ≠ 0 :=
    MazurProof.N13MumfordKummerValue.uTheta_ne_zero _
  have huL :
      MazurProof.N13GaussianFieldEquiv.sexticEquivGaussian
          (MazurProof.N13MumfordKummerValue.uTheta
            (MazurProof.N13LowDegreeKummerHom.asMumford D)) ≠ 0 :=
    by
      simpa only [map_zero] using
        MazurProof.N13GaussianFieldEquiv.sexticEquivGaussian.injective.ne
          hu
  intro hzero
  have hprod :
      algebraMap ℚ MazurProof.N13GlobalKummerSimpleRootParity.L c *
          MazurProof.N13GaussianFieldEquiv.sexticEquivGaussian
            (MazurProof.N13MumfordKummerValue.uTheta
              (MazurProof.N13LowDegreeKummerHom.asMumford D)) =
        0 := by
    calc
      algebraMap ℚ MazurProof.N13GlobalKummerSimpleRootParity.L c *
            MazurProof.N13GaussianFieldEquiv.sexticEquivGaussian
              (MazurProof.N13MumfordKummerValue.uTheta
                (MazurProof.N13LowDegreeKummerHom.asMumford D)) =
          ((MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D : MazurProof.N13GlobalKummerSimpleRootParity.O) : MazurProof.N13GlobalKummerSimpleRootParity.L) :=
        hspec.symm
      _ = ((0 : MazurProof.N13GlobalKummerSimpleRootParity.O) : MazurProof.N13GlobalKummerSimpleRootParity.L) := by rw [hzero]
      _ = 0 := rfl
  exact (mul_ne_zero hcL huL) hprod
