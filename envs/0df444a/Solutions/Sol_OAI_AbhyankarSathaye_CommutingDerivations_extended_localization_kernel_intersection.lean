-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.extended_localization_kernel_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:51:48.678984+00:00
-- url     : https://prove2.me/submissions/3b18469b-f1c1-41d4-9cb9-b17126eee93b

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedKernelIntersection.lean:L42-L84
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.extended_localization_kernel_intersection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_extendedParameter_laurent_intersection
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_extended_isLocalization

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedParameterRetraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The explicit intersection proof retains every dimension n >= 4 and
identifies its ordinary polynomial side with the standard subalgebra C[F_n]. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

/-- Replacing f by f+1 does not change the literal polynomial-expression set. -/
theorem exists_aeval_add_one_iff {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (f a : A) :
    (∃ q : Polynomial K, a = Polynomial.aeval (f + 1) q) ↔
      ∃ q : Polynomial K, a = Polynomial.aeval f q := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q.comp (Polynomial.X + 1), ?_⟩
    simp [Polynomial.aeval_comp]
  · rintro ⟨q, rfl⟩
    refine ⟨q.comp (Polynomial.X - 1), ?_⟩
    simp [Polynomial.aeval_comp]

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedKernelIntersection ----
namespace OAI

/-!
The coefficient algebra of the localization intersects the full ambient
ring in exactly `ℂ[Fₙ]` in every dimension `n ≥ 4`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem extendedCoefficientMap_polynomial {n : ℕ} (hn : 4 ≤ n) (q : Polynomial ℂ) :
    extendedCoefficientMap n (algebraMap (Polynomial ℂ) LaurentCoefficients q) =
      extendedLocMap hn (Polynomial.aeval (extendedAmbientParameter hn) q) := by
  change C (coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients q)) = _
  rw [coefficientMap_polynomial]
  let original : R →ₐ[ℂ] ExtendedLocalizedAmbient n :=
    (IsScalarTower.toAlgHom ℂ LocalizedAmbient (ExtendedLocalizedAmbient n)).comp
      (IsScalarTower.toAlgHom ℂ R LocalizedAmbient)
  have he : original.comp (Polynomial.aeval ambientC) =
      (extendedLocAlgHom hn).comp (Polynomial.aeval (extendedAmbientParameter hn)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    change C (loc ambientC) = extendedLocMap hn (extendedF hn + 1)
    exact (extendedLocMap_c hn).symm
  exact AlgHom.congr_fun he q

theorem extendedCoefficientMap_parameter {n : ℕ} (hn : 4 ≤ n) :
    extendedCoefficientMap n coefficientC = extendedLocMap hn (extendedAmbientParameter hn) := by
  change C (coefficientMap coefficientC) = extendedLocMap hn (extendedF hn + 1)
  rw [coefficientMap_C, extendedLocMap_c]

/-- Exact input to the generic commuting-family construction, specialized to
the actual all-dimensional localization and coordinate equivalence. -/
theorem extended_localization_kernel_intersection {n : ℕ} (hn : 4 ≤ n)
    (r : MvPolynomial (Fin n) ℂ) :
    (∃ b : LaurentCoefficients,
      extendedLocalizationEquiv hn (extendedLocMap hn r) = C b) ↔
    r ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)) := by
  let := extendedAlgebra hn
  let : IsLocalization.Away (extendedAmbientParameter hn) (ExtendedLocalizedAmbient n) := by
    change IsLocalization.Away (extendedF hn + 1) (ExtendedLocalizedAmbient n)
    exact extended_isLocalization hn
  constructor
  · rintro ⟨b, hb⟩
    have hpre : extendedLocMap hn r = extendedCoefficientMap n b := by
      apply (extendedLocalizationEquiv hn).injective
      rw [hb, extendedLocalizationEquiv_coefficient]
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial ℂ) b
    change b * coefficientC^m = algebraMap (Polynomial ℂ) LaurentCoefficients q at hq
    have he : extendedCoefficientMap n b *
        (extendedLocMap hn (extendedAmbientParameter hn))^m =
        extendedLocMap hn (Polynomial.aeval (extendedAmbientParameter hn) q) := by
      simpa only [map_mul, map_pow, extendedCoefficientMap_parameter hn,
        extendedCoefficientMap_polynomial hn] using congrArg (extendedCoefficientMap n) hq
    apply (extendedParameter_laurent_intersection hn (ExtendedLocalizedAmbient n) r).mp
    refine ⟨m, q, ?_⟩
    change (extendedLocMap hn (extendedAmbientParameter hn))^m * extendedLocMap hn r =
      extendedLocMap hn (Polynomial.aeval (extendedAmbientParameter hn) q)
    rw [hpre, mul_comm]
    exact he
  · intro hr
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨q, hq⟩ := hr
    obtain ⟨p, hp⟩ := (exists_aeval_add_one_iff (K := ℂ) (extendedF hn) r).mpr ⟨q, hq.symm⟩
    refine ⟨algebraMap (Polynomial ℂ) LaurentCoefficients p, ?_⟩
    calc
      extendedLocalizationEquiv hn (extendedLocMap hn r) =
          extendedLocalizationEquiv hn
            (extendedCoefficientMap n (algebraMap (Polynomial ℂ) LaurentCoefficients p)) := by
        apply congrArg (extendedLocalizationEquiv hn)
        rw [extendedCoefficientMap_polynomial]
        exact congrArg (extendedLocMap hn) hp
      _ = C (algebraMap (Polynomial ℂ) LaurentCoefficients p) :=
        extendedLocalizationEquiv_coefficient hn _

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem solution {n : ℕ} (hn : 4 ≤ n)
    (r : MvPolynomial (Fin n) ℂ) :
    (∃ b : LaurentCoefficients,
      extendedLocalizationEquiv hn (extendedLocMap hn r) = C b) ↔
    r ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)) := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.extended_localization_kernel_intersection hn r
    | exact OAI.AbhyankarSathaye.CommutingDerivations.extended_localization_kernel_intersection
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.extended_localization_kernel_intersection <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.extended_localization_kernel_intersection <;> assumption)
