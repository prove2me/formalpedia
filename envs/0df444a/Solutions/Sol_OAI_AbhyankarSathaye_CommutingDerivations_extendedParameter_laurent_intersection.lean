-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.extendedParameter_laurent_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:50:13.868449+00:00
-- url     : https://prove2.me/submissions/b1ff2946-2d87-45b2-8595-9c0fa7e1f16b

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedParameterRetraction.lean:L104-L132
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.extendedParameter_laurent_intersection. The node keeps its source
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

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedParameterRetraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The explicit intersection proof retains every dimension n >= 4 and
identifies its ordinary polynomial side with the standard subalgebra C[F_n]. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

theorem extendedParameter_ne_zero {n : ℕ} (hn : 4 ≤ n) : extendedAmbientParameter hn ≠ 0 := by
  intro hh
  have he := congrArg (extendedParameterSlice hn) hh
  simp at he

theorem extendedParameter_power_saturated {n : ℕ} (hn : 4 ≤ n)
    (a : MvPolynomial (Fin n) ℂ) (q : Polynomial ℂ) (m : ℕ)
    (he : (extendedAmbientParameter hn)^m * a = Polynomial.aeval (extendedAmbientParameter hn) q) :
    a = Polynomial.aeval (extendedAmbientParameter hn) (extendedParameterSlice hn a) := by
  apply mul_left_cancel₀ (pow_ne_zero m (extendedParameter_ne_zero hn))
  have hh := congrArg (Polynomial.aeval (extendedAmbientParameter hn) :
      Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ)
    (congrArg (extendedParameterSlice hn) he)
  have hh' : (extendedAmbientParameter hn)^m *
      Polynomial.aeval (extendedAmbientParameter hn) (extendedParameterSlice hn a) =
      Polynomial.aeval (extendedAmbientParameter hn) q := by
    simpa only [map_mul, map_pow, extendedParameterSlice_parameter,
      extendedParameterSlice_aeval_apply, Polynomial.aeval_X] using hh
  exact he.trans hh'.symm

theorem extendedParameter_localization_injective {n : ℕ} (hn : 4 ≤ n)
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin n) ℂ) L]
    [IsLocalization.Away (extendedAmbientParameter hn) L] :
    Function.Injective (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
  apply IsLocalization.injective L (M := Submonoid.powers (extendedAmbientParameter hn))
  intro z hz
  obtain ⟨m, rfl⟩ := hz
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m (extendedParameter_ne_zero hn))

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

/-- Complete dimension-quantified intersection in the standard subalgebra
representation of C[F_n], with localization membership given by one Laurent
denominator and an ordinary polynomial numerator. -/
theorem extendedParameter_laurent_intersection {n : ℕ} (hn : 4 ≤ n)
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin n) ℂ) L]
    [IsLocalization.Away (extendedAmbientParameter hn) L] (a : MvPolynomial (Fin n) ℂ) :
    (∃ (m : ℕ) (q : Polynomial ℂ),
      (algebraMap (MvPolynomial (Fin n) ℂ) L (extendedAmbientParameter hn))^m *
          algebraMap (MvPolynomial (Fin n) ℂ) L a =
        algebraMap (MvPolynomial (Fin n) ℂ) L (Polynomial.aeval (extendedAmbientParameter hn) q)) ↔
    a ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)) := by
  have hex :
      (∃ (m : ℕ) (q : Polynomial ℂ),
        (algebraMap (MvPolynomial (Fin n) ℂ) L (extendedAmbientParameter hn))^m *
            algebraMap (MvPolynomial (Fin n) ℂ) L a =
          algebraMap (MvPolynomial (Fin n) ℂ) L (Polynomial.aeval (extendedAmbientParameter hn) q)) ↔
      ∃ q : Polynomial ℂ, a = Polynomial.aeval (extendedAmbientParameter hn) q := by
    constructor
    · rintro ⟨m, q, hq⟩
      refine ⟨extendedParameterSlice hn a, extendedParameter_power_saturated hn a q m ?_⟩
      apply extendedParameter_localization_injective hn L
      simpa only [map_mul, map_pow] using hq
    · rintro ⟨q, rfl⟩
      exact ⟨0, q, by simp⟩
  rw [hex, extendedAmbientParameter, exists_aeval_add_one_iff,
    Algebra.adjoin_singleton_eq_range_aeval]
  change (∃ q : Polynomial ℂ, a = Polynomial.aeval (extendedF hn) q) ↔
    ∃ q : Polynomial ℂ, Polynomial.aeval (extendedF hn) q = a
  simp only [eq_comm]

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations

theorem solution {n : ℕ} (hn : 4 ≤ n)
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin n) ℂ) L]
    [IsLocalization.Away (extendedAmbientParameter hn) L] (a : MvPolynomial (Fin n) ℂ) :
    (∃ (m : ℕ) (q : Polynomial ℂ),
      (algebraMap (MvPolynomial (Fin n) ℂ) L (extendedAmbientParameter hn))^m *
          algebraMap (MvPolynomial (Fin n) ℂ) L a =
        algebraMap (MvPolynomial (Fin n) ℂ) L (Polynomial.aeval (extendedAmbientParameter hn) q)) ↔
    a ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)) := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.extendedParameter_laurent_intersection hn L a
    | exact OAI.AbhyankarSathaye.CommutingDerivations.extendedParameter_laurent_intersection
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.extendedParameter_laurent_intersection <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.extendedParameter_laurent_intersection <;> assumption)
