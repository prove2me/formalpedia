-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:57:54.454441+00:00
-- url     : https://prove2.me/submissions/4eadb37b-68c8-4cee-93d3-9f6c748074b1

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/CoordinatePartials.lean:L27-L46
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero. The node keeps its source
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
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.CoordinatePartials ----
namespace OAI

/-! The actual polynomial coordinate partials: commuting, locally nilpotent,
linearly independent over the polynomial ring, and with exact constant common
kernel in characteristic zero. No localization equivalence is assumed here. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {B σ : Type*} [CommRing B]

/-- Vanishing of all coefficients at exponent at least n implies annihilation
by the nth partial iterate. This works over every commutative ring. -/
theorem coordinate_partial_iterate_eq_zero (i : σ) (n : ℕ) (p : MvPolynomial σ B)
    (hp : ∀ m : σ →₀ ℕ, n ≤ m i → p.coeff m = 0) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[n] p = 0 := by
  classical
  induction n generalizing p with
  | zero =>
      apply MvPolynomial.ext
      intro m
      simpa using hp m (Nat.zero_le _)
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      apply ih
      intro m hm
      rw [coeff_pderiv]
      have hz : p.coeff (m + Finsupp.single i 1) = 0 := by
        apply hp
        simpa using Nat.succ_le_succ hm
      rw [hz, zero_mul]

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial
variable {B σ : Type*} [CommRing B]

theorem solution (i : σ) (n : ℕ) (p : MvPolynomial σ B)
    (hp : ∀ m : σ →₀ ℕ, n ≤ m i → p.coeff m = 0) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[n] p = 0 := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero i n p hp
    | exact OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero <;> assumption)
