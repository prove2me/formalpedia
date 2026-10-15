-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:58:43.491584+00:00
-- url     : https://prove2.me/submissions/183eb63d-1f20-4960-86b2-db8b7b9a521b

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/CoordinatePartials.lean:L67-L87
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero. The node keeps its source
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

/-- Exact coefficient consequence of the common-kernel condition. -/
theorem coefficient_eq_zero_of_all_partials_zero [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) (hp : ∀ i, pderiv i p = 0)
    (m : σ →₀ ℕ) (hm : m ≠ 0) : p.coeff m = 0 := by
  classical
  have hex : ∃ i, m i ≠ 0 := by
    by_contra hh
    apply hm
    ext i
    change m i = 0
    by_contra hi
    exact hh ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have he := congrArg (fun polynomial : MvPolynomial σ B =>
    polynomial.coeff (m - Finsupp.single i 1)) (hp i)
  rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi,
    MvPolynomial.coeff_zero] at he
  have hfactor : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : B) + 1 ≠ 0 := by
    rw [← Nat.cast_succ]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  exact (mul_eq_zero.mp he).resolve_right hfactor

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial
variable {B σ : Type*} [CommRing B]

theorem solution [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) (hp : ∀ i, pderiv i p = 0)
    (m : σ →₀ ℕ) (hm : m ≠ 0) : p.coeff m = 0 := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero p hp m hm
    | exact OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero <;> assumption)
