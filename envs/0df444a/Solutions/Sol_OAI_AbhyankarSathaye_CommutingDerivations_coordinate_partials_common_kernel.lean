-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:01:58.222465+00:00
-- url     : https://prove2.me/submissions/e3269c25-d113-4310-b28e-9ac923393641

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/CoordinatePartials.lean:L89-L105
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel. The node keeps its source
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
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_coefficient_eq_zero_of_all_partials_zero

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.CoordinatePartials ----
namespace OAI

/-! The actual polynomial coordinate partials: commuting, locally nilpotent,
linearly independent over the polynomial ring, and with exact constant common
kernel in characteristic zero. No localization equivalence is assumed here. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {B σ : Type*} [CommRing B]

/-- The common kernel is literally the coefficient ring, with witness equal
to the constant coefficient. In particular this applies to Laurent coefficients
over C, once that coefficient algebra's domain and characteristic are installed. -/
theorem coordinate_partials_common_kernel [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) :
    (∀ i, pderiv i p = 0) ↔ ∃ b : B, p = C b := by
  classical
  constructor
  · intro hp
    refine ⟨p.coeff 0, ?_⟩
    ext m
    by_cases hm : m = 0
    · subst m
      simp
    · rw [coefficient_eq_zero_of_all_partials_zero p hp m hm, coeff_C_of_ne_zero hm]
  · rintro ⟨b, rfl⟩ i
    exact pderiv_C

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial
variable {B σ : Type*} [CommRing B]

theorem solution [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) :
    (∀ i, pderiv i p = 0) ↔ ∃ b : B, p = C b := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel p
    | exact OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel <;> assumption)
