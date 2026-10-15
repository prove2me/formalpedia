-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:53:32.299456+00:00
-- url     : https://prove2.me/submissions/bf4141c1-15d9-4ff2-beaf-6337be7cce90

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/DenominatorDescent.lean:L18-L37
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image. The node keeps its source
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

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.DenominatorDescent ----
namespace OAI

/-!
A common exponent clears finitely many localized generator images.
Leibniz and polynomial induction extend the generator bounds to the full ring
and yield descended derivations.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K σ τ L : Type*} [CommRing K] [CommRing L]

/-- Leibniz extends a closure proof on the literal polynomial generators to
the whole polynomial ring. No finite-variable or domain assumption is needed. -/
theorem derivation_preserves_polynomial_image [Algebra K L]
    (ι : MvPolynomial σ K →ₐ[K] L) (D : Derivation K L L)
    (hX : ∀ j : σ, ∃ q : MvPolynomial σ K, ι q = D (ι (X j))) :
    ∀ p : MvPolynomial σ K, ∃ q : MvPolynomial σ K, ι q = D (ι p) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ?_⟩
      simp only [map_zero, algHom_C, Derivation.map_algebraMap]
  | add p q hp hq =>
      obtain ⟨dp, hdp⟩ := hp
      obtain ⟨dq, hdq⟩ := hq
      exact ⟨dp + dq, by simp only [map_add, hdp, hdq]⟩
  | mul_X p j hp =>
      obtain ⟨dp, hdp⟩ := hp
      obtain ⟨dj, hdj⟩ := hX j
      refine ⟨p * dj + X j * dp, ?_⟩
      simp only [map_add, map_mul, hdp, hdj, Derivation.leibniz, smul_eq_mul]

section Clearing
variable [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ K) L]

variable [Algebra K L] [IsScalarTower K (MvPolynomial σ K) L]

end Clearing
end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial
variable {K σ τ L : Type*} [CommRing K] [CommRing L]

theorem solution [Algebra K L]
    (ι : MvPolynomial σ K →ₐ[K] L) (D : Derivation K L L)
    (hX : ∀ j : σ, ∃ q : MvPolynomial σ K, ι q = D (ι (X j))) :
    ∀ p : MvPolynomial σ K, ∃ q : MvPolynomial σ K, ι q = D (ι p) := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image ι D hX
    | exact OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image <;> assumption)
