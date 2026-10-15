-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:55:19.575892+00:00
-- url     : https://prove2.me/submissions/df73d386-7d18-4cf5-9b7f-2c3cda1de938

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/DenominatorDescent.lean:L70-L94
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent. The node keeps its source
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
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_derivation_preserves_polynomial_image
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_finite_localization_denominator_bound

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.DerivationOperations ----
namespace OAI

/-!
Transport, scaling, and descent of derivations through algebra homomorphisms.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- Existence of descent from the precise closure obligation. -/
theorem exists_descendDerivation (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (hstable : ∀ a : A, ∃ b : A, ι b = D (ι a)) :
    ∃ d : Derivation K A A, ∀ a, ι (d a) = D (ι a) := by
  choose d hd using hstable
  exact ⟨descendDerivation ι hι D d hd, hd⟩

end AbhyankarSathaye.CommutingDerivations

end

end OAI

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

section Clearing
variable [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ K) L]

variable [Algebra K L] [IsScalarTower K (MvPolynomial σ K) L]

/-- Construct descended derivations with a common clearing exponent,
assuming injectivity of the localization map. -/
theorem exists_common_denominator_descent (c : MvPolynomial σ K)
    [IsLocalization.Away c L]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ K) L))
    (D : τ → Derivation K L L) :
    ∃ (N : ℕ) (d : τ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)),
      ∀ (i : τ) (p : MvPolynomial σ K),
        algebraMap (MvPolynomial σ K) L (d i p) =
          (algebraMap (MvPolynomial σ K) L c)^N *
            D i (algebraMap (MvPolynomial σ K) L p) := by
  let ι : MvPolynomial σ K →ₐ[K] L := IsScalarTower.toAlgHom K (MvPolynomial σ K) L
  obtain ⟨N, hN⟩ := finite_localization_denominator_bound c
    (fun i j => D i (algebraMap (MvPolynomial σ K) L (X j)))
  have hstable (i : τ) : ∀ p : MvPolynomial σ K,
      ∃ q : MvPolynomial σ K, ι q =
        ((algebraMap (MvPolynomial σ K) L c)^N • D i) (ι p) := by
    apply derivation_preserves_polynomial_image ι
    intro j
    simpa [ι, Derivation.smul_apply, smul_eq_mul] using hN i j
  choose d hd using fun i => exists_descendDerivation ι hinj
    ((algebraMap (MvPolynomial σ K) L c)^N • D i) (hstable i)
  refine ⟨N, d, ?_⟩
  intro i p
  simpa [ι, Derivation.smul_apply, smul_eq_mul] using hd i p

end Clearing
end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial
variable {K σ τ L : Type*} [CommRing K] [CommRing L]
variable [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ K) L]
variable [Algebra K L] [IsScalarTower K (MvPolynomial σ K) L]

theorem solution (c : MvPolynomial σ K)
    [IsLocalization.Away c L]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ K) L))
    (D : τ → Derivation K L L) :
    ∃ (N : ℕ) (d : τ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)),
      ∀ (i : τ) (p : MvPolynomial σ K),
        algebraMap (MvPolynomial σ K) L (d i p) =
          (algebraMap (MvPolynomial σ K) L c)^N *
            D i (algebraMap (MvPolynomial σ K) L p) := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent c hinj D
    | exact OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent <;> assumption)
