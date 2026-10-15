-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:54:40.350325+00:00
-- url     : https://prove2.me/submissions/e292fb5e-8c98-423d-9a8b-3236f878db0f

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/DenominatorDescent.lean:L43-L66
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound. The node keeps its source
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

section Clearing
variable [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ K) L]

/-- One exponent clears any finite collection of localization elements.
The proof selects actual numerators and takes the finite maximum of exponents.
It remains valid when the original coefficient ring has zero divisors. -/
theorem finite_localization_denominator_bound (c : MvPolynomial σ K)
    [IsLocalization.Away c L] (z : τ → σ → L) :
    ∃ N : ℕ, ∀ (i : τ) (j : σ), ∃ a : MvPolynomial σ K,
      algebraMap (MvPolynomial σ K) L a =
        (algebraMap (MvPolynomial σ K) L c)^N * z i j := by
  classical
  choose m a ha using fun ij : τ × σ => IsLocalization.Away.surj c (z ij.1 ij.2)
  let N : ℕ := Finset.univ.sup m
  refine ⟨N, ?_⟩
  intro i j
  have hle : m (i, j) ≤ N := Finset.le_sup (f := m) (Finset.mem_univ (i, j))
  refine ⟨c^(N - m (i, j)) * a (i, j), ?_⟩
  rw [map_mul, map_pow, ← ha (i, j)]
  calc
    (algebraMap (MvPolynomial σ K) L c)^(N - m (i, j)) *
        (z i j * (algebraMap (MvPolynomial σ K) L c)^m (i, j)) =
      (algebraMap (MvPolynomial σ K) L c)^(N - m (i, j) + m (i, j)) * z i j := by
        rw [pow_add]
        ring
    _ = (algebraMap (MvPolynomial σ K) L c)^N * z i j := by
        rw [Nat.sub_add_cancel hle]

variable [Algebra K L] [IsScalarTower K (MvPolynomial σ K) L]

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

theorem solution (c : MvPolynomial σ K)
    [IsLocalization.Away c L] (z : τ → σ → L) :
    ∃ N : ℕ, ∀ (i : τ) (j : σ), ∃ a : MvPolynomial σ K,
      algebraMap (MvPolynomial σ K) L a =
        (algebraMap (MvPolynomial σ K) L c)^N * z i j := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound c z
    | exact OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound <;> assumption)
