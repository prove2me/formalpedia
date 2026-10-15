-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:49:17.151053+00:00
-- url     : https://prove2.me/submissions/47bd9278-ad07-454f-a6d6-4bbff4a91d4f

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedLocalization.lean:L45-L60
-- (upload_full_project.md Phase 4): solution for node OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization. The node keeps its source
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

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedLocalization ----
namespace OAI

/-!
Localization coordinates in every dimension `n ≥ 4`.

The localization at `extendedF hn + 1` is a polynomial extension of the
four-dimensional localization, with an explicit structural map from the ambient ring.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

/-- This polynomial extension is the localization of the exact full ambient
ring at the powers of extendedF+1, with the displayed structural map. -/
theorem extended_isLocalization {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedAlgebra hn
    IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n) := by
  let := extendedAlgebra hn
  let : Algebra (MvPolynomial (Fin (n-4)) R) (ExtendedLocalizedAmbient n) :=
    MvPolynomial.algebraMvPolynomial
  have : IsLocalization ((Submonoid.powers ambientC).map
      (C : R →+* MvPolynomial (Fin (n-4)) R)) (ExtendedLocalizedAmbient n) :=
    MvPolynomial.isLocalization _ _
  apply IsLocalization.of_ringEquiv_left (splitAmbient hn).toRingEquiv
    (M₁ := (Submonoid.powers ambientC).map (C : R →+* MvPolynomial (Fin (n-4)) R))
  · simp [Submonoid.map_powers, splitAmbient_F, ambientC]
  · intro f
    rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- platform node ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem solution {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedAlgebra hn
    IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n) := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization hn
    | exact OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization <;> assumption)
