-- Prove2me | solution 1 for GlobalTheory.exists_etale_int_surjective_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:57.978428+00:00
-- url     : https://prove2.me/submissions/d3aa9070-8305-44bb-845d-ad2cfbb5b2cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [Finite K] :
    ∃ (A : Type) (_ : CommRing A) (β : A →+* K),
      (Int.castRingHom A).Etale ∧ Function.Surjective β := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  let f : ℤ[X] := X ^ (Fintype.card K - 1) - C 1
  let P : StandardEtalePair ℤ :=
    ⟨f, monic_X_pow_sub_C _ (by omega), derivative f, 1, 0, 1, by simp⟩
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Kˣ)
  have h1 : (α : K) ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ α.ne_zero
  have hm : P.HasMap (α : K) := by
    refine ⟨by simp [P, f, h1], ?_⟩
    have : ((Fintype.card K - 1 : ℕ) : K) = -1 := by
      rw [Nat.cast_sub hq.le]; simp
    simp [P, f, derivative_X_pow, this]
  refine ⟨P.Ring, inferInstance, (P.lift _ hm).toRingHom, ?_, fun k => ?_⟩
  · have : Int.castRingHom P.Ring = algebraMap ℤ P.Ring := RingHom.ext_int _ _
    rw [this]
    exact RingHom.etale_algebraMap.mpr inferInstance
  · by_cases hk : k = 0
    · exact ⟨0, by simp [hk]⟩
    · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hα (Units.mk0 k hk)))
      refine ⟨P.X ^ n, ?_⟩
      have := congrArg Units.val hn
      simpa using this
end GlobalTheory
