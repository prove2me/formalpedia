-- Prove2me | solution 1 for GlobalTheory.NormCurve.exists_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:32.575741+00:00
-- url     : https://prove2.me/submissions/05b7dceb-10ff-4851-b80e-a5704d1bb4c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint
import Theorems.Thm_GlobalTheory_exists_prime_le_notMem_ringKrullDim_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.NormCurve
namespace GlobalTheory.NormCurve
theorem _root_.solution (k : Type) {B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) (hm : m.IsMaximal) (h : B) (h0 : h ≠ 0) :
    ∃ p : Ideal B, p.IsPrime ∧ p ≤ m ∧ h ∉ p ∧ ringKrullDim (B ⧸ p) ≤ 1 := by
  by_cases hh : h ∈ m
  · obtain ⟨p, h1, h2, h3, h4⟩ := exists_prime_le_notMem_ringKrullDim_eq_one k B m h hm h0 hh
    exact ⟨p, h1, h2, h3, h4.le⟩
  · refine ⟨m, hm.isPrime, le_rfl, hh, ?_⟩
    letI := Ideal.Quotient.field m
    rw [ringKrullDim_eq_zero_of_field]
    exact zero_le_one
end GlobalTheory.NormCurve
