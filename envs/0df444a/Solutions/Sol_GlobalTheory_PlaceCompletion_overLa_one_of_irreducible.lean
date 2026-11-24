-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.overLa_one_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:29:26.118859+00:00
-- url     : https://prove2.me/submissions/0fe8e513-3591-4a82-a9e8-1d9c7c237a45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_algebraMap_of_isUnit
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_algebraMap_of_irreducible
import Theorems.Thm_GlobalTheory_PlaceCompletion_isUnit_atPrime_iff
import Theorems.Thm_GlobalTheory_PlaceCompletion_valuation_of_irreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.PlaceCompletion
open scoped WithZero
section Val
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
end Val
section Place
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
private theorem valV_algebraMap_eq_valuation {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    (o : la.valuationSubringAtPrime K →+* V) {π : la.valuationSubringAtPrime K}
    (hπ : Irreducible π) (hoπ : Irreducible (o π)) (x : la.valuationSubringAtPrime K) :
    valV V (algebraMap V K' (o x)) = la.valuation K (x : K) := by
  by_cases hx : x = 0
  · subst hx
    simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hc : (((u : la.valuationSubringAtPrime K) * π ^ n : la.valuationSubringAtPrime K) : K) =
      ((u : la.valuationSubringAtPrime K) : K) * (π : K) ^ n := by
    rfl
  rw [hc]
  simp only [map_mul, map_pow]
  rw [valV_algebraMap_of_isUnit (u.isUnit.map o), valV_algebraMap_of_irreducible hoπ,
    (isUnit_atPrime_iff la _).1 u.isUnit, valuation_of_irreducible la hπ]
private theorem valV_ringHom_eq_valuation {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    (j : K →+* K') (o : la.valuationSubringAtPrime K →+* V)
    (ho : ∀ x, algebraMap V K' (o x) = j x) {π : la.valuationSubringAtPrime K}
    (hπ : Irreducible π) (hoπ : Irreducible (o π)) (a : K) :
    valV V (j a) = la.valuation K a := by
  rcases ValuationSubring.mem_or_inv_mem (la.valuationSubringAtPrime K) a with h | h
  · have key := valV_algebraMap_eq_valuation la (K' := K') o hπ hoπ ⟨a, h⟩
    rw [ho] at key
    exact key
  · have key := valV_algebraMap_eq_valuation la (K' := K') o hπ hoπ ⟨a⁻¹, h⟩
    rw [ho] at key
    change valV V (j a⁻¹) = la.valuation K a⁻¹ at key
    rw [map_inv₀, map_inv₀, map_inv₀] at key
    exact inv_injective key
variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
end Place
end GlobalTheory.PlaceCompletion
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
namespace GlobalTheory.PlaceCompletion
theorem _root_.solution [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    (j : K →+* K') (o : la.valuationSubringAtPrime K →+* V)
    (ho : ∀ x, algebraMap V K' (o x) = j x) {π : la.valuationSubringAtPrime K}
    (hπ : Irreducible π) (hoπ : Irreducible (o π)) : OverLa la V j 1 := by
  have hall := valV_ringHom_eq_valuation la j o ho hπ hoπ
  unfold OverLa vV vLa
  refine ⟨Nat.one_pos, fun a => ?_⟩
  rw [hall a, Nat.cast_one, _root_.one_mul]
end GlobalTheory.PlaceCompletion
