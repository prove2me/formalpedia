-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.valuation_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:48.953574+00:00
-- url     : https://prove2.me/submissions/0d7f227b-69b2-48f6-884b-4d9240da79e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_PlaceCompletion_mem_atPrime_iff
import Theorems.Thm_GlobalTheory_PlaceCompletion_isUnit_atPrime_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
namespace GlobalTheory.PlaceCompletion
theorem _root_.solution [IsDiscreteValuationRing (la.valuationSubringAtPrime K)]
    {π : la.valuationSubringAtPrime K} (hπ : Irreducible π) :
    la.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := la.valuation_exists_uniformizer K
  have hle : ϖ ∈ la.valuationSubringAtPrime K := (mem_atPrime_iff la ϖ).2 (by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  have hnu : ¬ IsUnit (⟨ϖ, hle⟩ : la.valuationSubringAtPrime K) := fun hu => by
    have := (isUnit_atPrime_iff la _).1 hu
    rw [show ((⟨ϖ, hle⟩ : la.valuationSubringAtPrime K) : K) = ϖ from rfl, hϖ,
      WithZero.exp_eq_one] at this
    norm_num at this
  have hm : (⟨ϖ, hle⟩ : la.valuationSubringAtPrime K) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton'] at hm
  obtain ⟨a, ha⟩ := hm
  have hprod : la.valuation K (a : K) * la.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
    rw [← map_mul, ← hϖ]
    exact congrArg _ (congrArg Subtype.val ha)
  have hp0 : la.valuation K (π : K) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hprod; exact WithZero.exp_ne_zero hprod.symm
  have hq0 : la.valuation K (a : K) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hprod; exact WithZero.exp_ne_zero hprod.symm
  have hp1 : la.valuation K (π : K) < 1 := lt_of_le_of_ne ((mem_atPrime_iff la _).1 π.2)
    (fun h1 => hπ.not_isUnit ((isUnit_atPrime_iff la π).2 h1))
  have hq1 : la.valuation K (a : K) ≤ 1 := (mem_atPrime_iff la _).1 a.2
  have hlog := congrArg WithZero.log hprod
  rw [WithZero.log_mul hq0 hp0, WithZero.log_exp] at hlog
  have hlp : WithZero.log (la.valuation K (π : K)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hp0, WithZero.exp_zero]; exact hp1
  have hlq : WithZero.log (la.valuation K (a : K)) ≤ 0 := by
    rw [WithZero.log_le_iff_le_exp hq0, WithZero.exp_zero]; exact hq1
  rw [← WithZero.exp_log hp0]
  congr 1
  omega
end GlobalTheory.PlaceCompletion
