-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.isUnit_atPrime_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:37.254853+00:00
-- url     : https://prove2.me/submissions/752496f0-6c53-4004-af89-1206205a170d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_PlaceCompletion_mem_atPrime_iff

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
theorem _root_.solution (x : la.valuationSubringAtPrime K) :
    IsUnit x ↔ la.valuation K (x : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := (mem_atPrime_iff la ((u : la.valuationSubringAtPrime K) : K)).1 (u : la.valuationSubringAtPrime K).2
    have h2 := (mem_atPrime_iff la (((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K) : K)).1
      ((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K).2
    have hprod : la.valuation K ((u : la.valuationSubringAtPrime K) : K) *
        la.valuation K (((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K) : K) = 1 := by
      rw [← map_mul]
      have : ((u : la.valuationSubringAtPrime K) : K) *
          (((u⁻¹ : (la.valuationSubringAtPrime K)ˣ) : la.valuationSubringAtPrime K) : K) = 1 := by
        exact congrArg Subtype.val u.mul_inv
      rw [this, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = _ := hprod.symm
      _ ≤ la.valuation K ((u : la.valuationSubringAtPrime K) : K) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
    have hinv : (x : K)⁻¹ ∈ la.valuationSubringAtPrime K :=
      (mem_atPrime_iff la _).2 (by rw [map_inv₀, h, inv_one])
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
end GlobalTheory.PlaceCompletion
