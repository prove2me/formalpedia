-- Prove2me | solution 1 for GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:53.883595+00:00
-- url     : https://prove2.me/submissions/a19b783a-ba2d-45e7-87fd-4749f0f02121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringComapEqNonunits

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
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution {K L : Type} [Field K] [Field L] (f : K →+* L)
    (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U ∧ ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
  classical
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  refine ⟨W, ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_comap]
    constructor
    · intro hx
      by_contra hxU
      have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
      have hinv : x⁻¹ ∈ U := (U.mem_or_inv_mem x).resolve_left hxU
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : U) := by
        intro hu
        obtain ⟨⟨y, hy⟩, hyx⟩ := isUnit_iff_exists_inv.mp hu
        have hyx' : x⁻¹ * y = 1 := congrArg Subtype.val hyx
        have : y = x := by
          calc y = x * (x⁻¹ * y) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hx0, _root_.one_mul]
            _ = x := by rw [hyx', _root_.mul_one]
        exact hxU (this ▸ hy)
      apply hnu
      apply (hloc.map_nonunit (⟨x⁻¹, hinv⟩ : U))
      refine isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, ?_⟩
      apply Subtype.ext
      change f x⁻¹ * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    · intro hx
      exact hW ⟨x, hx⟩
  · intro x hx
    obtain ⟨hxU, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx
    have hfx : f x ∈ W := hW ⟨x, hxU⟩
    have key : (⟨f x, hfx⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hmax
      exact hloc.map_nonunit (⟨x, hxU⟩ : U) hu
    exact (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hfx, key⟩
end GlobalTheory.Reg
