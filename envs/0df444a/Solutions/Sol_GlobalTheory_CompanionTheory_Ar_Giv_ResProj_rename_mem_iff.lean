-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.rename_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:05.597847+00:00
-- url     : https://prove2.me/submissions/9cb96f76-44de-4d9b-8c4a-57ae5ebecee3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_cone_rename_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) (f : MRing ι) :
    rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y y₂) ↔ f ∈ mCoordIdeal y := by
  have h1 := AlgHom.congr_fun (cone_rename_inl y y₂) f
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h1
  unfold mCoordIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  show mConeMap (joinVec y y₂) (rename (joinInl ι ι₂) f) = 0 ↔ mConeMap y f = 0
  rw [h1]
  exact ⟨fun h => rename_injective _ Sum.inl_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
