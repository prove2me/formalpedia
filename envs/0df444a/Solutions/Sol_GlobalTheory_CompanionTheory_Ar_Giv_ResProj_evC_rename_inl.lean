-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.evC_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:57.330218+00:00
-- url     : https://prove2.me/submissions/e8921060-0d79-4363-be78-d25311877b4b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin

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
theorem _root_.solution (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (f : MRing ι) :
    evC z (rename (joinInl ι ι₂) f) = evC (z ∘ joinInl ι ι₂) f := by
  unfold evC
  rw [map_rename, eval_rename]
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
