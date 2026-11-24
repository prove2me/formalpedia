-- Prove2me | solution 1 for GlobalTheory.RestrMeas.isHaarProdFin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:49.232012+00:00
-- url     : https://prove2.me/submissions/8594fce7-8a7f-4255-993c-011b9f0b173e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
namespace GlobalTheory.RestrMeas
theorem _root_.solution : IsHaarProdFin pf K μf μ ↔ (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧
    (∀ᶠ v in cofinite, μf v (K v) = 1) ∧
    ∀ S : Finset V, (∀ v ∉ S, μf v (K v) = 1) → ∀ B : ∀ v, Set (Yf v), (∀ v ∈ S, MeasurableSet (B v)) →
      μ {x | (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v} = ∏ v ∈ S, μf v (B v) := by
  simp [IsHaarProdFin, IsHaarProd, IsCylProd, cyl]
end GlobalTheory.RestrMeas
