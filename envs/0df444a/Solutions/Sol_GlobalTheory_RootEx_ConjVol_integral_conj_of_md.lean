-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.integral_conj_of_md
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:25.709568+00:00
-- url     : https://prove2.me/submissions/27609cfe-5bca-42c4-81ba-68766e6a39b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G) [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U]
namespace GlobalTheory.RootEx.ConjVol
theorem _root_.solution (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular]
    (g : Subgroup.normalizer (U : Set G)) (hg : md U g = 1) (f : G → ℂ) :
    ∫ u : U, f (g * (u : G) * (g : G)⁻¹) ∂μ = ∫ u : U, f u ∂μ := by
  have h := mulEquivHaarChar_smul_map μ (cj U g)
  rw [show mulEquivHaarChar (cj U g) = 1 from hg, one_smul] at h
  have h3 := integral_map_equiv (μ := μ) (cj U g).toHomeomorph.toMeasurableEquiv (fun u : U => f u)
  rw [show ⇑(cj U g).toHomeomorph.toMeasurableEquiv = ⇑(cj U g) from rfl, h] at h3
  exact h3.symm
end GlobalTheory.RootEx.ConjVol
