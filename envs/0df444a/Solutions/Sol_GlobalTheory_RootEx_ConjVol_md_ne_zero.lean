-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.md_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:43.125934+00:00
-- url     : https://prove2.me/submissions/edf419ce-ab62-4336-9eb0-b2aa5ad8e248

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
theorem _root_.solution (g : Subgroup.normalizer (U : Set G)) : md U g ≠ 0 := (mulEquivHaarChar_pos _).ne'
end GlobalTheory.RootEx.ConjVol
