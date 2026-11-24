-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.md_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:37.479844+00:00
-- url     : https://prove2.me/submissions/09ed953d-30c5-481b-b14a-e9ca708cd25b

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
theorem _root_.solution (x g : Subgroup.normalizer (U : Set G)) : md U (x * g * x⁻¹) = md U g := by
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]
end GlobalTheory.RootEx.ConjVol
