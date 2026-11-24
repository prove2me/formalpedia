-- Prove2me | solution 1 for GlobalTheory.T.averagedFibreMeasure_compl_fibre_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:49.47051+00:00
-- url     : https://prove2.me/submissions/13ee789d-e9e3-4228-b183-5bb549c5c400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AveragedFibreMeasureComplFibreEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AveragedFibreMeasureComplFibreEqZeroStatement
import Theorems.Thm_GlobalTheory_QuadFibre_fibOf_compl_fibre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  first | exact @GlobalTheory.QuadFibre.fibOf_compl_fibre | exact GlobalTheory.QuadFibre.fibOf_compl_fibre | (intros; apply GlobalTheory.QuadFibre.fibOf_compl_fibre <;> assumption)
end _root_.GlobalTheory.T
