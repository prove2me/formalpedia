-- Prove2me | solution 1 for GlobalTheory.T.parabolic_quotient_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:20:27.576282+00:00
-- url     : https://prove2.me/submissions/6c21154c-cdf2-4529-bedd-54d008407a35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicQuotientMeasure
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicQuotientMeasureStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_isHaarMeasure_map_splitHomeo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], (∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν) → (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)).IsHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo | exact GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo <;> assumption)
end _root_.GlobalTheory.T
