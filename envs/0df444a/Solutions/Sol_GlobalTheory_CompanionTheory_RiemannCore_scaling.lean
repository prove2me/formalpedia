-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:39.847313+00:00
-- url     : https://prove2.me/submissions/3566c866-b764-4aaa-ad78-8bf67f0920b0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution (μ : Measure G) {τ : G → G} (hτ : MeasurableEmbedding τ) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map τ μ = ENNReal.ofReal c • μ) {h : G → ℝ} (hh : Integrable h μ) :
    Integrable (fun y => h (τ y)) μ ∧ ∫ y, h (τ y) ∂μ = c * ∫ y, h y ∂μ := by
  constructor
  · have h1 : Integrable h (Measure.map τ μ) := by
      rw [hmap]; exact hh.smul_measure ENNReal.ofReal_ne_top
    exact hτ.integrable_map_iff.1 h1
  · rw [← hτ.integral_map, hmap, integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
end GlobalTheory.CompanionTheory.RiemannCore
