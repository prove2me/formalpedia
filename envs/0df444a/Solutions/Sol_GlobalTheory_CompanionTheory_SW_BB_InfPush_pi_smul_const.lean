-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.InfPush.pi_smul_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:52.926784+00:00
-- url     : https://prove2.me/submissions/df987d3e-0d41-4370-8dc3-6c1a86546240

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanCoordinateMeasureTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.InfPush
namespace GlobalTheory.CompanionTheory.SW.BB.InfPush
theorem _root_.solution {ι α : Type} [Fintype ι] [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi fun _ : ι => ν := by
  have : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    rw [← ENNReal.smul_def]; infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
end GlobalTheory.CompanionTheory.SW.BB.InfPush
