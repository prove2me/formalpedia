-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.InfScale.pi_const_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:51.085593+00:00
-- url     : https://prove2.me/submissions/51fdc20f-0b5a-4e3b-945e-4d4e8bb6ebfb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedean

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.InfScale
open GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.Equi.InfScale
theorem _root_.solution {X : Type} [MeasurableSpace X] (ι : Type) [Fintype ι] (μ : Measure X) [SigmaFinite μ]
    (c : ENNReal) [SigmaFinite (c • μ)] :
    (Measure.pi fun _ : ι => c • μ) = c ^ Fintype.card ι • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
end GlobalTheory.CompanionTheory.Equi.InfScale
