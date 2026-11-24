-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:41.427796+00:00
-- url     : https://prove2.me/submissions/fcb373e1-68d5-44ba-9f45-ec268e78d012

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]
variable (ι : R →+* K) (τ : K →+* K)
variable {ι τ}
namespace GlobalTheory.CompanionTheory.SW.LDL
theorem _root_.solution (ι : R →+* K) (τ : K →+* K) {n : ℕ} (d : Fin n → Rˣ) (u : Up n → K) :
    gram ι τ d u = cT τ (unip u) * Matrix.diagonal (fun i => ι (d i)) * unip u := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  rfl
end GlobalTheory.CompanionTheory.SW.LDL
