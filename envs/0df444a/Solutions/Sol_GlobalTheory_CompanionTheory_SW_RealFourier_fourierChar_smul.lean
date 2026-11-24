-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealFourier.fourierChar_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:49.228678+00:00
-- url     : https://prove2.me/submissions/7910b237-a741-4f67-8a78-3d38c41fb17c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LebesgueSelfdualForDotCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealFourier
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.RealFourier
theorem _root_.solution (t : ℝ) (c : ℂ) :
    (Real.fourierChar t : Circle) • c = c * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring
end GlobalTheory.CompanionTheory.SW.RealFourier
