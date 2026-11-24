-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.mul_ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:27.566395+00:00
-- url     : https://prove2.me/submissions/f5fdf97e-d0df-4491-97c4-36df963f1b40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution {e f : K} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (α β γ δ : L) :
    (α • e + β • f) * (γ • e + δ • f) = (α * γ) • e + (β * δ) • f := by
  simp only [Algebra.smul_def, map_mul]
  linear_combination (algebraMap L K α * algebraMap L K γ) * he +
    (algebraMap L K β * algebraMap L K δ) * hf +
    (algebraMap L K α * algebraMap L K δ + algebraMap L K β * algebraMap L K γ) * hef
end GlobalTheory.CompanionTheory.SW.PrimGood
