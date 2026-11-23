-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitProdAlg.mulSupport_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:19.197314+00:00
-- url     : https://prove2.me/submissions/0b49a9f0-5095-456c-a512-2551ebed83b9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg
theorem _root_.solution {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    (Function.mulSupport c).Finite := by
  have := h.1
  rw [Filter.eventually_cofinite] at this
  exact this
end GlobalTheory.CompanionTheory.SW.UnitProdAlg
