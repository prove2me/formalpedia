-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocGauss.ofReal_inv_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:27:54.545792+00:00
-- url     : https://prove2.me/submissions/80bd6bcb-6a07-437e-8675-56c7faeed869

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGramFiberContinuousDensity

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocGauss
namespace GlobalTheory.CompanionTheory.SW.LocGauss
theorem _root_.solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hab : a ≤ c * b)
    (N : ℕ) : ENNReal.ofReal ((b ^ N)⁻¹) ≤
      ((c ^ N).toNNReal : ℝ≥0∞) * ENNReal.ofReal ((a ^ N)⁻¹) := by
  have h1 : (b ^ N)⁻¹ ≤ c ^ N * (a ^ N)⁻¹ := by
    have h2 : a ^ N ≤ c ^ N * b ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ ha.le hab N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc ENNReal.ofReal ((b ^ N)⁻¹) ≤ ENNReal.ofReal (c ^ N * (a ^ N)⁻¹) :=
        ENNReal.ofReal_le_ofReal h1
    _ = _ := ENNReal.ofReal_mul (by positivity)
end GlobalTheory.CompanionTheory.SW.LocGauss
