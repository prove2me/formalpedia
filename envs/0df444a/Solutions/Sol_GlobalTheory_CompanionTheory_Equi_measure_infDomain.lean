-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.measure_infDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:52.823853+00:00
-- url     : https://prove2.me/submissions/257d4406-3a7d-44e4-837a-a973f93e1222

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_measurable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_map_coord_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_measurePreserving_toMixed


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi
open GlobalTheory.CompanionTheory.SW.RealCoord
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.CompanionTheory.Equi
theorem _root_.solution (li : Measure (Ainf F)) (hl : IsStdInf li) : li (infDomain F) = 1 := by
  have hfd := ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)
  have hmeas := (measurePreserving_toMixed F).measurable hfd
  have hpos : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))
  have hv : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
      one_mul, ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  calc li (infDomain F)
      = (li.map (coord F)) (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
        (Measure.map_apply (coord_measurable F) hmeas).symm
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [map_coord_eq F li hl, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [(measurePreserving_toMixed F).measure_preimage hfd.nullMeasurableSet]
    _ = 1 := by
        rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_mul_cancel₀ hpos.ne',
          ENNReal.ofReal_one]
end GlobalTheory.CompanionTheory.Equi
