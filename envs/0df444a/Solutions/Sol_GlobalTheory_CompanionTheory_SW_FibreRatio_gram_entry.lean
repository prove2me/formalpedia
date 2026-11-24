-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.gram_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:58.094855+00:00
-- url     : https://prove2.me/submissions/5f3727bb-04ef-4f23-b9e0-6b79eb4c46b3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_fixed_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_half_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_sigR_hR_self
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_half_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_half_trace_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreRatio
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [Field R] [Algebra F R]
variable {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.CompanionTheory.SW.FibreRatio
theorem _root_.solution (h : IsCMExt F E σ) (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    gramR R σ J X 0 0 =
      (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) ⊗ₜ[F] (1 : E) := by
  obtain ⟨r, hr⟩ := fixed_tmul R h (gramR R σ J X 0 0) (sigR_hR_self R h hJ (X 0))
  rw [hr, half_trace_tmul R h r]
end GlobalTheory.CompanionTheory.SW.FibreRatio
