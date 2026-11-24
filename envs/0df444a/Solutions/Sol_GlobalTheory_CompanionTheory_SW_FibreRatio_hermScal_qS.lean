-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.hermScal_qS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:48.746226+00:00
-- url     : https://prove2.me/submissions/6486a819-1579-4c22-a94d-4bcca95072bc

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
theorem _root_.solution (h : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (qS R σ S) = S := by
  have hfix : sigR R σ ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) =
      (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 := S.2 0 0
  obtain ⟨r, hr⟩ := fixed_tmul R h _ hfix
  have hq : qS R σ S = r := by
    unfold qS
    rw [hr]
    exact half_trace_tmul R h r
  apply Subtype.ext
  funext a c
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : c = 0 := Subsingleton.elim _ _
  rw [hq, hr]
  rfl
end GlobalTheory.CompanionTheory.SW.FibreRatio
