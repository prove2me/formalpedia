-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimInf.exists_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:33.850421+00:00
-- url     : https://prove2.me/submissions/f9d4aced-b75b-4b67-831c-ed38709f40fb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimInf
theorem _root_.solution (w : InfinitePlace F) : ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = w.embedding := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : E →ₐ[F] ℂ).commutes x
end GlobalTheory.CompanionTheory.SW.PrimInf
