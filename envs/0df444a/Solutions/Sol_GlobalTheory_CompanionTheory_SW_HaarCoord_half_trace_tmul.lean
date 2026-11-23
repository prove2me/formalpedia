-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.half_trace_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:11.746857+00:00
-- url     : https://prove2.me/submissions/ab205c7d-c3d5-421a-a97b-3d80274ac4d6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_half_add_self

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution [CharZero F] (h2 : Module.finrank F E = 2) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let B : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  have : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [this, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R B)]
  simp only [Fintype.card_fin, two_nsmul]
  exact half_add_self (F := F) R s
end GlobalTheory.CompanionTheory.SW.HaarCoord
