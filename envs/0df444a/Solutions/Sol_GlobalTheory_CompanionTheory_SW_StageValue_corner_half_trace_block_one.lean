-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.corner_half_trace_block_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:08.115902+00:00
-- url     : https://prove2.me/submissions/74e2715a-3947-4510-b9da-d9ae6b533de0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_one_tmul_algebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_corner_half_trace_eq_of_pure_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StageValue
theorem _root_.solution [CharZero F] (hfr : Module.finrank F E = 2) (T : Matrix (Fin n) (Fin n) E) :
    s0 R ((blockOne (algebraMap F E t) T).map (inclR (F := F) R)) = algebraMap F R t := by
  apply corner_half_trace_eq_of_pure_tensor R hfr
  rw [← one_tmul_algebraMap]
  rfl
end GlobalTheory.CompanionTheory.SW.StageValue
