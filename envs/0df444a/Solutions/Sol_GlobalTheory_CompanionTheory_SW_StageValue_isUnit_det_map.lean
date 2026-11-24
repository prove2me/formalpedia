-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.isUnit_det_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:32.395799+00:00
-- url     : https://prove2.me/submissions/6a3d5a48-bd14-4987-ac37-28075720b6c5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport

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
theorem _root_.solution (T : Matrix (Fin n) (Fin n) E) (hdet : T.det ≠ 0) :
    IsUnit (T.map (inclR (F := F) R)).det := by
  have h := (IsUnit.mk0 _ hdet).map (inclR (F := F) R)
  rw [RingHom.map_det] at h
  exact h
end GlobalTheory.CompanionTheory.SW.StageValue
