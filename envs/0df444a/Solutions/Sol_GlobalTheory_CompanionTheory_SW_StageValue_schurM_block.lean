-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.schurM_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:34.576576+00:00
-- url     : https://prove2.me/submissions/7e61ecbb-5d4e-4554-9d8d-6189ae9227bd

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_cvec_block

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
theorem _root_.solution (T : Matrix (Fin n) (Fin n) E) :
    schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) = T.map (inclR R) := by
  ext i j
  have hc := cvec_block R t a T
  simp only [schurM, hc, Pi.zero_apply, map_zero, zero_mul, sub_zero]
  simp [blockOne]
end GlobalTheory.CompanionTheory.SW.StageValue
