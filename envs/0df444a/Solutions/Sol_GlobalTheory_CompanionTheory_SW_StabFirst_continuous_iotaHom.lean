-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.continuous_iotaHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:07.167764+00:00
-- url     : https://prove2.me/submissions/8172d822-9bee-4a95-948e-009dc118d1f0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_continuous_blockOne
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_isEmbedding_pairMap

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution : Continuous (iotaHom R σ J s) := by
  rw [(isEmbedding_pairMap R σ (blockOne s J)).isInducing.continuous_iff]
  have hp := (isEmbedding_pairMap R σ J).continuous
  have : pairMap R σ (blockOne s J) ∘ iotaHom R σ J s = fun u =>
      (blockOne 1 (pairMap R σ J u).1,
        MulOpposite.op (blockOne 1 (MulOpposite.unop (pairMap R σ J u).2))) := rfl
  rw [this]
  exact (continuous_blockOne.comp hp.fst).prodMk
    (MulOpposite.continuous_op.comp
      (continuous_blockOne.comp (MulOpposite.continuous_unop.comp hp.snd)))
end GlobalTheory.CompanionTheory.SW.StabFirst
