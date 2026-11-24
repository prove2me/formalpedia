-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.isClosed_range_iotaHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:18.098964+00:00
-- url     : https://prove2.me/submissions/09b011f9-6ee6-4ca4-8084-44eeef6812aa

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mem_range_iff
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
theorem _root_.solution [T2Space (R ⊗[F] E)] (hs : s ≠ 0) :
    IsClosed (Set.range (iotaHom R σ J s)) := by
  have hp := (isEmbedding_pairMap R σ (blockOne s J)).continuous
  have e : Set.range (iotaHom R σ J s) =
      {h | (pairMap R σ (blockOne s J) h).1 0 0 = 1} ∩
        ⋂ i : Fin M, {h | (pairMap R σ (blockOne s J) h).1 i.succ 0 = 0} := by
    ext h
    have := mem_range_iff R σ J s hs h
    simp only [MonoidHom.mem_range] at this
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact this
  rw [e]
  refine IsClosed.inter (isClosed_eq (hp.fst.matrix_elem 0 0) continuous_const) ?_
  exact isClosed_iInter fun i => isClosed_eq (hp.fst.matrix_elem i.succ 0) continuous_const
end GlobalTheory.CompanionTheory.SW.StabFirst
