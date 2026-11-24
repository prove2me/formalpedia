-- Prove2me | solution 1 for GlobalTheory.JR.Step.isClosedEmbedding_embHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:43.150472+00:00
-- url     : https://prove2.me/submissions/02fbfe04-c299-40b2-8282-e0c04b696f6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneUnitaryGroupEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
namespace GlobalTheory.JR.Step
theorem _root_.solution (r : ℕ) (E : Type) [CommRing E] [TopologicalSpace E] [T2Space E] :
    Topology.IsClosedEmbedding (embHom r E) := by
  have hc : Continuous (embHom r E) := by
    change Continuous fun g : Matrix (Fin r) (Fin r) E =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
    exact (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _
  have hl : Function.LeftInverse
      (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) E => M.submatrix (Fin.castAdd 1) (Fin.castAdd 1))
      (embHom r E) := by
    intro g
    ext i j
    change (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
      (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = g i j
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  exact hl.isClosedEmbedding (continuous_id.matrix_submatrix _ _) hc
end GlobalTheory.JR.Step
