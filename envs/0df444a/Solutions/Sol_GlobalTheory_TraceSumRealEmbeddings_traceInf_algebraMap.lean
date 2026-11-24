-- Prove2me | solution 1 for GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:36.294509+00:00
-- url     : https://prove2.me/submissions/e93e6c44-6a6a-4015-beb0-5c42be12b826

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TraceInfAlgebraMap
import Theorems.Thm_GlobalTheory_TraceSumRealEmbeddings_sum_re_embeddings
import Theorems.Thm_GlobalTheory_TraceSumRealEmbeddings_trace_eq_sum_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceSumRealEmbeddings
open NumberField NumberField.InfinitePlace
namespace GlobalTheory.TraceSumRealEmbeddings
theorem _root_.solution (F : Type) [Field F] [NumberField F] (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) x) =
      ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_eq_sum_re, sum_re_embeddings]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
end GlobalTheory.TraceSumRealEmbeddings
