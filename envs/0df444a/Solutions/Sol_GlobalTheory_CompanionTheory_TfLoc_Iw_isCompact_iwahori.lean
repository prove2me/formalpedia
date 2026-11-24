-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.isCompact_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:54.189597+00:00
-- url     : https://prove2.me/submissions/eaa99785-f4be-4fe5-8346-43fdb5d242ba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_mem_unitGL_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isClopen_iwahori
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isCompact_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution : IsCompact (iwahori (m := m) F) := by
  have hK := isCompact_integral (F := F) (m := m)
  have hK' := hK.image MulOpposite.continuous_op
  have hc := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) F)).isCompact_preimage (hK.prod hK')
  refine hc.of_isClosed_subset isClopen_iwahori.isClosed fun g hg => ?_
  have h := (mem_unitGL_iff g).1 hg.1
  exact ⟨h.1, ⟨_, h.2, rfl⟩⟩
end GlobalTheory.CompanionTheory.TfLoc.Iw
