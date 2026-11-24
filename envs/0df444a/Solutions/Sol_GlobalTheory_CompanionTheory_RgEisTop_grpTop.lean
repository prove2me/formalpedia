-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTop.grpTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:17.48708+00:00
-- url     : https://prove2.me/submissions/6dfb9fe7-533c-42f5-83d8-9cdf88b4b5d0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_generalLinear_t2Space
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_gl_locallyCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_gl_secondCountable
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_isClosed_uSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTop
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEisTop
theorem _root_.solution : PositivityTheory.RgEis.GrpTop := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ ε
  have hc := isClosed_uSub A hA.σcont ε ι
  have hce : IsClosedEmbedding (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) :=
    hc.isClosedEmbedding_subtypeVal
  have := generalLinear_t2Space R (ι ⊕ ι)
  have := gl_locallyCompact R (ι ⊕ ι)
  have := gl_secondCountable R (ι ⊕ ι)
  refine ⟨generalLinear_t2Space R ι, gl_locallyCompact R ι, gl_secondCountable R ι, hce.isEmbedding.t2Space,
    hce.locallyCompactSpace, hce.isEmbedding.secondCountableTopology, ?_⟩
  exact hce.isCompact_preimage (hA.toGoodL.kcpt (ι ⊕ ι))
end GlobalTheory.CompanionTheory.RgEisTop
