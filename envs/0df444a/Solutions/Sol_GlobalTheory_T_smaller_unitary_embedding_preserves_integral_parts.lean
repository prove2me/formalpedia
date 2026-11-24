-- Prove2me | solution 1 for GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:04:13.125331+00:00
-- url     : https://prove2.me/submissions/e84acfcb-b498-42f8-98ae-2e9e03c40b47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallerUnitaryEmbeddingPreservesIntegralParts
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallerUnitaryEmbeddingPreservesIntegralPartsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_embMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.SatakeWeyl.EmbMem := by
  first | exact @GlobalTheory.SatakeWeyl.embMem | exact GlobalTheory.SatakeWeyl.embMem | (intros; apply GlobalTheory.SatakeWeyl.embMem <;> assumption)
end _root_.GlobalTheory.T
