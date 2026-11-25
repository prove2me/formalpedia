-- Prove2me | solution 1 for GlobalTheory.T.iInf_map_le_map_iInf_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:41.790919+00:00
-- url     : https://prove2.me/submissions/d0c8dbee-6661-4f1f-baeb-c4f28bbdf9f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlatStatement
import Theorems.Thm_GlobalTheory_FlatIdealInf_iInf_map_le_map_iInf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R] [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B), ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  first | exact @GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf | exact GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf | (intros; apply GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf <;> assumption)
end _root_.GlobalTheory.T
