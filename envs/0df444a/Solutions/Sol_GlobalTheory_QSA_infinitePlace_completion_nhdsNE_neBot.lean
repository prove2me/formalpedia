-- Prove2me | solution 1 for GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:09.937605+00:00
-- url     : https://prove2.me/submissions/1e373838-d43f-422d-af1c-8b531edf2752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfinitePlaceCompletionNhdsNEZeroNeBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA
namespace GlobalTheory.QSA
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  intro F _ _ w
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    have := (AddMonoidHomClass.isometry_iff_norm _).1 hiso (2 : w.Completion)
    rw [← this, map_ofNat]; simp
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by rw [h2]; norm_num⟩ }
  exact NormedField.nhdsNE_neBot (0 : w.Completion)
end GlobalTheory.QSA
