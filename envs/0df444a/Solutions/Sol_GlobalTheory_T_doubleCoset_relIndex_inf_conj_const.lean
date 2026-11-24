-- Prove2me | solution 1 for GlobalTheory.T.doubleCoset_relIndex_inf_conj_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:29.428878+00:00
-- url     : https://prove2.me/submissions/72ab8b9d-d787-4608-b9f5-28d2a16ad537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConstStatement
import Theorems.Thm_GlobalTheory_doubleCoset_relIndex_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  first | exact @GlobalTheory.doubleCoset_relIndex_const | exact GlobalTheory.doubleCoset_relIndex_const | (intros; apply GlobalTheory.doubleCoset_relIndex_const <;> assumption)
end _root_.GlobalTheory.T
