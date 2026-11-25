-- Prove2me | solution 1 for GlobalTheory.T.qminor_intertwining_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:18.466168+00:00
-- url     : https://prove2.me/submissions/ea11bd3d-764b-4506-a4a2-0913b81d370f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApply
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApplyStatement
import Theorems.Thm_GlobalTheory_qminor_intertwine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  first | exact @GlobalTheory.qminor_intertwine | exact GlobalTheory.qminor_intertwine | (intros; apply GlobalTheory.qminor_intertwine <;> assumption)
end _root_.GlobalTheory.T
