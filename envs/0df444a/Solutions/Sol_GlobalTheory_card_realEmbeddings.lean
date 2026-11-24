-- Prove2me | solution 1 for GlobalTheory.card_realEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:56.925246+00:00
-- url     : https://prove2.me/submissions/c72675fa-1ccf-4af7-98ae-365c74768e4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_bijective_ofRealHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
variable (F)
namespace GlobalTheory
theorem _root_.solution : Fintype.card (F →+* ℝ) = finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  exact Fintype.card_of_bijective (bijective_ofRealHom_comp F)
end GlobalTheory
