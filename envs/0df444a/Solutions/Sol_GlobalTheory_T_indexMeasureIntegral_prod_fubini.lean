-- Prove2me | solution 1 for GlobalTheory.T.indexMeasureIntegral_prod_fubini
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:15.559619+00:00
-- url     : https://prove2.me/submissions/c0c37f23-c82f-4a68-a80a-da37b035fd36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubiniStatement
import Theorems.Thm_GlobalTheory_IdxInt_Fubini_cint_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ), Nice (A.prod A') φ → (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧ cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  first | exact @GlobalTheory.IdxInt.Fubini.cint_prod | exact GlobalTheory.IdxInt.Fubini.cint_prod | (intros; apply GlobalTheory.IdxInt.Fubini.cint_prod <;> assumption)
end _root_.GlobalTheory.T
