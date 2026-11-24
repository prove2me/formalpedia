-- Prove2me | solution 1 for GlobalTheory.Doubling.hform_dblGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:40:43.976262+00:00
-- url     : https://prove2.me/submissions/b9ac2e7a-8c07-4e8d-8481-9a03807c08c1

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
variable [Fintype n] [Fintype ι]
namespace GlobalTheory.Doubling
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (x y x' y' : n → A) :
    hform σ (dblGram e J) (pairVec e x y) (pairVec e x' y') = hform σ J x x' - hform σ J y y' := by
  simp [hform, ← e.sum_comp, dblGram, blkMat, sub_eq_add_neg]
end GlobalTheory.Doubling
