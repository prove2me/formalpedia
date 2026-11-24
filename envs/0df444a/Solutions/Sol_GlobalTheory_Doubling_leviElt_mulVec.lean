-- Prove2me | solution 1 for GlobalTheory.Doubling.leviElt_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:43:03.651632+00:00
-- url     : https://prove2.me/submissions/3c29aa51-adfc-47c9-92a2-9989606d3b06

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_blkMat_mulVec
import Theorems.Thm_GlobalTheory_Doubling_cayley_mulVec
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
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
namespace GlobalTheory.Doubling
theorem _root_.solution (g : GL n A × GL n A) (x y : n → A) : (leviElt e g).1 *ᵥ pairVec e (x + y) (x - y) =
    pairVec e (g.1.1 *ᵥ x + g.2.1 *ᵥ y) (g.1.1 *ᵥ x - g.2.1 *ᵥ y) := by
  rw [← cayley_mulVec, ← cayley_mulVec, ← blkMat_mulVec, mulVec_mulVec, mulVec_mulVec, ← val_blkGL, ← Units.val_mul,
    ← Units.val_mul]
  simp [leviElt]
end GlobalTheory.Doubling
