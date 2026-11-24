-- Prove2me | solution 1 for GlobalTheory.Doubling.leviMat_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:11.38781+00:00
-- url     : https://prove2.me/submissions/13b807c1-60e1-4099-b5bc-0f5585782f13

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
namespace GlobalTheory.Doubling
theorem _root_.solution (f : A →+* B) (M : Matrix ι ι A) : leviMat e (M.map f) = (leviMat e M).map f := by
  ext i j; simp [leviMat, toBlocks₁₁, toBlocks₁₂]
end GlobalTheory.Doubling
