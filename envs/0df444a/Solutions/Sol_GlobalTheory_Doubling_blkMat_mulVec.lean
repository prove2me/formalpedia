-- Prove2me | solution 1 for GlobalTheory.Doubling.blkMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:22.122061+00:00
-- url     : https://prove2.me/submissions/426efd4d-4952-4b6a-afef-4fd1d69c5f09

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
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]
namespace GlobalTheory.Doubling
theorem _root_.solution (x : Matrix m m A) (y : Matrix n n A) (u : m → A) (v : n → A) :
    blkMat e x y *ᵥ pairVec e u v = pairVec e (x *ᵥ u) (y *ᵥ v) := by
  simp [mulVec_pairVec, submatrix_blkMat]
end GlobalTheory.Doubling
