-- Prove2me | solution 1 for GlobalTheory.Doubling.continuous_blkGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:24:55.819705+00:00
-- url     : https://prove2.me/submissions/5fef6781-3f0a-440d-bd19-e66204bd6fab

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]
namespace GlobalTheory.Doubling
theorem _root_.solution [TopologicalSpace A] : Continuous (blkGL (A := A) e) := by
  have h : Continuous fun p : Matrix m m A × Matrix n n A => blkMat e p.1 p.2 :=
    (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_submatrix _ _
  exact Units.continuous_iff.2 ⟨h.comp ((Units.continuous_val.comp continuous_fst).prodMk
    (Units.continuous_val.comp continuous_snd)), h.comp ((Units.continuous_coe_inv.comp continuous_fst).prodMk
    (Units.continuous_coe_inv.comp continuous_snd))⟩
end GlobalTheory.Doubling
