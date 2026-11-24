-- Prove2me | solution 1 for GlobalTheory.Doubling.bc_blkGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:32.102332+00:00
-- url     : https://prove2.me/submissions/9f47a652-0674-47b6-89b4-84059bdb201e

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
theorem _root_.solution (f : A →+* B) (x : GL m A) (y : GL n A) : bc f (blkGL e (x, y)) = blkGL e (bc f x, bc f y) :=
  Units.ext (blkMat_map e f (map_zero f) _ _)
end GlobalTheory.Doubling
