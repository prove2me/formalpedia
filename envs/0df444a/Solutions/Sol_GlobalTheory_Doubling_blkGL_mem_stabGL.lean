-- Prove2me | solution 1 for GlobalTheory.Doubling.blkGL_mem_stabGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:24:51.450775+00:00
-- url     : https://prove2.me/submissions/d2b62f0f-5e8a-4384-89c5-88393b0433ef

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_blkMat_mulVec
import Theorems.Thm_GlobalTheory_Doubling_pairVec_mem_sumLat
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
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]
omit [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
namespace GlobalTheory.Doubling
theorem _root_.solution [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
    {O : Type} [CommRing O] [Algebra O A] {L : Submodule O (m → A)} {L' : Submodule O (n → A)} {x : GL m A} {y : GL n A} :
    blkGL e (x, y) ∈ stabGL (sumLat e L L') ↔ x ∈ stabGL L ∧ y ∈ stabGL L' := by
  refine ⟨fun h => ⟨fun u => ?_, fun v => ?_⟩, fun h w => ?_⟩
  · simpa [blkMat_mulVec, pairVec_mem_sumLat] using h (pairVec e u 0)
  · simpa [blkMat_mulVec, pairVec_mem_sumLat] using h (pairVec e 0 v)
  · rw [← pairVec_eta e w, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, pairVec_mem_sumLat]
    exact and_congr (h.1 _) (h.2 _)
end GlobalTheory.Doubling
