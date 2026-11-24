-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.det_rmat_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:21.753693+00:00
-- url     : https://prove2.me/submissions/06e547dd-8267-4b2a-b645-d7f56ad9a0f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_of_blocks
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (u : unipRad k e) : (rmat e ((u : GL n k) : Matrix n n k)).det = 1 := by
  rw [← det_transpose, det_of_blocks _ (fun p : Idx e => blk e p.1.2) ?_ (fun a => {j : n // blk e j < a})
    (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    simp [rmat, (mem_unipRad.1 u.2).1 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) ((mem_unipRad.1 u.2).2 a x.1 y.1) rfl
end GlobalTheory.SmGL.UnitInd
