-- Prove2me | solution 1 for GlobalTheory.SymDec.mem_KO_of_intM_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:48.033798+00:00
-- url     : https://prove2.me/submissions/46ecb07e-4b7a-4bfd-842d-98b19b0be2f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
import Theorems.Thm_GlobalTheory_SymDec_intM_adjugate
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymDec
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (h : IntM g.val) (hd : g.val.det = 1) :
    g ∈ KO k n := by
  refine mem_KO.2 ⟨h, ?_⟩
  have : (g⁻¹).val = g.val.adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hd]; simp
  rw [this]; exact intM_adjugate h
end GlobalTheory.SymDec
