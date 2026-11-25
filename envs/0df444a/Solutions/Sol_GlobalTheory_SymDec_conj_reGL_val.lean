-- Prove2me | solution 1 for GlobalTheory.SymDec.conj_reGL_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:50:17.307497+00:00
-- url     : https://prove2.me/submissions/12e6e444-d48f-4ff0-9335-b2f66fe276cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
import Theorems.Thm_GlobalTheory_SymDec_conj_entry
import Theorems.Thm_GlobalTheory_StepData_reGL_val


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
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymDec
theorem _root_.solution (ϖ : kˣ) (hc : 0 + c = c) (g : GL (Fin κ ⊕ Fin c) k) (r s : XIx (Fin κ) t 0 ⊕ Fin c) :
    ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)).val r s =
      dg ϖ r * g.val ((ordZ t hc).symm r) ((ordZ t hc).symm s) * (dg ϖ s)⁻¹ := by
  rw [conj_entry, reGL_val]; rfl
end GlobalTheory.SymDec
