-- Prove2me | solution 1 for GlobalTheory.SymCompare.exists_reindex_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:08.44873+00:00
-- url     : https://prove2.me/submissions/aee68969-870f-42f1-956e-6a42a45fe9ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_StepData_reGL_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (P : TypeDatum k n) (e : n ≃ m) (M : Matrix m m k) :
    (∃ g ∈ (P.reindex e).J, g.val = M) ↔ ∃ g ∈ P.J, g.val = M.submatrix e e := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, hg, rfl⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨reGL e g, ?_, by rw [reGL_val, h]; simp⟩
    change (reGL e).symm (reGL e g) ∈ P.J
    rwa [MulEquiv.symm_apply_apply]
end GlobalTheory.SymCompare
