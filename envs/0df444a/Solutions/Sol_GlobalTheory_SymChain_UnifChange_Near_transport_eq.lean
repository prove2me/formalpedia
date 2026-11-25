-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.Near.transport_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:15.078857+00:00
-- url     : https://prove2.me/submissions/790948d5-9617-4e16-b6ea-98147cee8afd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_apply_mul_KOne
import Theorems.Thm_GlobalTheory_StepData_HasTypes_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.SymChain.UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.SymChain.UnifChange
namespace Near
theorem _root_.solution {F G : LatFrame k ι Y} {F' G' : LatFrame k ι' Y'} (h : Near F G) (h' : Near F' G')
    {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x) :
    G.transport G' f = F.transport F' f := by
  funext x
  change f (G.coords G' x) = f (F.coords F' x)
  rw [← apply_mul_KOne hs hp (reGL_symm_mem_KOne F.ord (inv_mem h.2)) (reGL_symm_mem_KOne F'.ord h'.2) (F.coords F' x)]
  congr 1
  unfold LatFrame.coords
  rw [reGL_symm_val, reGL_symm_val, submatrix_mul_equiv, submatrix_mul_equiv, h.1, h'.1]
  congr 1
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.bas.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc F'.bas.val, Units.mul_inv,
    Matrix.one_mul]
end Near
end GlobalTheory.SymChain.UnifChange
