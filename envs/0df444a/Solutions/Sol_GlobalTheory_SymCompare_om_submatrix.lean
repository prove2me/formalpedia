-- Prove2me | solution 1 for GlobalTheory.SymCompare.om_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:39.417513+00:00
-- url     : https://prove2.me/submissions/7880242e-f88c-4f6e-9e8d-4fc1e78cec78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_StepData_det_reGL
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
theorem _root_.solution (μ : kˣ →* ℂˣ) (E : n ≃ m) (E' : n' ≃ m') (h : GL n k) (Φ : Matrix n n' k → ℂ) :
    om μ 1 (reGL E h) (fun x => Φ (x.submatrix E E')) = fun x => om μ 1 h Φ (x.submatrix E E') := by
  funext x
  simp only [om, det_reGL, ← Fintype.card_congr E, ← Fintype.card_congr E', ← map_inv (reGL _), reGL_val, map_one,
    Units.val_one, Matrix.mul_one]
  congr 2
  rw [← submatrix_mul_equiv _ _ _ E]
  simp
end GlobalTheory.SymCompare
