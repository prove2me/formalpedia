-- Prove2me | solution 1 for GlobalTheory.SymCompare.coords_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:20:22.742851+00:00
-- url     : https://prove2.me/submissions/722dd8bc-c436-4c04-8daa-7ec8b28deded

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
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution {ι ι' κ κ' : Type*}
    (F : LatFrame k ι n) (F' : LatFrame k ι' m) (a : ι ≃ ι') (b : n ≃ m) (ho : a.trans F'.ord = F.ord.trans b)
    (hb : F'.bas = reGL b F.bas)
    (G : LatFrame k κ n') (G' : LatFrame k κ' m') (a' : κ ≃ κ') (b' : n' ≃ m') (ho' : a'.trans G'.ord = G.ord.trans b')
    (hb' : G'.bas = reGL b' G.bas) (x : Matrix m m' k) :
    (F'.coords G' x).submatrix a a' = F.coords G (x.submatrix b b') := by
  have e1 : (F.bas⁻¹).val = (F'.bas⁻¹).val.submatrix b b := by
    rw [hb, ← map_inv, reGL_val]; simp
  have e2 : G.bas.val = G'.bas.val.submatrix b' b' := by
    rw [hb', reGL_val]; simp
  unfold LatFrame.coords
  rw [e1, e2, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_submatrix, submatrix_submatrix]
  exact congrArg₂ _ (congrArg (fun e : ι ≃ m => (e : ι → m)) ho) (congrArg (fun e : κ ≃ m' => (e : κ → m')) ho')
end GlobalTheory.SymCompare
