-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.moveArgs_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:51.412859+00:00
-- url     : https://prove2.me/submissions/5aebb840-e1f7-41c5-bb49-1686fe93daf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_SplitFlip_invT_inv_val
import Theorems.Thm_GlobalTheory_SplitFlip_invT_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution (g : G.VertexGroup) (z : G.Args) (i j : ℕ) : G.moveArgs .one g z (.theta i j) =
    (((g (i, j + 1))⁻¹).val * (z (.theta i j))ᵀ * (g (i, j)).val)ᵀ := by
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, Edge.src, Edge.tgt]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]
end GlobalTheory.FunObj.OneCosetProof
