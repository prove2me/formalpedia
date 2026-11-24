-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.moveArgs_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:28.903974+00:00
-- url     : https://prove2.me/submissions/859abacc-120a-4cad-af52-33b9505a8e86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor

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
theorem _root_.solution (g : G.VertexGroup) (z z' : G.Args) :
    G.moveArgs .one g (z + z') = G.moveArgs .one g z + G.moveArgs .one g z' := by
  funext b
  simp [Grid.moveArgs, Matrix.mul_add, Matrix.add_mul]
end GlobalTheory.FunObj.OneCosetProof
