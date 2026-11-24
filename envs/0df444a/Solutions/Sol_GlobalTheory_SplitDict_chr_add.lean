-- Prove2me | solution 1 for GlobalTheory.SplitDict.chr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:42.875058+00:00
-- url     : https://prove2.me/submissions/cdf52eb6-af6a-40fc-a37b-86955d531ad0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]
namespace GlobalTheory.SplitDict
theorem _root_.solution (ψ : AddChar k Circle) (s : ℤˣ) (x y : k) : chr ψ s (x + y) = chr ψ s x * chr ψ s y := by
  simp only [chr, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul]
end GlobalTheory.SplitDict
