-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.simpleSum_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:45.315907+00:00
-- url     : https://prove2.me/submissions/758566e9-8821-4530-b740-8ebf48165d0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (u : GL (n ⊕ Fin c) k) (g : GL n k) :
    simpleSum ((embX c g)⁻¹ * u * embX c g) = simpleSum u := by
  rw [← map_inv]
  have hv : ∀ i j, ((embX c g⁻¹) * u * embX c g).val (Sum.inr i) (Sum.inr j) = u.val (Sum.inr i) (Sum.inr j) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val]
    simp [embX, fromBlocks_multiply]
  simp only [simpleSum, hv]
end GlobalTheory.RootEx.Model
