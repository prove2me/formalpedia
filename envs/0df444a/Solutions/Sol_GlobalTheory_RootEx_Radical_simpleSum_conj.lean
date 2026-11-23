-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.simpleSum_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:19.404821+00:00
-- url     : https://prove2.me/submissions/f098c2aa-b9a0-423e-a594-38e680a2101f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g := by
  simp only [simpleSum, conj_val, fromBlocks_apply₂₂]
  rfl
end GlobalTheory.RootEx.Radical
