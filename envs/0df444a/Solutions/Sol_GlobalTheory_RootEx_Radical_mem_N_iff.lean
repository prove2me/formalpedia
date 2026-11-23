-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.mem_N_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:28.528258+00:00
-- url     : https://prove2.me/submissions/b5397799-fae0-4ceb-805a-60b0107c4598

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv

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
theorem _root_.solution (g : GL (n ⊕ Fin c) k) : g ∈ N k n c p ↔ InN p g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => intro r s _; rfl
    | mul x y _ _ hx hy => exact Uni.mul (b := lev p) hx hy
    | inv x _ hx => exact Uni.inv (b := lev p) hx
  · intro hg
    exact Subgroup.subset_closure hg
end GlobalTheory.RootEx.Radical
