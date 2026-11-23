-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotLinear.isClosed_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:26.031217+00:00
-- url     : https://prove2.me/submissions/b414393d-d4bd-4242-aa61-ae979397d61e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotLinear
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.QuotLinear
theorem _root_.solution : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = ⋂ r, ⋂ s, ⋂ (_ : lev p s ≤ lev p r),
      {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
    ext g
    simp only [SetLike.mem_coe, Radical.mem_N_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq ?_ continuous_const
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop
end GlobalTheory.RootEx.QuotLinear
