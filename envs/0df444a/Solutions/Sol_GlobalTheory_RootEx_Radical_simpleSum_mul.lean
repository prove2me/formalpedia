-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.simpleSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:20.6928+00:00
-- url     : https://prove2.me/submissions/94a43022-b2aa-4ad7-b6f0-c8a20073eb1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul_apply_succ
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff

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
theorem _root_.solution {g h : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (hh : h ∈ N k n c p) :
    simpleSum (g * h) = simpleSum g + simpleSum h := by
  rw [mem_N_iff] at hg hh
  simp only [simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Uni.mul_apply_succ (b := lev p) hg hh (by simp [lev, hij])
  · simp
end GlobalTheory.RootEx.Radical
