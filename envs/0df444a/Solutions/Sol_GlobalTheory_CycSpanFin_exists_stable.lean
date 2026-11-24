-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.exists_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:13.773394+00:00
-- url     : https://prove2.me/submissions/95c6a185-da0f-47dd-b81e-697d3a06dbce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
import Theorems.Thm_GlobalTheory_CycSpanFin_commute_aeval_left
import Theorems.Thm_GlobalTheory_CycSpanFin_le_ext
import Theorems.Thm_GlobalTheory_CycSpanFin_ext_stable
import Theorems.Thm_GlobalTheory_CycSpanFin_ext_stable_comm
import Theorems.Thm_GlobalTheory_CycSpanFin_ext_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CycSpanFin
theorem _root_.solution (a : ℕ → Module.End ℂ V) (Q : ℕ → ℂ[X]) (hc : ∀ i j, Commute (a i) (a j))
    (hQ : ∀ j, Q j ≠ 0) (w : V) (hw : ∀ j, aeval (a j) (Q j) w = 0) : ∀ m : ℕ, ∃ N : Submodule ℂ V,
      FiniteDimensional ℂ N ∧ w ∈ N ∧ (∀ j < m, ∀ v ∈ N, a j v ∈ N) ∧ (∀ j, ∀ v ∈ N, aeval (a j) (Q j) v = 0)
  | 0 => ⟨Submodule.span ℂ {w}, inferInstance, Submodule.mem_span_singleton_self w, by simp, fun j v hv => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hw, smul_zero]⟩
  | m + 1 => by
      obtain ⟨N, hf, hwN, hst, hk⟩ := solution a Q hc hQ w hw m
      haveI := hf
      refine ⟨ext (a m) (Q m).natDegree N, ?_, le_ext _ _ _ hwN, ?_, ?_⟩
      · unfold ext; infer_instance
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact ext_stable_comm (a m) (a j) _ (hc j m) (hst j h)
        · subst h; exact ext_stable (a j) (hQ j) (hk j)
      · intro j
        exact ext_kill (a m) _ _ (commute_aeval_left (hc j m) _) (hk j)
end GlobalTheory.CycSpanFin
