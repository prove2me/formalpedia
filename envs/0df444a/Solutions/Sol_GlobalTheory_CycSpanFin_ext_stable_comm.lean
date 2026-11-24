-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.ext_stable_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:14.290728+00:00
-- url     : https://prove2.me/submissions/d66f1df0-f5d3-42ad-9069-6811b72b285f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
import Theorems.Thm_GlobalTheory_CycSpanFin_pow_mem_ext

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
theorem _root_.solution (T S : Module.End ℂ V) (d : ℕ) (hST : Commute S T) {N : Submodule ℂ V}
    (hS : ∀ v ∈ N, S v ∈ N) : ∀ v ∈ ext T d N, S v ∈ ext T d N := by
  have : ext T d N ≤ (ext T d N).comap S := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change S ((T ^ (k : ℕ)) x) ∈ ext T d N
    have h := congrArg (fun F : Module.End ℂ V => F x) (hST.pow_right (k : ℕ)).eq
    simp only [Module.End.mul_apply] at h
    rw [h]
    exact pow_mem_ext T (Nat.lt_succ_iff.1 k.2) (hS x hx)
  exact fun v hv => this hv
end GlobalTheory.CycSpanFin
