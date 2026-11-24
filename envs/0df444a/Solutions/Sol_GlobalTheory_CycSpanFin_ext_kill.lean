-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.ext_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:13.183909+00:00
-- url     : https://prove2.me/submissions/e56e6a39-5efd-44d4-a4ec-ba7f48dff106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin

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
theorem _root_.solution (T R : Module.End ℂ V) (d : ℕ) (hRT : Commute R T) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, R v = 0) : ∀ v ∈ ext T d N, R v = 0 := by
  have : ext T d N ≤ LinearMap.ker R := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [LinearMap.mem_ker]
    have h := congrArg (fun F : Module.End ℂ V => F x) (hRT.pow_right (k : ℕ)).eq
    simp only [Module.End.mul_apply] at h
    rw [h, hN x hx, map_zero]
  exact fun v hv => this hv
end GlobalTheory.CycSpanFin
