-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.ext_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:55.615418+00:00
-- url     : https://prove2.me/submissions/d0c36d4d-4b59-4e38-b556-77b2c75e7814

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
import Theorems.Thm_GlobalTheory_CycSpanFin_aeval_mem_ext

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
theorem _root_.solution (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) : ∀ v ∈ ext T Q.natDegree N, T v ∈ ext T Q.natDegree N := by
  have : ext T Q.natDegree N ≤ (ext T Q.natDegree N).comap T := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change T ((T ^ (k : ℕ)) x) ∈ ext T Q.natDegree N
    have := aeval_mem_ext T hQ hN (X ^ ((k : ℕ) + 1)) hx
    rwa [map_pow, aeval_X, pow_succ', Module.End.mul_apply] at this
  exact fun v hv => this hv
end GlobalTheory.CycSpanFin
