-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.map_lt_of_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:20.334303+00:00
-- url     : https://prove2.me/submissions/ea0d31c4-60a8-4da5-8b0c-ab699e9bec23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution {N : Submodule ℂ V} (g : End ℂ V) (K : ℕ)
    (hg : N.map g ≤ N) (hK : ∀ n ∈ N, (g ^ K) n = 0) (hN : N ≠ ⊥) : N.map g < N := by
  refine lt_of_le_of_ne hg fun h => hN ?_
  have hk : ∀ k : ℕ, N.map (g ^ k) = N := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih => rw [pow_succ, Module.End.mul_eq_comp, Submodule.map_comp, h, ih]
  rw [← hk K, eq_bot_iff]
  rintro _ ⟨n, hn, rfl⟩
  simp [hK n hn]
end GlobalTheory.GenEigenFinOrbit
