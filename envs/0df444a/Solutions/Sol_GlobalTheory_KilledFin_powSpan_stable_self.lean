-- Prove2me | solution 1 for GlobalTheory.KilledFin.powSpan_stable_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:08.501246+00:00
-- url     : https://prove2.me/submissions/fbc9bb0e-1f27-4dc4-8bb7-f687a3b3edae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
import Theorems.Thm_GlobalTheory_KilledFin_pow_mem_powSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.KilledFin
theorem _root_.solution (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (v : V) (hv : v ∈ powSpan t q.natDegree N) :
    t v ∈ powSpan t q.natDegree N := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, n, hn, rfl⟩ := hx
    have e : t ((t ^ i) n) = (t ^ (i + 1)) n := by rw [pow_succ', Module.End.mul_apply]
    rw [e]
    rcases Nat.lt_or_ge (i + 1) q.natDegree with h | h
    · exact Submodule.subset_span ⟨i + 1, h, n, hn, rfl⟩
    · have : i + 1 = q.natDegree := by omega
      rw [this]
      exact pow_mem_powSpan t q hq N hkill n hn
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
end GlobalTheory.KilledFin
