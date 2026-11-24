-- Prove2me | solution 1 for GlobalTheory.KilledFin.powSpan_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:29.163027+00:00
-- url     : https://prove2.me/submissions/f9361e9c-66aa-4969-9505-c1e05accc708

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated

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
theorem _root_.solution (t u : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V)
    (hu : ∀ n ∈ N, u n ∈ N) (hc : Commute u t) (v : V) (hv : v ∈ powSpan t d N) :
    u v ∈ powSpan t d N := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, n, hn, rfl⟩ := hx
    have e : u ((t ^ i) n) = (t ^ i) (u n) := by
      rw [← Module.End.mul_apply, (hc.pow_right i).eq, Module.End.mul_apply]
    rw [e]
    exact Submodule.subset_span ⟨i, hi, u n, hu n hn, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
end GlobalTheory.KilledFin
