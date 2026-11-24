-- Prove2me | solution 1 for GlobalTheory.NormFormGauss.sum_eq_zero_add_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:50.266789+00:00
-- url     : https://prove2.me/submissions/1daf5dee-41de-4e1e-81de-c98e4d31d438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss
namespace GlobalTheory.NormFormGauss
theorem _root_.solution {k : Type} [Field k] [Fintype k] {M : Type} [AddCommMonoid M]
    (g : k → M) : ∑ x : k, g x = g 0 + ∑ x : kˣ, g x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
  congr 1
  symm
  refine Finset.sum_bij (fun x _ => (x : k)) ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro b hb
    exact ⟨Units.mk0 b (by simpa using hb), by simp, rfl⟩
  · intro a _; rfl
end GlobalTheory.NormFormGauss
