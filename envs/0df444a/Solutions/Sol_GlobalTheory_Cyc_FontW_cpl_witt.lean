-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.cpl_witt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:54.329016+00:00
-- url     : https://prove2.me/submissions/f9a718de-e12f-4437-8b17-e2a8e9df97c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_mem_Dv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p] :
    Cpl p (WittVector p k) := by
  have key : ∀ (r : ℕ) (x : WittVector p k), x ∈ Dv p r (WittVector p k) ↔
      x ∈ ((Ideal.span {(p : WittVector p k)}) ^ r • ⊤ : Submodule (WittVector p k) (WittVector p k)) := by
    intro r x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton', mem_Dv]
    simp [mul_comm]
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact IsHausdorff.haus (I := Ideal.span {(p : WittVector p k)}) inferInstance x fun n =>
      SModEq.zero.2 ((key n x).1 (hx n))
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : WittVector p k)}) inferInstance
      (f := f) ((AdicCompletion.isAdicCauchy_iff _ _ f).2 fun n => by
        rw [SModEq.sub_mem, ← key, ← neg_sub]; exact neg_mem (hf n))
    refine ⟨L, fun r => ?_⟩
    have := hL r
    rw [SModEq.sub_mem, ← key] at this
    rw [← neg_sub]; exact neg_mem this
end GlobalTheory.Cyc.FontW
