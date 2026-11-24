-- Prove2me | solution 1 for GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:26.327958+00:00
-- url     : https://prove2.me/submissions/9b206943-93fb-4b70-a2a5-6bfbaf279c6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdOfFnEqSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.ProductOfFnSingle
namespace GlobalTheory.ProductOfFnSingle
theorem _root_.solution {M : Type u_1} [inst : Monoid M] {d : ℕ} (g : Fin d → M) (j : Fin d)
    (h : ∀ (i : Fin d), i ≠ j → g i = (1 : M)) : List.prod (List.ofFn g) = g j := by
  induction d with
  | zero => exact j.elim0
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have hrest : List.prod (List.ofFn fun i : Fin d => g i.succ) = 1 := by
        apply List.prod_eq_one
        intro x hx
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero i)
      rw [hrest, mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      rw [h 0 (fun e => hj e.symm), one_mul]
      exact ih (fun i => g i.succ) j' (fun i hi => h _ (fun e => hi (Fin.succ_injective _ e)))
end GlobalTheory.ProductOfFnSingle
