-- Prove2me | solution 1 for GlobalTheory.PMonE.moore_step_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:07.654048+00:00
-- url     : https://prove2.me/submissions/450db090-0f27-4a7c-ad80-34138e817fb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Theorems.Thm_GlobalTheory_PMonE_moore_pow_sub_self_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) :
    x ^ p - t ^ (p - 1) * x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases ht : t = 0
  · subst ht
    rw [zero_pow (by omega)]
    simp
  · have h := moore_pow_sub_self_eq_prod p (x / t)
    have h1 : ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) = ∏ c : ZMod p, (t * (x / t - ((c.val : ℕ) : F))) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      field_simp
    rw [h1, Finset.prod_mul_distrib, ← h, Finset.prod_const, Finset.card_univ, ZMod.card]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, div_pow]
    field_simp
    ring
end GlobalTheory.PMonE
