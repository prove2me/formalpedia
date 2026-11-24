-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.exists_least_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:42.254909+00:00
-- url     : https://prove2.me/submissions/17d11dd5-eb6c-41e3-aba4-9937abb54a2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace GlobalTheory.ValuedPrincipal
theorem _root_.solution {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) {d : ℕ} (hd : 1 ≤ d)
    (h : ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) (q : ℚ) :
    ∃ t : F, t ≠ 0 ∧ (q : WithTop ℚ) ≤ v t ∧ ∀ a : F, (q : WithTop ℚ) ≤ v a → v t ≤ v a := by
  classical
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hne : ∃ n : ℤ, ∃ x : F, x ≠ 0 ∧ v x = (((n : ℚ) / d : ℚ) : WithTop ℚ) ∧ q ≤ (n : ℚ) / d := by
    obtain ⟨y, hy, hyv⟩ := exists_val_eq_int v hπ ⌈q⌉
    have hc : ((⌈q⌉ * d : ℤ) : ℚ) / d = ⌈q⌉ := by
      push_cast
      field_simp
    refine ⟨⌈q⌉ * d, y, hy, ?_, ?_⟩
    · rw [hyv, hc]
    · rw [hc]
      exact Int.le_ceil q
  have hbdd : ∃ b : ℤ, ∀ n : ℤ, (∃ x : F, x ≠ 0 ∧ v x = (((n : ℚ) / d : ℚ) : WithTop ℚ) ∧
      q ≤ (n : ℚ) / d) → b ≤ n := by
    refine ⟨⌊q * d⌋, ?_⟩
    rintro n ⟨x, -, -, hqn⟩
    rw [le_div_iff₀ hdq] at hqn
    have hf := Int.floor_le (q * d)
    exact_mod_cast hf.trans hqn
  obtain ⟨n, ⟨t, ht, htv, hqt⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hne
  refine ⟨t, ht, ?_, ?_⟩
  · rw [htv]
    exact_mod_cast hqt
  · intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, v.map_zero]
      exact le_top
    · obtain ⟨m, hm⟩ := h a ha0
      have hqm : q ≤ (m : ℚ) / d := by
        rw [hm] at ha
        exact_mod_cast ha
      have hnm : (n : ℚ) ≤ m := by exact_mod_cast hmin m ⟨a, ha0, hm, hqm⟩
      have hdiv : (n : ℚ) / d ≤ (m : ℚ) / d := by gcongr
      rw [htv, hm]
      exact_mod_cast hdiv
end GlobalTheory.ValuedPrincipal
