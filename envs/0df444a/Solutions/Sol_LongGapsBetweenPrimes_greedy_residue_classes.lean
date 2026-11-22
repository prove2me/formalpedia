-- Prove2me | solution 1 for LongGapsBetweenPrimes.greedy_residue_classes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:12.330794+00:00
-- url     : https://prove2.me/submissions/7e11cb31-983d-4361-b494-cc6f21439c99

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (S ps : Finset ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤ (S.card : ℝ) * ∏ p ∈ ps, (1 - 1 / (p : ℝ)) := by
  classical
  induction ps using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp, by simp [survivors]⟩
  | @insert p ps hp ih =>
      have hp0 : 0 < p := hpos p (Finset.mem_insert_self p ps)
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
      obtain ⟨a, ha, hcard⟩ := ih (fun q hq => hpos q (Finset.mem_insert_of_mem hq))
      let T := survivors S ps a
      have hsum : (∑ r ∈ Finset.range p,
          ((T.filter fun n => n % p = r).card : ℝ)) = T.card := by
        exact_mod_cast (Finset.card_eq_sum_card_fiberwise
          (f := fun n => n % p) (s := T) (t := Finset.range p)
          (by intro n _; exact Finset.mem_range.mpr (Nat.mod_lt n hp0))).symm
      obtain ⟨r, hr, hlarge⟩ : ∃ r ∈ Finset.range p,
          (T.card : ℝ) / p ≤ ((T.filter fun n => n % p = r).card : ℝ) := by
        apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hp0.ne')
        rw [hsum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact le_of_eq (by field_simp)
      have hsplit : ((T.filter fun n => n % p = r).card : ℝ) +
          ((T.filter fun n => n % p ≠ r).card : ℝ) = T.card := by
        exact_mod_cast T.card_filter_add_card_filter_not (fun n => n % p = r)
      have hstep : ((T.filter fun n => n % p ≠ r).card : ℝ) ≤
          (T.card : ℝ) * (1 - 1 / (p : ℝ)) := by
        rw [div_eq_mul_inv] at hlarge
        simp only [one_div]
        nlinarith
      refine ⟨Function.update a p r, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · simpa using Finset.mem_range.mp hr
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)] using ha q hq
      · have hsurvivors : survivors S (insert p ps) (Function.update a p r) =
            T.filter (fun n => n % p ≠ r) := by
          have hupdate : ∀ q ∈ ps, Function.update a p r q = a q := by
            intro q hq
            exact Function.update_of_ne (ne_of_mem_of_not_mem hq hp) r a
          ext n
          simp (config := { contextual := true }) only [survivors, Finset.mem_filter,
            Finset.mem_insert, forall_eq_or_imp, Function.update_self, T, hupdate]
          tauto
        rw [hsurvivors, Finset.prod_insert hp]
        calc
          _ ≤ (T.card : ℝ) * (1 - 1 / (p : ℝ)) := hstep
          _ ≤ ((S.card : ℝ) * ∏ q ∈ ps, (1 - 1 / (q : ℝ))) *
              (1 - 1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard (by
              have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
              exact sub_nonneg.mpr ((div_le_one hpR).mpr this))
          _ = _ := by ring
end LongGapsBetweenPrimes
