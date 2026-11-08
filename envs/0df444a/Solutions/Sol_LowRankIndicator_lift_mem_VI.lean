-- Prove2me | solution 1 for LowRankIndicator.lift_mem_VI
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:35:56.709383+00:00
-- url     : https://prove2.me/submissions/620fbb4f-293e-4a8a-bacb-f93973232dd5

import Mathlib
import Definitions.Def_LowRankIndicator_Sets
import Definitions.Def_LowRankIndicator_FeasibleSet7

open scoped Matrix

open LowRankIndicator in
theorem solution {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) {tbar : ℝ} {xbar zbar xstar : Fin n → ℝ}
    (hbar : (tbar, xbar, zbar) ∈ Q g A c Iplus) (hstar : xstar ∈ feas7 A xbar) :
    (tbar + c ⬝ᵥ (xstar - xbar), xstar, zbar) ∈ VI g A c Iplus (supp xstar) := by
  simp only [Q, Set.mem_setOf_eq] at hbar
  obtain ⟨hobj, hIp, hz01, hcomp⟩ := hbar
  obtain ⟨hAx, hsign, hzero⟩ := hstar
  have hxs : ∀ i, xstar i ≠ 0 → xbar i ≠ 0 := fun i h h0 => h (hzero i h0)
  simp only [VI, XI, Xset, ZI, Set.mem_setOf_eq, Set.mem_inter_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hz01, ?_⟩
  · unfold objective at hobj ⊢
    rw [hAx]
    have h : g (A.mulVec xbar) + ((c ⬝ᵥ xbar : ℝ) : EReal) + ((c ⬝ᵥ xstar - c ⬝ᵥ xbar : ℝ) : EReal)
        ≤ (tbar : EReal) + ((c ⬝ᵥ xstar - c ⬝ᵥ xbar : ℝ) : EReal) := add_le_add hobj le_rfl
    calc g (A.mulVec xbar) + ((c ⬝ᵥ xstar : ℝ) : EReal)
        = g (A.mulVec xbar) + ((c ⬝ᵥ xbar : ℝ) : EReal) + ((c ⬝ᵥ xstar - c ⬝ᵥ xbar : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add,
            show c ⬝ᵥ xbar + (c ⬝ᵥ xstar - c ⬝ᵥ xbar) = c ⬝ᵥ xstar by ring]
      _ ≤ (tbar : EReal) + ((c ⬝ᵥ xstar - c ⬝ᵥ xbar : ℝ) : EReal) := h
      _ = ((tbar + c ⬝ᵥ (xstar - xbar) : ℝ) : EReal) := by
          rw [← EReal.coe_add, dotProduct_sub]
  · intro i hi
    by_cases h0 : xbar i = 0
    · rw [hzero i h0]
    · have h1 := hsign i h0
      have h2 := hIp i hi
      have hpos : 0 < xbar i := lt_of_le_of_ne h2 (Ne.symm h0)
      nlinarith
  · intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro i hi
    have hne := (Finset.mem_filter.mp hi).2
    have h := (mul_eq_zero.mp (hcomp i)).resolve_left (hxs i hne)
    linarith
