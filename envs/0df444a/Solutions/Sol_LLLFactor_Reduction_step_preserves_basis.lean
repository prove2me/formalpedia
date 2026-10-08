-- Prove2me | solution 1 for LLLFactor.Reduction.step_preserves_basis
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:59:02.439228+00:00
-- url     : https://prove2.me/submissions/f34361ad-6f57-497e-938e-0eb0601db9d8

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

set_option backward.isDefEq.respectTransparency false
open LLLFactor.Reduction LLLFactor.RedBasis

private theorem reduce_li {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
    (κ l : Fin n) (hne : κ ≠ l) (r : ℤ) : LinearIndependent ℝ (reduceBy b κ l r) := by
  apply hb.update κ (b κ - (r : ℝ) • b l)
  refine ⟨1, by simp, Finsupp.single κ 1 - Finsupp.single l (r : ℝ), ?_, ?_⟩
  · simp [hne]
  · simp

private theorem reduce_le {n : ℕ} (b : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    latticeOf (reduceBy b κ l r) ≤ latticeOf b := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  by_cases hi : i = κ
  · subst i
    simp only [reduceBy, Function.update_self]
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨κ, rfl⟩
    · have h := (latticeOf b).smul_mem r (Submodule.subset_span (Set.mem_range_self l))
      simpa only [Int.cast_smul_eq_zsmul] using h
  · simpa [reduceBy, latticeOf, Function.update_of_ne hi] using
      (Submodule.subset_span (Set.mem_range_self i) : b i ∈ latticeOf b)

private theorem reduce_lat {n : ℕ} (b : Fin n → Vec n) (κ l : Fin n) (hne : κ ≠ l) (r : ℤ) :
    latticeOf (reduceBy b κ l r) = latticeOf b := by
  apply le_antisymm (reduce_le b κ l r)
  have hinv : reduceBy (reduceBy b κ l r) κ l (-r) = b := by
    funext i
    by_cases hi : i = κ
    · subst i
      simp [reduceBy, Function.update_of_ne hne.symm]
    · simp [reduceBy, Function.update_of_ne hi]
  have h := reduce_le (reduceBy b κ l r) κ l (-r)
  rwa [hinv] at h

private theorem achieve_basis {n : ℕ} (b c : Fin n → Vec n) (k : ℕ)
    (hb : LinearIndependent ℝ b) (h : Achieve118 b k c) :
    LinearIndependent ℝ c ∧ latticeOf c = latticeOf b := by
  unfold Achieve118 at h
  split_ifs at h with hk
  · rcases h with ⟨_, rfl⟩ | ⟨_, r, _, rfl⟩
    · exact ⟨hb, rfl⟩
    · exact ⟨reduce_li b hb _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega) r,
        reduce_lat b _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega) r⟩
  · subst c
    exact ⟨hb, rfl⟩

private theorem loop_basis {n : ℕ} (κ : Fin n) (b c : Fin n → Vec n)
    (hb : LinearIndependent ℝ b) (h : Relation.ReflTransGen (LoopStep κ) b c) :
    LinearIndependent ℝ c ∧ latticeOf c = latticeOf b := by
  induction h with
  | refl => exact ⟨hb, rfl⟩
  | @tail c d hcd hs ih =>
    rcases hs with ⟨l, hl, _, _, r, _, rfl⟩
    exact ⟨reduce_li c ih.1 κ l (ne_of_gt hl) r,
      (reduce_lat c κ l (ne_of_gt hl) r).trans ih.2⟩

theorem solution {n : ℕ} (b b' : Fin n → Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) (hstep : Step (b, k) (b', k')) :
    LinearIndependent ℝ b' ∧ latticeOf b' = latticeOf b := by
  rcases hstep with h | h
  · rcases h with ⟨hk, c, hc, _, hb', _⟩
    obtain ⟨hci, hcl⟩ := achieve_basis b c k hb hc
    dsimp at hb'
    subst b'
    refine ⟨hci.comp _ (Equiv.swap _ _).injective, ?_⟩
    rw [latticeOf, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact hcl
  · rcases h with ⟨hk, c, hc, _, hl, _, _⟩
    obtain ⟨hci, hcl⟩ := achieve_basis b c k hb hc
    obtain ⟨hli, hll⟩ := loop_basis _ c b' hci hl
    exact ⟨hli, hll.trans hcl⟩

#print axioms solution
