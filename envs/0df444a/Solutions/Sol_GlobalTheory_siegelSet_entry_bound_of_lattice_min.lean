-- Prove2me | solution 1 for GlobalTheory.siegelSet_entry_bound_of_lattice_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:41.702563+00:00
-- url     : https://prove2.me/submissions/d52d1771-098d-46ab-8b6b-57392a8bd66e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelSetEntryBoundOfLatticeMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (C : ℝ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ) (hS : IsSiegel C k a n) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmin : ∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖)
    (i j : Fin N) : |(k * diagonal a * n) i j| * t ^ N ≤ N * C ^ N := by
  have hN : 0 < N := Fin.pos i
  set i0 : Fin N := ⟨0, hN⟩ with hi0

  have hk : ∀ p q, |k p q| ≤ 1 := by
    intro p q
    have h := congrFun (congrFun hS.orth q) q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have : k p q * k p q ≤ ∑ x, k x q * k x q :=
      Finset.single_le_sum (f := fun x => k x q * k x q) (fun x _ => mul_self_nonneg _) (Finset.mem_univ p)
    rw [h] at this
    have h2 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact this
    nlinarith [abs_nonneg (k p q)]
  have hC1 : 1 ≤ C := by
    have := hS.bdd i i
    rw [hS.diag i, abs_one] at this
    exact this

  have hg : ∀ p q, (k * diagonal a * n) p q = ∑ l, k p l * a l * n l q := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]

  have hcol : ∀ p, (k * diagonal a * n) p i0 = k p i0 * a i0 := by
    intro p
    rw [hg, Finset.sum_eq_single i0]
    · rw [hS.diag i0, mul_one]
    · intro l _ hl
      have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      rw [hS.lower l i0 this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have ha0 : t ≤ a i0 := by
    have h := hmin (Pi.single i0 1) (by
      intro h; have := congrFun h i0; simp at this)
    refine h.trans ?_
    refine (pi_norm_le_iff_of_nonneg (le_of_lt (hS.pos i0))).2 ?_
    intro p
    have : ((k * diagonal a * n) *ᵥ fun i => (((Pi.single i0 (1:ℤ) : Fin N → ℤ) i : ℤ) : ℝ)) p
        = (k * diagonal a * n) p i0 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hcol, Real.norm_eq_abs, abs_mul, abs_of_pos (hS.pos i0)]
    exact mul_le_of_le_one_left (le_of_lt (hS.pos i0)) (hk p i0)
  have hlow : ∀ l, t ≤ C * a l := by
    intro l
    by_cases hl : l = i0
    · subst hl
      nlinarith [hS.pos i0]
    · have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      exact ha0.trans (hS.le i0 l this)
  have hup : ∀ l, a l * t ^ (N - 1) ≤ C ^ (N - 1) := by
    intro l
    have hprod : ∏ x ∈ Finset.univ.erase l, t ≤ ∏ x ∈ Finset.univ.erase l, (C * a x) :=
      Finset.prod_le_prod (fun _ _ => le_of_lt ht0) (fun x _ => hlow x)
    rw [Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin] at hprod
    have h1 : a l * ∏ x ∈ Finset.univ.erase l, a x = 1 := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ l)]; exact hS.prod_eq
    have hal := le_of_lt (hS.pos l)
    calc a l * t ^ (N - 1) ≤ a l * (C ^ (N - 1) * ∏ x ∈ Finset.univ.erase l, a x) :=
          mul_le_mul_of_nonneg_left hprod hal
      _ = C ^ (N - 1) * (a l * ∏ x ∈ Finset.univ.erase l, a x) := by ring
      _ = C ^ (N - 1) := by rw [h1, mul_one]
  have hent : |(k * diagonal a * n) i j| ≤ ∑ l, a l * C := by
    rw [hg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (hS.pos l)]
    have h1 := hk i l
    have h2 := hS.bdd l j
    have hal := le_of_lt (hS.pos l)
    calc |k i l| * a l * |n l j| ≤ 1 * a l * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hal) h2 (abs_nonneg _) (by positivity)
      _ = a l * C := by ring
  have htN : t ^ N = t ^ (N - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have htpow : 0 ≤ t ^ N := by positivity
  calc |(k * diagonal a * n) i j| * t ^ N ≤ (∑ l, a l * C) * t ^ N :=
        mul_le_mul_of_nonneg_right hent htpow
    _ = ∑ l, (a l * t ^ (N - 1)) * C * t := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; rw [htN]; ring
    _ ≤ ∑ l : Fin N, C ^ (N - 1) * C * 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hup l) (by linarith)) ht1 (le_of_lt ht0)
        positivity
    _ = N * C ^ N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_succ,
          Nat.sub_add_cancel hN]
end GlobalTheory
