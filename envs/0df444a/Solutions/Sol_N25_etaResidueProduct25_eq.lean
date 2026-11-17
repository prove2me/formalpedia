-- Prove2me | solution 1 for N25.etaResidueProduct25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:36.480208+00:00
-- url     : https://prove2.me/submissions/a4831bb9-e7c8-477a-8cc9-66b00dccdda8

import Mathlib

set_option autoImplicit false

namespace N25

private theorem residue_reindex (r : ℕ) (hr : 0 < r) (hr25 : r < 25)
    (f : ℕ → ℂ) :
    (∏' k : ℕ, if (k + 1) % 25 = r then f (k + 1) else 1) =
      ∏' n : ℕ, f (25 * n + r) := by
  let F : ℕ → ℂ := fun k => if (k + 1) % 25 = r then f (k + 1) else 1
  let j : ℕ → ℕ := fun n => 25 * n + r - 1
  have hj : ∀ n, j n + 1 = 25 * n + r := fun n => by dsimp [j]; omega
  have hinj : Function.Injective j := by
    intro a b hab
    have ha := hj a
    have hb := hj b
    omega
  have hcond : ∀ n, (j n + 1) % 25 = r := fun n => by rw [hj]; omega
  have hsupp : Function.mulSupport F ⊆ Set.range j := by
    intro k hk
    rw [Function.mem_mulSupport] at hk
    have hc : (k + 1) % 25 = r := by
      by_contra hc
      exact hk (by simp only [F, if_neg hc])
    refine ⟨(k + 1) / 25, ?_⟩
    dsimp [j]
    omega
  calc
    (∏' k, F k) = ∏' n, F (j n) := (hinj.tprod_eq hsupp).symm
    _ = ∏' n, f (25 * n + r) := tprod_congr fun n => by
      dsimp [F]
      rw [if_pos (hcond n), hj]

private theorem residue_multipliable (r : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ => if (k + 1) % 25 = r then 1 - q ^ (k + 1) else 1) := by
  have hs : Summable (fun k : ℕ => ‖if (k + 1) % 25 = r then -(q ^ (k + 1)) else 0‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq))
    intro k
    split_ifs <;> simp [norm_pow, pow_nonneg (norm_nonneg q)]
  convert multipliable_one_add_of_summable hs using 1
  funext k
  split_ifs <;> simp [sub_eq_add_neg]

private theorem stream_multipliable (r : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (25 * n + r)) := by
  have hs : Summable (fun n : ℕ => ‖-(q ^ (25 * n + r))‖) := by
    have hp : ‖q‖ ^ 25 < 1 := pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
    simpa only [norm_neg, norm_mul, norm_pow, pow_add, pow_mul] using
      (summable_geometric_of_lt_one (pow_nonneg (norm_nonneg q) _) hp).mul_right (‖q‖ ^ r)
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/-- The product selected by the two residues is the paired residue stream. -/
theorem _root_.solution (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (if (k + 1) % 25 = g then 1 - q ^ (k + 1) else 1) *
      (if (k + 1) % 25 = 25 - g then 1 - q ^ (k + 1) else 1)) =
    ∏' n : ℕ, (1 - q ^ (25 * n + g)) * (1 - q ^ (25 * (n + 1) - g)) := by
  rw [(residue_multipliable g q hq).tprod_mul (residue_multipliable (25 - g) q hq),
    residue_reindex g hg hg25 (fun k => 1 - q ^ k),
    residue_reindex (25 - g) (by omega) (by omega) (fun k => 1 - q ^ k),
    ← (stream_multipliable g q hq).tprod_mul (stream_multipliable (25 - g) q hq)]
  apply tprod_congr
  intro n
  have he : 25 * n + (25 - g) = 25 * (n + 1) - g := by omega
  rw [he]

end N25
