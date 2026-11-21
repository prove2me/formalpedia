-- Prove2me | solution 1 for MasulloGRH.nuclear_of_dual_domination
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:18:16.325381+00:00
-- url     : https://prove2.me/submissions/1e50ee36-3706-4563-acdb-81868592800a

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_expansion_of_dual_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH

universe u

/-- A nuclear expansion `x = ∑ cₙ gₙ(x) yₙ` (convergent for `p`, with `p(yₙ) ≤ 1`) gives the
quasinuclear estimate `p(x) ≤ ∑ cₙ |gₙ(x)|`. -/
private lemma le_tsum_of_expansion {E : Type u} [AddCommGroup E] [Module ℂ E]
    (p r : Seminorm ℂ E) (y : ℕ → E) (g : ℕ → E → ℂ) (c : ℕ → ℝ)
    (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c) (hy : ∀ n, p (y n) ≤ 1)
    (hg : ∀ n x, ‖g n x‖ ≤ r x) (x : E)
    (ht : Filter.Tendsto
        (fun N : ℕ => p (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * g n x) • y n))
        Filter.atTop (nhds 0)) :
    p x ≤ ∑' n, c n * ‖g n x‖ := by
  have hnn : ∀ n, 0 ≤ c n * ‖g n x‖ := fun n => mul_nonneg (hc0 n) (norm_nonneg _)
  have hsum : Summable (fun n => c n * ‖g n x‖) :=
    (hcs.mul_right (r x)).of_nonneg_of_le hnn
      (fun n => mul_le_mul_of_nonneg_left (hg n x) (hc0 n))
  have key : ∀ N : ℕ, p x - ∑' n, c n * ‖g n x‖ ≤
      p (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * g n x) • y n) := by
    intro N
    set S := ∑ n ∈ Finset.range N, ((c n : ℂ) * g n x) • y n
    have h1 : p x ≤ p S + p (x - S) := by
      calc p x = p (S + (x - S)) := by congr 1; abel
        _ ≤ p S + p (x - S) := map_add_le_add p _ _
    have h2 : p S ≤ ∑ n ∈ Finset.range N, c n * ‖g n x‖ := by
      refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [map_smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
      calc c n * ‖g n x‖ * p (y n) ≤ c n * ‖g n x‖ * 1 :=
            mul_le_mul_of_nonneg_left (hy n) (hnn n)
        _ = c n * ‖g n x‖ := mul_one _
    have h3 : ∑ n ∈ Finset.range N, c n * ‖g n x‖ ≤ ∑' n, c n * ‖g n x‖ :=
      hsum.sum_le_tsum _ (fun n _ => hnn n)
    linarith
  have : p x - ∑' n, c n * ‖g n x‖ ≤ 0 :=
    ge_of_tendsto ht (Filter.Eventually.of_forall key)
  linarith

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hdom : ∀ q : Seminorm ℂ E, Continuous q →
      ∃ (p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
        Continuous p ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
        ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
          ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖) :
    IsNuclear E := by
  refine nuclear_of_quasinuclear_domination E hE ?_
  intro p hp
  obtain ⟨r, y, g, c, hr, hc0, hcs, hy, hg, ht⟩ :=
    nuclear_expansion_of_dual_domination E hE hdom p hp
  exact ⟨r, g, c, hr, hc0, hcs, hg, fun x =>
    le_tsum_of_expansion p r y (fun n => g n) c hc0 hcs hy hg x (ht x)⟩
