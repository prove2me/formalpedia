-- Prove2me | solution 1 for MasulloGRH.nuclear_dual_domination
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:19:49.573555+00:00
-- url     : https://prove2.me/submissions/7b5f2907-4efb-44c8-a845-a73005cb7a43

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_quasinuclear_comp_nuclear_expansion

set_option autoImplicit false

open MasulloGRH
open Filter Topology

universe u

/-- A pointwise nuclear expansion `x = ∑ cₙ hₙ(x) yₙ` (convergent for `q`) with `|hₙ| ≤ s` and
`q(yₙ) ≤ 1` yields the dual estimate `|F(x)| ≤ ∑ cₙ |F(yₙ)|` for `F ∈ U_q°` and `s(x) ≤ 1`. -/
private theorem dual_bound_of_expansion {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (q s : Seminorm ℂ E) (h : ℕ → StrongDual ℂ E) (y : ℕ → E)
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c) (hh : ∀ n x, ‖h n x‖ ≤ s x)
    (hy : ∀ n, q (y n) ≤ 1)
    (hexp : ∀ x, Tendsto (fun N => q (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n))
      atTop (𝓝 0))
    (F : StrongDual ℂ E) (hF : ∀ x, ‖F x‖ ≤ q x) (x : E) (hx : s x ≤ 1) :
    ‖F x‖ ≤ ∑' n, c n * ‖F (y n)‖ := by
  have hFy : ∀ n, ‖F (y n)‖ ≤ 1 := fun n => (hF _).trans (hy n)
  have hsum : Summable (fun n => c n * ‖F (y n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (norm_nonneg _))
      (fun n => ?_) hcs
    simpa using mul_le_mul_of_nonneg_left (hFy n) (hc0 n)
  set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, (c n * h n x) * F (y n) with hS
  -- the partial sums `S N` converge to `F x`
  have hlim : Tendsto S atTop (𝓝 (F x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (hexp x)
    have : F x - S N = F (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n) := by
      simp [hS, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [norm_sub_rev, this]
    exact hF _
  have hbound : ∀ N, ‖S N‖ ≤ ∑' n, c n * ‖F (y n)‖ := by
    intro N
    calc ‖S N‖ ≤ ∑ n ∈ Finset.range N, ‖(c n * h n x) * F (y n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, c n * ‖F (y n)‖ := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
          have h1 : ‖h n x‖ ≤ 1 := (hh n x).trans hx
          calc c n * ‖h n x‖ * ‖F (y n)‖ ≤ c n * 1 * ‖F (y n)‖ := by
                gcongr
                · exact hc0 n
            _ = c n * ‖F (y n)‖ := by ring
      _ ≤ ∑' n, c n * ‖F (y n)‖ :=
          hsum.sum_le_tsum _ (fun n _ => mul_nonneg (hc0 n) (norm_nonneg _))
  exact le_of_tendsto' hlim.norm hbound

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
      Continuous p ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
        ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  -- `q` is quasi-nuclearly dominated by `r`, and `r` by `s`
  obtain ⟨r, f, a, hr, ha, has, hf, hqr⟩ := nuclear_quasinuclear_domination E hE q hq
  obtain ⟨s, g, b, hs, hb, hbs, hg, hrs⟩ := nuclear_quasinuclear_domination E hE r hr
  -- the product of the two quasi-nuclear canonical maps is nuclear
  obtain ⟨h, y, c, hc0, hcs, hh, hy, hexp⟩ :=
    quasinuclear_comp_nuclear_expansion E q r s f a ha has hf hqr g b hb hbs hg hrs
  exact ⟨s, y, c, hs, hc0, hcs, hy, fun F hF x hx =>
    dual_bound_of_expansion q s h y c hc0 hcs hh hy hexp F hF x hx⟩
