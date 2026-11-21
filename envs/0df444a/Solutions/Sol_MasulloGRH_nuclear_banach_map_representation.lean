-- Prove2me | solution 1 for MasulloGRH.nuclear_banach_map_representation
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:26:45.77335+00:00
-- url     : https://prove2.me/submissions/283a7257-92cf-44f6-b158-969504ddec15

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_quasinuclear_comp_nuclear_expansion

set_option autoImplicit false

open MasulloGRH
open Filter Topology

theorem solution (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (hE : IsNuclear E) (u : E →L[ℂ] H) :
    ∃ (p : Seminorm ℂ E) (φ : ℕ → StrongDual ℂ E) (v : ℕ → H) (c : ℕ → ℂ),
      Continuous p ∧ (∀ n x, ‖φ n x‖ ≤ p x) ∧ (∀ n, ‖v n‖ ≤ 1) ∧
      Summable (fun n => ‖c n‖) ∧ ∀ x, HasSum (fun n => (c n * φ n x) • v n) (u x) := by
  -- the continuous seminorm `q(x) = ‖u x‖`
  set q : Seminorm ℂ E := (normSeminorm ℂ H).comp (u : E →ₗ[ℂ] H) with hqdef
  have hqx : ∀ x, q x = ‖u x‖ := fun x => rfl
  have hq : Continuous q := by
    have : (q : E → ℝ) = fun x => ‖u x‖ := funext hqx
    rw [this]; exact u.continuous.norm
  obtain ⟨r, f, a, hr, ha, has, hf, hqr⟩ := nuclear_quasinuclear_domination E hE q hq
  obtain ⟨s, g, b, hs, hb, hbs, hg, hrs⟩ := nuclear_quasinuclear_domination E hE r hr
  obtain ⟨h, y, c, hc0, hcs, hh, hy, hexp⟩ :=
    quasinuclear_comp_nuclear_expansion E q r s f a ha has hf hqr g b hb hbs hg hrs
  refine ⟨s, h, fun n => u (y n), fun n => (c n : ℂ), hs, hh, fun n => ?_, ?_, fun x => ?_⟩
  · rw [← hqx]; exact hy n
  · simpa [Complex.norm_real, Real.norm_of_nonneg (hc0 _)] using hcs
  · -- absolute summability
    have hbd : ∀ n, ‖((c n : ℂ) * h n x) • u (y n)‖ ≤ c n * s x := by
      intro n
      rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
      have h1 : ‖u (y n)‖ ≤ 1 := by rw [← hqx]; exact hy n
      calc c n * ‖h n x‖ * ‖u (y n)‖ ≤ c n * s x * 1 := by
            have h2 := hh n x
            have h3 : 0 ≤ c n * ‖h n x‖ := mul_nonneg (hc0 n) (norm_nonneg _)
            calc c n * ‖h n x‖ * ‖u (y n)‖ ≤ c n * ‖h n x‖ * 1 :=
                  mul_le_mul_of_nonneg_left h1 h3
              _ ≤ c n * s x * 1 := by
                  rw [mul_one, mul_one]; exact mul_le_mul_of_nonneg_left h2 (hc0 n)
        _ = c n * s x := mul_one _
    have hsum : Summable (fun n => ((c n : ℂ) * h n x) • u (y n)) :=
      Summable.of_norm_bounded (hcs.mul_right (s x)) hbd
    -- the partial sums converge to `u x`
    have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • u (y n))
        atTop (𝓝 (u x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (hexp x)
      rw [norm_sub_rev, hqx]
      simp [map_sub, map_sum, map_smul]
    have heq : ∑' n, ((c n : ℂ) * h n x) • u (y n) = u x :=
      tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
    rw [← heq]; exact hsum.hasSum
