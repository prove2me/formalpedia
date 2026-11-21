-- Prove2me | solution 2 for MasulloGRH.strongDual_seminorm_le_polar
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:18:10.978517+00:00
-- url     : https://prove2.me/submissions/e0556b1e-0b4d-410a-82d4-683c788447ac

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (p : Seminorm ℂ (StrongDual ℂ E)) (hp : Continuous p) :
    ∃ (B : Set E) (C : ℝ), Bornology.IsVonNBounded ℂ B ∧ 0 ≤ C ∧
      ∀ (f : StrongDual ℂ E) (r : ℝ), 0 ≤ r → (∀ x ∈ B, ‖f x‖ ≤ r) → p f ≤ C * r := by
  obtain ⟨⟨ι, hι, ps, hps⟩, hT⟩ := hE
  have : ContinuousSMul ℂ E := hps.continuousSMul
  have hb := ContinuousLinearMap.hasBasis_nhds_zero_of_basis (σ := RingHom.id ℂ)
    (E := E) (Metric.nhds_basis_ball (x := (0 : ℂ)))
  obtain ⟨⟨B, ε⟩, ⟨hB, hε⟩, hsub⟩ := hb.mem_iff.mp (p.ball_mem_nhds hp zero_lt_one)
  refine ⟨B, ε⁻¹, hB, (inv_pos.mpr hε).le, ?_⟩
  intro f r hr hf
  apply le_of_forall_gt
  intro t ht
  have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (inv_nonneg.mpr hε.le) hr) ht
  have hrt : r < ε * t := (inv_mul_lt_iff₀ hε).mp ht
  have hg : ((t⁻¹ : ℝ) : ℂ) • f ∈ p.ball 0 1 := hsub (by
    intro x hx
    change dist (((t⁻¹ : ℝ) : ℂ) * f x) 0 < ε
    rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht0)]
    calc t⁻¹ * ‖f x‖ ≤ t⁻¹ * r := mul_le_mul_of_nonneg_left (hf x hx) (inv_nonneg.mpr ht0.le)
      _ < ε := by
        apply (inv_mul_lt_iff₀ ht0).mpr
        simpa [mul_comm] using hrt)
  have hpg : t⁻¹ * p f < 1 := by
    simpa only [Seminorm.mem_ball_zero, map_smul_eq_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)] using hg
  have : p f < t := by simpa only [mul_one] using (inv_mul_lt_iff₀ ht0).mp hpg
  exact this
