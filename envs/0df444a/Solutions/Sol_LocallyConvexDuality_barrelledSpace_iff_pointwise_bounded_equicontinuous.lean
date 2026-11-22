-- Prove2me | solution 1 for LocallyConvexDuality.barrelledSpace_iff_pointwise_bounded_equicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:02:30.515626+00:00
-- url     : https://prove2.me/submissions/00b27420-7c37-40a0-91b3-4824fc0059cf

import Mathlib

set_option autoImplicit false

namespace Sol_LocallyConvexDuality_barrelledSpace_iff_pointwise_bounded_equicontinuous

open Topology

/-- Hahn–Banach for a lower semicontinuous seminorm `p` on a locally convex space: a point `x₀`
outside the closed unit ball of `p` is detected by a continuous linear functional dominated
by `p`. -/
theorem exists_dominated_functional {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) {x₀ : E} (hx₀ : 1 < p x₀) :
    ∃ g : StrongDual 𝕜 E, (∀ x, ‖g x‖ ≤ p x) ∧ 1 < ‖g x₀‖ := by
  let : Module ℝ E := Module.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  have : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  -- the closed unit ball of `p` is closed and convex
  have hclosed : IsClosed (p.closedBall 0 1) := by
    rw [p.closedBall_zero_eq]
    exact hp.isClosed_preimage 1
  have hconv : Convex ℝ (p.closedBall 0 1) := p.convex_closedBall 0 1
  have hx₀' : x₀ ∉ p.closedBall 0 1 := by
    rw [p.mem_closedBall_zero]
    exact not_le.mpr hx₀
  obtain ⟨f, u, hfu, hux⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hconv hclosed hx₀'
  have hu : 0 < u := by
    have := hfu 0 (by rw [p.mem_closedBall_zero]; simp)
    simpa using this
  -- `‖f a‖ < u` on the unit ball of `p`, by rotating `a`
  have hnorm : ∀ a, p a ≤ 1 → ‖f a‖ < u := by
    intro a ha
    by_cases h0 : f a = 0
    · simpa [h0] using hu
    · have hne : (‖f a‖ : 𝕜) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.mpr h0)
      set c : 𝕜 := (starRingEnd 𝕜) (f a) / (‖f a‖ : 𝕜) with hc_def
      have hc : ‖c‖ = 1 := by
        rw [hc_def, norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm]
        exact div_self (norm_ne_zero_iff.mpr h0)
      have hmem : c • a ∈ p.closedBall 0 1 := by
        rw [p.mem_closedBall_zero, map_smul_eq_mul, hc, one_mul]
        exact ha
      have h1 := hfu (c • a) hmem
      have h2 : f (c • a) = ((‖f a‖ : ℝ) : 𝕜) := by
        rw [map_smul, smul_eq_mul, hc_def, div_mul_eq_mul_div, RCLike.conj_mul]
        rw [sq, mul_div_assoc, div_self hne, mul_one]
      rw [h2, RCLike.ofReal_re] at h1
      exact h1
  -- normalise: `g = u⁻¹ • f`
  have hnu : ‖((u : 𝕜))⁻¹‖ = u⁻¹ := by
    rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hu]
  have hg_apply : ∀ a, ‖(((u : 𝕜))⁻¹ • f) a‖ = u⁻¹ * ‖f a‖ := by
    intro a
    rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, hnu]
  have hle1 : ∀ a, p a ≤ 1 → ‖(((u : 𝕜))⁻¹ • f) a‖ ≤ 1 := by
    intro a ha
    rw [hg_apply a, inv_mul_le_iff₀ hu, mul_one]
    exact (hnorm a ha).le
  refine ⟨((u : 𝕜))⁻¹ • f, ?_, ?_⟩
  · intro x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hr : 0 < p x + ε := add_pos_of_nonneg_of_pos (apply_nonneg p x) hε
    have hrn : ‖(((p x + ε : ℝ) : 𝕜))⁻¹‖ = (p x + ε)⁻¹ := by
      rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hr]
    have hpa : p ((((p x + ε : ℝ) : 𝕜))⁻¹ • x) ≤ 1 := by
      rw [map_smul_eq_mul, hrn, inv_mul_le_iff₀ hr, mul_one]
      exact le_add_of_nonneg_right hε.le
    have h3 := hle1 _ hpa
    rw [map_smul, norm_smul, hrn, inv_mul_le_iff₀ hr, mul_one] at h3
    exact h3
  · rw [hg_apply x₀, lt_inv_mul_iff₀ hu, mul_one]
    exact hux.trans_le (RCLike.re_le_norm (f x₀))

end Sol_LocallyConvexDuality_barrelledSpace_iff_pointwise_bounded_equicontinuous

theorem solution {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] :
    BarrelledSpace 𝕜 E ↔
      ∀ H : Set (StrongDual 𝕜 E),
        (∀ x : E, Bornology.IsBounded ((fun f : StrongDual 𝕜 E => f x) '' H)) →
          Equicontinuous (fun f : H => ((f : StrongDual 𝕜 E) : E → 𝕜)) := by
  constructor
  · intro hB H hH
    let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    have key : UniformEquicontinuous
        ((↑) ∘ (fun f : H => (f : StrongDual 𝕜 E)) : H → E → 𝕜) := by
      refine (norm_withSeminorms 𝕜 𝕜).banach_steinhaus ?_
      intro k x
      obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.mp (hH x))
      refine ⟨C, ?_⟩
      rintro _ ⟨f, rfl⟩
      exact hC _ ⟨f.1, f.2, rfl⟩
    exact key.equicontinuous
  · intro h
    refine ⟨fun p hp => ?_⟩
    -- the set of continuous functionals dominated by `p`
    have hbdd : ∀ x : E, Bornology.IsBounded
        ((fun f : StrongDual 𝕜 E => f x) '' {g : StrongDual 𝕜 E | ∀ y, ‖g y‖ ≤ p y}) := by
      intro x
      refine (Metric.isBounded_closedBall (x := (0 : 𝕜)) (r := p x)).subset ?_
      rintro _ ⟨g, hg, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact hg x
    have heq := h {g : StrongDual 𝕜 E | ∀ y, ‖g y‖ ≤ p y} hbdd
    have hev := heq 0 _ (Metric.dist_mem_uniformity one_pos)
    refine Seminorm.continuous' (r := 1) ?_
    filter_upwards [hev] with x hx
    rw [p.mem_closedBall_zero]
    by_contra hlt
    obtain ⟨g, hg, hg1⟩ :=
      Sol_LocallyConvexDuality_barrelledSpace_iff_pointwise_bounded_equicontinuous.exists_dominated_functional
        p hp (not_le.mp hlt)
    have h4 := hx ⟨g, hg⟩
    simp only [map_zero, dist_zero_left] at h4
    exact absurd hg1 (not_lt.mpr h4.le)
