-- Prove2me | solution 1 for LocallyConvexDuality.barrelledSpace_iff_eq_strongTopology
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:12:12.390065+00:00
-- url     : https://prove2.me/submissions/b78c827e-30e3-4a9f-9344-36c98e01655e

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

namespace Sol_LocallyConvexDuality_barrelledSpace_iff_eq_strongTopology

open Topology LocallyConvexDuality

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

/-- A set of continuous linear functionals is bounded for the weak-`*` topology `σ(E', E)` iff it is
pointwise bounded. -/
theorem isVonNBounded_iff {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] (A : Set (E →L[𝕜] 𝕜)) :
    Bornology.IsVonNBounded (E := WeakBilin (topDualPairing 𝕜 E).flip.flip) 𝕜 A ↔
      ∀ x : E, ∃ r > 0, ∀ f ∈ A, ‖f x‖ < r := by
  exact WithSeminorms.isVonNBounded_iff_seminorm_bounded
    (E := WeakBilin (topDualPairing 𝕜 E).flip.flip)
    ((topDualPairing 𝕜 E).flip.flip.weakBilin_withSeminorms)

/-- The given topology `t` is finer than `β(E, E')` iff every `σ(E', E)`-bounded subset of the dual
is equicontinuous. -/
theorem le_strongTopology_iff {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] :
    t ≤ strongTopology (topDualPairing 𝕜 E).flip ↔
      ∀ A : Set (E →L[𝕜] 𝕜),
        Bornology.IsVonNBounded (E := WeakBilin (topDualPairing 𝕜 E).flip.flip) 𝕜 A →
          Equicontinuous (fun f : A => ((f : E →L[𝕜] 𝕜) : E → 𝕜)) := by
  unfold strongTopology polarTopology
  rw [← continuous_iff_le_induced, UniformOnFun.topologicalSpace_eq]
  simp only [continuous_iInf_rng, continuous_induced_rng]
  refine forall₂_congr fun A hA => ?_
  rw [equicontinuous_iff_continuous]
  rfl

/-- On a locally convex space the strong topology `β(E, E')` is finer than the given topology. -/
theorem strongTopology_le {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] :
    strongTopology (topDualPairing 𝕜 E).flip ≤ t := by
  rw [le_iff_nhds]
  intro x₀ N hN
  obtain ⟨s, r, hr, hsub⟩ := ((PolynormableSpace.withSeminorms 𝕜 E).mem_nhds_iff x₀ N).mp hN
  set q : Seminorm 𝕜 E := s.sup (fun p : {p : Seminorm 𝕜 E // Continuous p} => p.1) with hq_def
  have hq : Continuous q :=
    Seminorm.continuous (r := 1)
      (((PolynormableSpace.withSeminorms 𝕜 E).mem_nhds_iff 0 _).mpr ⟨s, 1, one_pos, subset_rfl⟩)
  have hH : {g : E →L[𝕜] 𝕜 | ∀ y, ‖g y‖ ≤ q y} ∈
      {A : Set (E →L[𝕜] 𝕜) |
        Bornology.IsVonNBounded (E := WeakBilin (topDualPairing 𝕜 E).flip.flip) 𝕜 A} :=
    (isVonNBounded_iff _).mpr fun x =>
      ⟨q x + 1, add_pos_of_nonneg_of_pos (apply_nonneg q x) one_pos,
        fun f hf => lt_of_le_of_lt (hf x) (lt_add_one _)⟩
  unfold strongTopology polarTopology
  rw [nhds_induced]
  refine Filter.mem_comap.mpr
    ⟨_, UniformOnFun.gen_mem_nhds _ _ _ hH (Metric.dist_mem_uniformity (half_pos hr)), ?_⟩
  intro x hx
  apply hsub
  rw [Seminorm.mem_ball]
  by_contra hlt
  have hr2 : 0 < r / 2 := half_pos hr
  have hrn : ‖(((r / 2 : ℝ) : 𝕜))⁻¹‖ = (r / 2)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hr2]
  have hz : 1 < q ((((r / 2 : ℝ) : 𝕜))⁻¹ • (x - x₀)) := by
    rw [map_smul_eq_mul, hrn, lt_inv_mul_iff₀ hr2, mul_one]
    exact lt_of_lt_of_le (half_lt_self hr) (not_lt.mp hlt)
  obtain ⟨g, hg, hg1⟩ := exists_dominated_functional q hq.lowerSemicontinuous hz
  have h1 : dist (g x₀) (g x) < r / 2 := hx g hg
  rw [map_smul, norm_smul, hrn, lt_inv_mul_iff₀ hr2, mul_one, map_sub, ← dist_eq_norm,
    dist_comm] at hg1
  exact lt_irrefl _ (hg1.trans h1)

end Sol_LocallyConvexDuality_barrelledSpace_iff_eq_strongTopology

open Sol_LocallyConvexDuality_barrelledSpace_iff_eq_strongTopology in
theorem solution {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] :
    BarrelledSpace 𝕜 E ↔ LocallyConvexDuality.strongTopology (topDualPairing 𝕜 E).flip = t := by
  constructor
  · intro hB
    refine le_antisymm strongTopology_le (le_strongTopology_iff.mpr fun A hA => ?_)
    let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    have key : UniformEquicontinuous
        ((↑) ∘ (fun f : A => (f : E →L[𝕜] 𝕜)) : A → E → 𝕜) := by
      refine (norm_withSeminorms 𝕜 𝕜).banach_steinhaus ?_
      intro k x
      obtain ⟨C, -, hC⟩ := (isVonNBounded_iff A).mp hA x
      refine ⟨C, ?_⟩
      rintro _ ⟨f, rfl⟩
      exact (hC f.1 f.2).le
    exact key.equicontinuous
  · intro h
    have hequi := le_strongTopology_iff.mp h.ge
    refine ⟨fun p hp => ?_⟩
    have hbdd : Bornology.IsVonNBounded (E := WeakBilin (topDualPairing 𝕜 E).flip.flip) 𝕜
        {g : E →L[𝕜] 𝕜 | ∀ y, ‖g y‖ ≤ p y} :=
      (isVonNBounded_iff _).mpr fun x =>
        ⟨p x + 1, add_pos_of_nonneg_of_pos (apply_nonneg p x) one_pos,
          fun f hf => lt_of_le_of_lt (hf x) (lt_add_one _)⟩
    have heq := hequi _ hbdd
    have hev := heq 0 _ (Metric.dist_mem_uniformity one_pos)
    refine Seminorm.continuous' (r := 1) ?_
    filter_upwards [hev] with x hx
    rw [p.mem_closedBall_zero]
    by_contra hlt
    obtain ⟨g, hg, hg1⟩ := exists_dominated_functional p hp (not_le.mp hlt)
    have h4 := hx ⟨g, hg⟩
    simp only [map_zero, dist_zero_left] at h4
    exact absurd hg1 (not_lt.mpr h4.le)
