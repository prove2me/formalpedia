-- Prove2me | solution 1 for NumStochOpt.QuasiFejer.proof_6_2_one_step_inequality
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T00:31:13.000673+00:00
-- url     : https://prove2.me/submissions/df122911-f120-4ad3-be7d-479b6a9403d1

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

def sf_filtration {Ω : Type*} [m : MeasurableSpace Ω] {n : ℕ}
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hz : ∀ s, Measurable (z s)) :
    Filtration ℕ m where
  seq := historySigma z
  mono' := by
    intro i j hij
    exact iSup_le fun k => iSup_le fun hki =>
      le_iSup_of_le k (le_iSup_of_le (hki.trans hij) le_rfl)
  le' := fun s => iSup_le fun k => iSup_le fun _ => (hz k).comap_le

lemma sf_history_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (s : ℕ) :
    @Measurable Ω _ (historySigma z s) _ (z s) :=
  Measurable.of_comap_le (le_iSup_of_le s (le_iSup_of_le le_rfl le_rfl))

lemma sf_distance_adapted {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hz : ∀ s, Measurable (z s))
    (w : EuclideanSpace ℝ (Fin n)) :
    StronglyAdapted (sf_filtration z hz) (fun s ω => ‖w - z s ω‖ ^ 2) := by
  intro s
  change StronglyMeasurable[historySigma z s] (fun ω => ‖w - z s ω‖ ^ 2)
  letI : MeasurableSpace Ω := historySigma z s
  exact ((measurable_const.sub (sf_history_measurable z s)).norm.pow_const 2).stronglyMeasurable

lemma sf_distance_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : Ω → EuclideanSpace ℝ (Fin n))
    (hz : MemLp z 2 μ) (w : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ω => ‖w - z ω‖ ^ 2) μ := by
  have h : MemLp (fun ω => w - z ω) 2 μ := (memLp_const w).sub hz
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace NumStochOpt.QuasiFejer

lemma sf_projection_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (y : EuclideanSpace ℝ (Fin n)) :
    projX X y ∈ X ∧ ∀ w ∈ X, ‖y - projX X y‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by
  classical
  letI : Nonempty X := hne.to_subtype
  have hb : BddBelow (Set.range (fun q : X => ‖y - q‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact norm_nonneg _
  obtain ⟨p, hp, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc y
  have hnorm (w) (hw : w ∈ X) : ‖y - p‖ ≤ ‖y - w‖ := by
    rw [heq]
    exact ciInf_le hb ⟨w, hw⟩
  have hex : ∃ p ∈ X, ∀ w ∈ X, ‖y - p‖ ^ 2 ≤ ‖y - w‖ ^ 2 :=
    ⟨p, hp, fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hnorm w hw) 2⟩
  simpa only [projX, dif_pos hex] using hex.choose_spec

lemma sf_projection_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (y w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ X) :
    ‖w - projX X y‖ ^ 2 ≤ ‖w - y‖ ^ 2 := by
  letI : Nonempty X := hne.to_subtype
  have hbd : BddBelow (Set.range (fun q : X => ‖y - q‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact norm_nonneg _
  obtain ⟨hp, hmin⟩ := sf_projection_spec X hc hcl hne y
  have heq : ‖y - projX X y‖ = ⨅ q : X, ‖y - q‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro q
      have := hmin q q.property
      nlinarith [norm_nonneg (y - projX X y), norm_nonneg (y - q)]
    · exact ciInf_le hbd ⟨_, hp⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hp).1 heq w hw
  have he : (y - projX X y) - (w - projX X y) = y - w := by abel
  have hh := norm_sub_sq_real (y - projX X y) (w - projX X y)
  rw [he, norm_sub_rev y w] at hh
  nlinarith [sq_nonneg ‖y - projX X y‖]

lemma sf_projection_step_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (w x ξ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hw : w ∈ X) :
    ‖w - projX X (x - ρ • ξ)‖ ^ 2 ≤
      ‖w - x‖ ^ 2 + 2 * ρ * ⟪ξ, w - x⟫_ℝ + ρ ^ 2 * ‖ξ‖ ^ 2 := by
  have h := sf_projection_bound X hc hcl hne (x - ρ • ξ) w hw
  have he : w - (x - ρ • ξ) = (w - x) + ρ • ξ := by abel
  rw [he, norm_add_sq_real, inner_smul_right, real_inner_comm ξ (w - x),
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  nlinarith

lemma sf_scaled_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ρ : Ω → ℝ) (ξ : Ω → EuclideanSpace ℝ (Fin n))
    (hm : AEStronglyMeasurable ρ μ) (hi : Integrable ξ μ)
    (hsq : Integrable (fun ω => ρ ω ^ 2 * ‖ξ ω‖ ^ 2) μ) :
    MemLp (fun ω => ρ ω • ξ ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (hm.smul hi.aestronglyMeasurable)).2
  simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hsq

lemma sf_inner_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) (f g : Ω → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω, g ω⟫_ℝ) μ := by
  exact memLp_one_iff_integrable.1 ((innerSL ℝ).memLp_of_bilin 1 hf hg)

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_one_step_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ) (s : ℕ)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X) (hXne : X.Nonempty)
    (hx_meas : ∀ k, Measurable (x k)) (hx_L2 : MemLp (x s) 2 μ)
    (hξ_int : Integrable (ξ s) μ)
    (hρξ_int : Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ)
    (hρ_adapt : StronglyMeasurable[historySigma x s] (ρ s))
    (hrec : ∀ ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    condExp (historySigma x s) μ (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2)
      ≤ᵐ[μ] fun ω => ‖xstar - x s ω‖ ^ 2
          + 2 * ρ s ω * ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ
          + (condExp (historySigma x s) μ (fun ω' => ρ s ω' ^ 2 * ‖ξ s ω'‖ ^ 2)) ω := by
  let ℱ := sf_filtration x hx_meas
  have hm : historySigma x s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hρm : AEStronglyMeasurable (ρ s) μ := (hρ_adapt.mono hm).aestronglyMeasurable
  have hp := sf_scaled_memLp μ (ρ s) (ξ s) hρm hξ_int hρξ_int
  have hd : MemLp (fun ω => xstar - x s ω) 2 μ := (memLp_const xstar).sub hx_L2
  have hdi := sf_distance_integrable μ (x s) hx_L2 xstar
  have hcross := sf_inner_integrable μ (fun ω => ρ s ω • ξ s ω)
    (fun ω => xstar - x s ω) hp hd
  let g : Ω → EuclideanSpace ℝ (Fin n) := fun ω => (2 * ρ s ω) • (xstar - x s ω)
  have hga : StronglyMeasurable[historySigma x s] g := by
    letI : MeasurableSpace Ω := historySigma x s
    exact (stronglyMeasurable_const.mul hρ_adapt).smul
      (stronglyMeasurable_const.sub (sf_history_measurable x s).stronglyMeasurable)
  have hgξ : Integrable (fun ω => ⟪g ω, ξ s ω⟫_ℝ) μ := by
    convert hcross.const_mul 2 using 1
    funext ω
    simp only [g, real_inner_smul_left, real_inner_comm (ξ s ω) (xstar - x s ω)]
    ring
  have hnext : Integrable (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2) μ := by
    have hy : MemLp (fun ω => x s ω - ρ s ω • ξ s ω) 2 μ := hx_L2.sub hp
    apply (sf_distance_integrable μ _ hy xstar).mono_nonneg
      (((measurable_const.sub (hx_meas (s + 1))).norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun _ => sq_nonneg _)
    exact ae_of_all _ fun ω => by
      simp only [Pi.sub_apply]
      rw [hrec ω]
      exact sf_projection_bound X hXconv hXclosed hXne _ xstar hxstar
  have hupperi : Integrable (fun ω => ‖xstar - x s ω‖ ^ 2 + ⟪g ω, ξ s ω⟫_ℝ +
      ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ := (hdi.add hgξ).add hρξ_int
  have hpoint : (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2) ≤ᵐ[μ]
      (fun ω => ‖xstar - x s ω‖ ^ 2 + ⟪g ω, ξ s ω⟫_ℝ +
        ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) := by
    apply ae_of_all
    intro ω
    dsimp only
    rw [hrec ω]
    simpa only [g, real_inner_smul_left, real_inner_comm (ξ s ω) (xstar - x s ω)] using
      sf_projection_step_bound X hXconv hXclosed hXne xstar (x s ω) (ξ s ω) (ρ s ω) hxstar
  have hmono := condExp_mono (m := historySigma x s) hnext hupperi hpoint
  have hpull := condExp_bilin_of_stronglyMeasurable_left (B := innerSL ℝ) hga hgξ hξ_int
  have had := sf_distance_adapted x hx_meas xstar s
  filter_upwards [hmono, hpull,
    condExp_add (hdi.add hgξ) hρξ_int (historySigma x s),
    condExp_add hdi hgξ (historySigma x s)] with ω h h1 h2 h3
  change μ[(fun ω => ‖xstar - x (s + 1) ω‖ ^ 2) | historySigma x s] ω ≤
    μ[((fun ω => ‖xstar - x s ω‖ ^ 2) + (fun ω => ⟪g ω, ξ s ω⟫_ℝ)) +
      (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) | historySigma x s] ω at h
  rw [h2] at h
  simp only [Pi.add_apply] at h
  rw [h3] at h
  simp only [Pi.add_apply] at h
  rw [condExp_of_stronglyMeasurable hm had hdi] at h
  change μ[(fun ω => ⟪g ω, ξ s ω⟫_ℝ) | historySigma x s] ω =
    ⟪g ω, μ[ξ s | historySigma x s] ω⟫_ℝ at h1
  rw [h1] at h
  simpa only [g, innerSL_apply_apply, real_inner_smul_left,
    real_inner_comm _ (xstar - x s ω)] using h

end NumStochOpt.QuasiFejer

open NumStochOpt.QuasiFejer

/-- **One-step inequality of the projection method** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988),
proof of Theorem 6.2, p. 145, first display). Let `X` be a nonempty closed convex set and
`x^{s+1} = π_X(x^s - ρ_s ξ⁰(s))` with `ρ_s` measurable with respect to `σ(x⁰, …, x^s)`. Then for
every `x* ∈ X`, almost surely,
`E{‖x* - x^{s+1}‖² | x⁰, …, x^s} ≤ ‖x* - x^s‖² + 2ρ_s⟨E{ξ⁰(s) | x⁰, …, x^s}, x* - x^s⟩
  + E{ρ_s² ‖ξ⁰(s)‖² | x⁰, …, x^s}`.
The page prints the last term as `ρ_s E{‖ξ⁰(s)‖² | …}`; the square on `ρ_s` is restored here
(it is `ρ_s²` in the next display and in (6.15)). -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ) (s : ℕ)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X) (hXne : X.Nonempty)
    (hx_meas : ∀ k, Measurable (x k)) (hx_L2 : MemLp (x s) 2 μ)
    (hξ_int : Integrable (ξ s) μ)
    (hρξ_int : Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ)
    (hρ_adapt : StronglyMeasurable[historySigma x s] (ρ s))
    (hrec : ∀ ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    condExp (historySigma x s) μ (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2)
      ≤ᵐ[μ] fun ω => ‖xstar - x s ω‖ ^ 2
          + 2 * ρ s ω * ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ
          + (condExp (historySigma x s) μ (fun ω' => ρ s ω' ^ 2 * ‖ξ s ω'‖ ^ 2)) ω := by
  exact sf_one_step_result μ X x ξ ρ s hXconv hXclosed hXne hx_meas hx_L2 hξ_int hρξ_int hρ_adapt hrec xstar hxstar

#print axioms solution
