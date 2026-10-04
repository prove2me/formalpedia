-- Prove2me | solution 1 for NumStochOpt.QuasiFejer.proof_6_2_quasi_fejer_for_optimal_set
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T00:44:06.455446+00:00
-- url     : https://prove2.me/submissions/3d92e658-9c00-4d0f-904e-fd0ac4c6250c

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


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_iterates_mem {Ω : Type*} {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hc : Convex ℝ X) (hcl : IsClosed X)
    (hne : X.Nonempty) (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ)
    (hx0 : ∀ ω, x 0 ω ∈ X)
    (hr : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω)) :
    ∀ s ω, x s ω ∈ X := by
  intro s ω
  cases s with
  | zero => exact hx0 ω
  | succ s => rw [hr]; exact (sf_projection_spec X hc hcl hne _).1

lemma sf_compact_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsCompact X) (x : Ω → EuclideanSpace ℝ (Fin n))
    (hm : Measurable x) (hx : ∀ ω, x ω ∈ X) : MemLp x 2 μ := by
  obtain ⟨B, hB⟩ := hX.isBounded.exists_norm_le
  exact MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun ω => hB _ (hx ω))

noncomputable def sf_error {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (ρ γ : ℕ → Ω → ℝ) (s : ℕ) : Ω → ℝ :=
  μ[(fun ω => 2 * ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) | historySigma x s]

lemma sf_error_data {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ)
    (hx : ∀ s, Measurable (x s)) (hξ : ∀ s, Integrable (ξ s) μ)
    (hρ : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : ∀ s, StronglyMeasurable[historySigma x s] (γ s))
    (hρn : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal
      (ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    (∀ s, Integrable (fun ω => ρ s ω * |γ s ω|) μ) ∧
    (∀ s, Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ) ∧
    (∀ s, Measurable (sf_error μ x ξ ρ γ s)) ∧
    (∀ s, 0 ≤ᵐ[μ] sf_error μ x ξ ρ γ s) ∧
    (∑' s, ∫⁻ ω, ENNReal.ofReal (sf_error μ x ξ ρ γ s ω) ∂μ) < ⊤ := by
  let ℱ := sf_filtration x hx
  let a : ℕ → Ω → ℝ := fun s ω => ρ s ω * |γ s ω|
  let b : ℕ → Ω → ℝ := fun s ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2
  have ham (s) : AEStronglyMeasurable (a s) μ :=
    by
      convert (((hρ s).mono (ℱ.le s)).aestronglyMeasurable.mul
        (((hγ s).mono (ℱ.le s)).aestronglyMeasurable.norm)) using 1
      funext ω
      simp [a, Real.norm_eq_abs]
  have hbm (s) : AEStronglyMeasurable (b s) μ :=
    (((hρ s).mono (ℱ.le s)).aestronglyMeasurable.pow 2).mul
      ((hξ s).aestronglyMeasurable.norm.pow 2)
  have han (s) : 0 ≤ᵐ[μ] a s := hρn.mono fun ω h => mul_nonneg (h s) (abs_nonneg _)
  have hbn (s) : 0 ≤ᵐ[μ] b s := ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have habi (s) : Integrable (fun ω => a s ω + b s ω) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable ((ham s).add (hbm s)) ?_).1
      (ne_of_lt ((ENNReal.le_tsum s).trans_lt hsum))
    filter_upwards [han s, hbn s] with ω ha hb
    exact add_nonneg ha hb
  have hai (s) : Integrable (a s) μ := (habi s).mono_nonneg (ham s) (han s)
    ((hbn s).mono fun _ hb => le_add_of_nonneg_right hb)
  have hbi (s) : Integrable (b s) μ := (habi s).mono_nonneg (hbm s) (hbn s)
    ((han s).mono fun _ ha => le_add_of_nonneg_left ha)
  let e : ℕ → Ω → ℝ := fun s ω => 2 * a s ω + b s ω
  have hei (s) : Integrable (e s) μ := ((hai s).const_mul 2).add (hbi s)
  have hen (s) : 0 ≤ᵐ[μ] e s := by
    filter_upwards [han s, hbn s] with ω ha hb
    exact add_nonneg (mul_nonneg (by norm_num) ha) hb
  have her (s) : sf_error μ x ξ ρ γ s = μ[e s | historySigma x s] := by
    unfold sf_error
    congr 1
    funext ω
    dsimp [e, a, b]
    ring
  have hrn (s) : 0 ≤ᵐ[μ] sf_error μ x ξ ρ γ s := by
    rw [her]; exact condExp_nonneg (hen s)
  have heint (s) : (∫ ω, sf_error μ x ξ ρ γ s ω ∂μ) = ∫ ω, e s ω ∂μ := by
    rw [her s]
    have hm : historySigma x s ≤ ‹MeasurableSpace Ω› := ℱ.le s
    letI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    exact integral_condExp hm
  refine ⟨hai, hbi, fun s => ?_, hrn, ?_⟩
  · rw [her]
    exact (stronglyMeasurable_condExp.mono (ℱ.le s)).measurable
  · have hle (s) : (∫⁻ ω, ENNReal.ofReal (sf_error μ x ξ ρ γ s ω) ∂μ) ≤
        2 * ∫⁻ ω, ENNReal.ofReal (a s ω + b s ω) ∂μ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (by rw [her]; exact integrable_condExp) (hrn s),
        heint s, ofReal_integral_eq_lintegral_ofReal (hei s) (hen s)]
      calc
        _ ≤ ∫⁻ ω, ENNReal.ofReal (2 * (a s ω + b s ω)) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hbn s] with ω hb
          apply ENNReal.ofReal_le_ofReal
          change 0 ≤ b s ω at hb
          dsimp only [e]
          linarith
        _ = _ := by
          simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [lintegral_const_mul' (ENNReal.ofReal 2)
            (fun ω => ENNReal.ofReal (a s ω + b s ω)) ENNReal.ofReal_ne_top]
          norm_num
    calc
      _ ≤ ∑' s, 2 * ∫⁻ ω, ENNReal.ofReal (a s ω + b s ω) ∂μ := ENNReal.tsum_le_tsum hle
      _ = 2 * ∑' s, ∫⁻ ω, ENNReal.ofReal (a s ω + b s ω) ∂μ := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hsum

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_descent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ) (s : ℕ)
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (hx : ∀ k, Measurable (x k)) (hxl : MemLp (x s) 2 μ) (hξ : Integrable (ξ s) μ)
    (ha : Integrable (fun ω => ρ s ω * |γ s ω|) μ)
    (hb : Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ)
    (hρ : StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : StronglyMeasurable[historySigma x s] (γ s))
    (hρn : 0 ≤ᵐ[μ] ρ s)
    (hr : ∀ ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ X)
    (hq : ∀ᵐ ω ∂μ, F w - F (x s ω) ≥
      ⟪μ[ξ s | historySigma x s] ω, w - x s ω⟫_ℝ + γ s ω) :
    μ[(fun ω => ‖w - x (s + 1) ω‖ ^ 2) | historySigma x s] ≤ᵐ[μ]
      fun ω => ‖w - x s ω‖ ^ 2 - 2 * ρ s ω * (F (x s ω) - F w) +
        sf_error μ x ξ ρ γ s ω := by
  let ℱ := sf_filtration x hx
  let a : Ω → ℝ := fun ω => 2 * (ρ s ω * |γ s ω|)
  have hai : Integrable a μ := ha.const_mul 2
  have haa : StronglyMeasurable[historySigma x s] a := by
    letI : MeasurableSpace Ω := historySigma x s
    convert (stronglyMeasurable_const (b := (2 : ℝ))).mul (hρ.mul hγ.norm) using 1
    funext ω
    simp [a, Real.norm_eq_abs]
  have heq : (fun ω => 2 * ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) =
      a + (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) := by
    funext ω; dsimp [a]; ring
  have hm : historySigma x s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hca : μ[a | historySigma x s] = a := condExp_of_stronglyMeasurable hm haa hai
  have herror : sf_error μ x ξ ρ γ s =ᵐ[μ] fun ω =>
      a ω + μ[(fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) | historySigma x s] ω := by
    unfold sf_error
    rw [heq]
    exact (condExp_add hai hb (historySigma x s)).mono fun ω h => by
      rw [h, hca]
      rfl
  have hstep := sf_one_step_result μ X x ξ ρ s hc hcl hne hx hxl hξ hb hρ hr w hw
  filter_upwards [hstep, hq, hρn, herror] with ω h hq hρ herr
  rw [herr]
  have hn : 0 ≤ 2 * ρ s ω := mul_nonneg (by norm_num) hρ
  have h1 := mul_le_mul_of_nonneg_left hq hn
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (γ s ω)) hn
  dsimp [a]
  nlinarith

lemma sf_optimalset_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ)
    (hc : Convex ℝ X) (hX : IsCompact X) (hne : X.Nonempty)
    (hx : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ : ∀ s, Integrable (ξ s) μ)
    (hρ : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : ∀ s, StronglyMeasurable[historySigma x s] (γ s))
    (hr : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hq : ∀ w ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ, F w - F (x s ω) ≥
      ⟪μ[ξ s | historySigma x s] ω, w - x s ω⟫_ℝ + γ s ω)
    (hρn : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal
      (ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    IsStochQuasiFejer μ x (optimalSet F X) := by
  have hxm := sf_iterates_mem X hc hX.isClosed hne x ξ ρ hx0 hr
  have hxl (s) := sf_compact_memLp μ X hX (x s) (hx s) (hxm s)
  obtain ⟨hai, hbi, herm, hern, hers⟩ := sf_error_data μ x ξ ρ γ hx hξ hρ hγ hρn hsum
  refine ⟨hx, hxl, sf_error μ x ξ ρ γ, herm, hern, hers, ?_⟩
  intro w hw s
  have h := sf_descent μ F X x ξ ρ γ s hc hX.isClosed hne hx (hxl s) (hξ s)
    (hai s) (hbi s) (hρ s) (hγ s) (hρn.mono fun ω h => h s) (hr s) w hw.1 (hq w hw s)
  filter_upwards [h, hρn] with ω h hρ
  have hg : 0 ≤ F (x s ω) - F w := sub_nonneg.2 (hw.2 _ (hxm s ω))
  have ht : 0 ≤ 2 * ρ s ω * (F (x s ω) - F w) :=
    mul_nonneg (mul_nonneg (by norm_num) (hρ s)) hg
  linarith

end NumStochOpt.QuasiFejer

open NumStochOpt.QuasiFejer

/-- **The iterates form a stochastic quasi-Féjer sequence for `X*`** (Ermoliev, Ch. 6 of
Ermoliev & Wets (1988), proof of Theorem 6.2, p. 145, sentence after the second display).
For the stochastic quasigradient projection method (6.11) on a nonempty convex compact `X`, with
directions satisfying (6.12) for every `x* ∈ X*` and parameters satisfying `ρ_s ≥ 0` and
`∑_s E{ρ_s|γ₀(s)| + ρ_s²‖ξ⁰(s)‖²} < ∞` from (6.15), the sequence `{x^s}` is a stochastic
quasi-Féjer sequence (6.14) for the optimal set `X*`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ₀ : ℕ → Ω → ℝ)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hx_meas : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ_int : ∀ s, Integrable (ξ s) μ)
    (hρ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (γ₀ s))
    (hrec : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hqg : ∀ xstar ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ,
      F xstar - F (x s ω) ≥ ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ + γ₀ s ω)
    (hρ_nonneg : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (ρ s ω * |γ₀ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    IsStochQuasiFejer μ x (optimalSet F X) := by
  exact sf_optimalset_result μ F X x ξ ρ γ₀ hXconv hXcpt hXne hx_meas hx0 hξ_int hρ_adapt hγ_adapt hrec hqg hρ_nonneg hsum

#print axioms solution
