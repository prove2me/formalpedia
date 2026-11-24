-- Prove2me | solution 1 for GlobalTheory.LocalCube.exists_third_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:07.788965+00:00
-- url     : https://prove2.me/submissions/a79b0673-4501-4000-aa12-0e94a6a3fc8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SeriesApplyEqZeroOfFace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix Filter Topology Asymptotics
open scoped BigOperators Real
namespace GlobalTheory.LocalCube
open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma norm_le_div_mul_norm_of_schwarz {φ : ℂ → ℂ} {ρ c : ℝ}
    (hd : DifferentiableOn ℂ φ (Metric.ball 0 ρ)) (h0 : φ 0 = 0)
    (hc : ∀ t ∈ Metric.ball (0 : ℂ) ρ, ‖φ t‖ ≤ c) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ) :
    ‖φ t‖ ≤ c / ρ * ‖t‖ := by
  have hmap : Set.MapsTo φ (Metric.ball 0 ρ) (Metric.closedBall (φ 0) c) := by
    intro s hs
    rw [h0, mem_closedBall_zero_iff]
    exact hc s hs
  simpa [h0, dist_zero_right] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmap ht
open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma isBigO_norm_cube_of_analytic_vanishing_coords {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {u : (Fin 3 → V) → ℂ} (ha : AnalyticAt ℂ u 0)
    (hv : ∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → V), x a = 0 → u x = 0) :
    u =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
  have hu0 : u 0 = 0 := (hv 0).self_of_nhds rfl
  have hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → V),
      DifferentiableAt ℂ u x ∧ ‖u x‖ < 1 ∧ ∀ a, x a = 0 → u x = 0 := by
    have h1 : ∀ᶠ x in 𝓝 (0 : Fin 3 → V), DifferentiableAt ℂ u x :=
      ha.eventually_analyticAt.mono fun x hx => hx.differentiableAt
    have h2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → V), ‖u x‖ < 1 :=
      ha.continuousAt.norm.eventually (gt_mem_nhds (by simp [hu0]))
    exact h1.and (h2.and (Filter.eventually_all.2 hv))
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine IsBigO.of_bound (1 / R ^ 3) ?_
  filter_upwards [Metric.ball_mem_nhds 0 hR] with y hy
  simp only [norm_pow, norm_norm]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [hu0]
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hyR : ‖y‖ < R := mem_ball_zero_iff.1 hy
  set ρ := R / ‖y‖ with hρdef
  have hρ : 0 < ρ := div_pos hR hyn
  have hρ1 : 1 < ρ := (one_lt_div hyn).2 hyR
  let e : Fin 3 → (Fin 3 → V) := fun a => Pi.single a (y a)
  let p : ℂ → ℂ → ℂ → (Fin 3 → V) := fun t₀ t₁ t₂ => t₀ • e 0 + t₁ • e 1 + t₂ • e 2
  have hpa : ∀ t₀ t₁ t₂ a, p t₀ t₁ t₂ a = ![t₀, t₁, t₂] a • y a := by
    intro t₀ t₁ t₂ a
    fin_cases a <;> simp [p, e, Pi.single_apply]
  have hpb : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → p t₀ t₁ t₂ ∈ Metric.ball 0 R := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    rw [mem_ball_zero_iff, pi_norm_lt_iff hR]
    intro a
    rw [hpa, norm_smul]
    have hya : ‖y a‖ ≤ ‖y‖ := norm_le_pi_norm y a
    have hta : ‖![t₀, t₁, t₂] a‖ < ρ := by fin_cases a <;> simp [h₀, h₁, h₂]
    calc ‖![t₀, t₁, t₂] a‖ * ‖y a‖ ≤ ‖![t₀, t₁, t₂] a‖ * ‖y‖ :=
          mul_le_mul_of_nonneg_left hya (norm_nonneg _)
      _ < ρ * ‖y‖ := mul_lt_mul_of_pos_right hta hyn
      _ = R := by rw [hρdef]; field_simp
  let G : ℂ → ℂ → ℂ → ℂ := fun t₀ t₁ t₂ => u (p t₀ t₁ t₂)
  have hGb : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → ‖G t₀ t₁ t₂‖ ≤ 1 :=
    fun _ _ _ h₀ h₁ h₂ => (hball _ (hpb _ _ _ h₀ h₁ h₂)).2.1.le
  have hGz : ∀ t₀ t₁ t₂ (a : Fin 3), ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      ![t₀, t₁, t₂] a = 0 → G t₀ t₁ t₂ = 0 := by
    intro t₀ t₁ t₂ a h₀ h₁ h₂ ha0
    exact (hball _ (hpb _ _ _ h₀ h₁ h₂)).2.2 a (by rw [hpa, ha0, zero_smul])
  have hGd : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → DifferentiableAt ℂ u (p t₀ t₁ t₂) :=
    fun _ _ _ h₀ h₁ h₂ => (hball _ (hpb _ _ _ h₀ h₁ h₂)).1
  have hd₀ : ∀ t₁ t₂, ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      DifferentiableOn ℂ (fun s => G s t₁ t₂) (Metric.ball 0 ρ) := by
    intro t₁ t₂ h₁ h₂ s hs
    rw [mem_ball_zero_iff] at hs
    have hfd : DifferentiableAt ℂ (fun s : ℂ => p s t₁ t₂) s := by
      show DifferentiableAt ℂ (fun s : ℂ => s • e 0 + t₁ • e 1 + t₂ • e 2) s
      fun_prop
    exact (DifferentiableAt.comp s (hGd s t₁ t₂ hs h₁ h₂) hfd).differentiableWithinAt
  have hd₁ : ∀ t₀ t₂, ‖t₀‖ < ρ → ‖t₂‖ < ρ →
      DifferentiableOn ℂ (fun s => G t₀ s t₂) (Metric.ball 0 ρ) := by
    intro t₀ t₂ h₀ h₂ s hs
    rw [mem_ball_zero_iff] at hs
    have hfd : DifferentiableAt ℂ (fun s : ℂ => p t₀ s t₂) s := by
      show DifferentiableAt ℂ (fun s : ℂ => t₀ • e 0 + s • e 1 + t₂ • e 2) s
      fun_prop
    exact (DifferentiableAt.comp s (hGd t₀ s t₂ h₀ hs h₂) hfd).differentiableWithinAt
  have hd₂ : ∀ t₀ t₁, ‖t₀‖ < ρ → ‖t₁‖ < ρ →
      DifferentiableOn ℂ (fun s => G t₀ t₁ s) (Metric.ball 0 ρ) := by
    intro t₀ t₁ h₀ h₁ s hs
    rw [mem_ball_zero_iff] at hs
    have hfd : DifferentiableAt ℂ (fun s : ℂ => p t₀ t₁ s) s := by
      show DifferentiableAt ℂ (fun s : ℂ => t₀ • e 0 + t₁ • e 1 + s • e 2) s
      fun_prop
    exact (DifferentiableAt.comp s (hGd t₀ t₁ s h₀ h₁ hs) hfd).differentiableWithinAt
  have h0ρ : ‖(0 : ℂ)‖ < ρ := by simpa using hρ
  have S₁ : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → ‖G t₀ t₁ t₂‖ ≤ 1 / ρ * ‖t₀‖ := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    exact norm_le_div_mul_norm_of_schwarz (φ := fun s => G s t₁ t₂) (hd₀ t₁ t₂ h₁ h₂)
      (hGz 0 t₁ t₂ 0 h0ρ h₁ h₂ (by simp))
      (fun s hs => hGb s t₁ t₂ (mem_ball_zero_iff.1 hs) h₁ h₂) (mem_ball_zero_iff.2 h₀)
  have S₂ : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      ‖G t₀ t₁ t₂‖ ≤ 1 / ρ / ρ * ‖t₁‖ * ‖t₀‖ := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    rcases eq_or_ne t₀ 0 with rfl | ht₀
    · rw [hGz 0 t₁ t₂ 0 h₀ h₁ h₂ (by simp)]
      simp
    have hn : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀
    have hb : ∀ s ∈ Metric.ball (0 : ℂ) ρ, ‖G t₀ s t₂ / t₀‖ ≤ 1 / ρ := by
      intro s hs
      rw [norm_div, div_le_iff₀ hn]
      exact S₁ t₀ s t₂ h₀ (mem_ball_zero_iff.1 hs) h₂
    have key := norm_le_div_mul_norm_of_schwarz (φ := fun s => G t₀ s t₂ / t₀) ((hd₁ t₀ t₂ h₀ h₂).div_const t₀)
      (by simp only [hGz t₀ 0 t₂ 1 h₀ h0ρ h₂ (by simp), zero_div]) hb (mem_ball_zero_iff.2 h₁)
    beta_reduce at key
    rwa [norm_div, div_le_iff₀ hn] at key
  have S₃ : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      ‖G t₀ t₁ t₂‖ ≤ 1 / ρ / ρ / ρ * ‖t₂‖ * (‖t₁‖ * ‖t₀‖) := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    rcases eq_or_ne (t₁ * t₀) 0 with h | ht
    · rcases mul_eq_zero.1 h with rfl | rfl
      · rw [hGz t₀ 0 t₂ 1 h₀ h₁ h₂ (by simp)]
        simp
      · rw [hGz 0 t₁ t₂ 0 h₀ h₁ h₂ (by simp)]
        simp
    have hn : 0 < ‖t₁ * t₀‖ := norm_pos_iff.2 ht
    have hb : ∀ s ∈ Metric.ball (0 : ℂ) ρ, ‖G t₀ t₁ s / (t₁ * t₀)‖ ≤ 1 / ρ / ρ := by
      intro s hs
      rw [norm_div, div_le_iff₀ hn, norm_mul, ← mul_assoc]
      exact S₂ t₀ t₁ s h₀ h₁ (mem_ball_zero_iff.1 hs)
    have key := norm_le_div_mul_norm_of_schwarz (φ := fun s => G t₀ t₁ s / (t₁ * t₀))
      ((hd₂ t₀ t₁ h₀ h₁).div_const _)
      (by simp only [hGz t₀ t₁ 0 2 h₀ h₁ h0ρ (by simp), zero_div]) hb (mem_ball_zero_iff.2 h₂)
    beta_reduce at key
    rwa [norm_div, div_le_iff₀ hn, norm_mul] at key
  have h1 : ‖(1 : ℂ)‖ < ρ := by simpa using hρ1
  have hy1 : p 1 1 1 = y := by
    funext a
    rw [hpa]
    fin_cases a <;> simp
  have hG1 : G 1 1 1 = u y := congrArg u hy1
  have hfin := S₃ 1 1 1 h1 h1 h1
  rw [hG1] at hfin
  simp only [norm_one, mul_one] at hfin
  calc ‖u y‖ ≤ 1 / ρ / ρ / ρ := hfin
    _ = 1 / R ^ 3 * ‖y‖ ^ 3 := by rw [hρdef]; field_simp
open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma isBigO_norm_cube_comp_clm {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] {u : F' → ℂ}
    (hu : u =O[𝓝 0] fun z => ‖z‖ ^ 3) (T : E →L[ℂ] F') :
    (fun x => u (T x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
  have h1 : (fun x => u (T x)) =O[𝓝 0] fun x => ‖T x‖ ^ 3 :=
    hu.comp_tendsto (by simpa using T.continuous.tendsto 0)
  refine h1.trans (IsBigO.of_bound (‖T‖ ^ 3) (Eventually.of_forall fun x => ?_))
  simp only [norm_pow, norm_norm]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 3
open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma eventually_nhds_zero_comp_of_continuous {E F' : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace F'] [Zero F'] {T : E → F'} (hT : Continuous T) (h0 : T 0 = 0)
    {p : F' → Prop} (h : ∀ᶠ y in 𝓝 0, p y) : ∀ᶠ x in 𝓝 0, p (T x) :=
  (hT.tendsto' 0 0 h0).eventually h
end GlobalTheory.LocalCube
end

set_option autoImplicit false
open Complex Matrix Filter Topology Asymptotics
open scoped BigOperators Real
open GlobalTheory GlobalTheory.LocalCube
open Complex Matrix Filter Topology Asymptotics
open scoped BigOperators Real
namespace GlobalTheory.LocalCube
namespace _root_.GlobalTheory.LocalCube
theorem _root_.solution :
    (∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧ ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ), F =O[𝓝 0] (fun z => ‖z‖ ^ 3) → (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro hA hB g F hF hF0 hcond
  obtain ⟨hax, heq⟩ := hcond
  have hsign : ∑ I : Finset (Fin 3), ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) = 0 := by
    have h : ∑ I : Finset (Fin 3), (-1 : ℤ) ^ (3 - I.card) = 0 := by decide
    rw [← Int.cast_sum, h, Int.cast_zero]
  set L := Complex.log (F 0) with hL
  have hL' : cexp L = F 0 := Complex.exp_log hF0
  set f : (Fin 3 → Fin g → ℂ) → ℂ := fun x => Complex.log (F x / F 0) with hfdef
  have hfa : AnalyticAt ℂ f 0 :=
    (hF.div analyticAt_const hF0).clog (by simpa [hF0] using Complex.one_mem_slitPlane)
  have hFne : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x ≠ 0 := hF.continuousAt.eventually_ne hF0
  have hFexp : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = cexp (L + f x) := by
    filter_upwards [hFne] with x hx
    rw [Complex.exp_add, hL']
    simp only [hfdef]
    rw [Complex.exp_log (div_ne_zero hx hF0)]
    field_simp
  have hfax : ∀ a, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → f x = 0 := by
    intro a
    filter_upwards [hax a] with x hx h0
    simp only [hfdef, hx h0, div_self hF0, Complex.log_one]
  have hfO : f =O[𝓝 0] fun z => ‖z‖ ^ 3 := isBigO_norm_cube_of_analytic_vanishing_coords hfa hfax
  let M : (Fin g → ℂ) →L[ℂ] (Fin 3 → Fin g → ℂ) := ContinuousLinearMap.pi fun a : Fin 3 =>
    ![ContinuousLinearMap.id ℂ (Fin g → ℂ), ContinuousLinearMap.id ℂ (Fin g → ℂ),
      -ContinuousLinearMap.id ℂ (Fin g → ℂ)] a
  have hM : ∀ s, M s = ![s, s, -s] := by
    intro s
    funext a
    fin_cases a <;> simp [M]
  let S : Finset (Fin 3) → (Fin 3 → Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fun I =>
    ∑ a ∈ I, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Fin g → ℂ) a
  have hS : ∀ I x, S I x = ∑ a ∈ I, x a := by
    intro I x
    simp [S]
  let φ : (Fin g → ℂ) → ℂ := fun s => f (M s)
  have hφa : AnalyticAt ℂ φ 0 := hfa.comp_of_eq (M.analyticAt 0) (map_zero M)
  have hφO : φ =O[𝓝 0] fun z => ‖z‖ ^ 3 := isBigO_norm_cube_comp_clm hfO M
  obtain ⟨k, hka, hkO, hkeq⟩ := hA g (fun s => -φ s) hφa.neg hφO.neg_left
  have hk0 : k 0 = 0 := by
    have : k =O[𝓝 (0 : Fin g → ℂ)] fun y => ‖y - 0‖ ^ 3 := by simpa using hkO
    exact this.eq_zero_of_norm_pow (by norm_num)
  let D : ((Fin g → ℂ) → ℂ) → (Fin 3 → Fin g → ℂ) → ℂ := fun w x =>
    ∑ I : Finset (Fin 3), ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * w (∑ a ∈ I, x a)
  have hDO : ∀ w : (Fin g → ℂ) → ℂ, w =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      D w =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    intro w hw
    have : D w = ∑ I : Finset (Fin 3),
        fun x => ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * w (S I x) := by
      funext x
      simp [D, hS]
    rw [this]
    exact IsBigO.sum fun I _ => (isBigO_norm_cube_comp_clm hw (S I)).const_mul_left _
  let Gf : (Fin 3 → Fin g → ℂ) → ℂ := fun x => f x - D k x
  have hGO : Gf =O[𝓝 0] fun x => ‖x‖ ^ 3 := hfO.sub (hDO k hkO)
  have ev2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) = cexp (L + f ((2 : ℂ) • x)) :=
    eventually_nhds_zero_comp_of_continuous (T := fun x : Fin 3 → Fin g → ℂ => (2 : ℂ) • x)
      (p := fun y => F y = cexp (L + f y)) (by fun_prop) (smul_zero _) hFexp
  have evn : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F (-x) = cexp (L + f (-x)) :=
    eventually_nhds_zero_comp_of_continuous (T := fun x : Fin 3 → Fin g → ℂ => -x)
      (p := fun y => F y = cexp (L + f y)) (by fun_prop) neg_zero hFexp
  have evI : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3),
      F (M (∑ a ∈ I, x a)) = cexp (L + f (M (∑ a ∈ I, x a))) :=
    Filter.eventually_all.2 fun I => eventually_nhds_zero_comp_of_continuous
      (T := fun x : Fin 3 → Fin g → ℂ => M (∑ a ∈ I, x a))
      (p := fun y => F y = cexp (L + f y))
      (M.continuous.comp (continuous_finset_sum _ fun a _ => continuous_apply a)) (by simp) hFexp
  have evk : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3),
      k ((2 : ℂ) • ∑ a ∈ I, x a) - 3 * k (∑ a ∈ I, x a) - k (-∑ a ∈ I, x a) =
        -φ (∑ a ∈ I, x a) :=
    Filter.eventually_all.2 fun I => eventually_nhds_zero_comp_of_continuous
      (T := fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a)
      (p := fun z => k ((2 : ℂ) • z) - 3 * k z - k (-z) = -φ z)
      (continuous_finset_sum _ fun a _ => continuous_apply a) (by simp) hkeq
  have hEt : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ),
      ‖f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x)‖ < 2 * π := by
    have h2x : (fun x : Fin 3 → Fin g → ℂ => f ((2 : ℂ) • x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
      have := isBigO_norm_cube_comp_clm hfO ((2 : ℂ) • ContinuousLinearMap.id ℂ (Fin 3 → Fin g → ℂ))
      simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using this
    have hnx : (fun x : Fin 3 → Fin g → ℂ => f (-x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
      have := isBigO_norm_cube_comp_clm hfO (-ContinuousLinearMap.id ℂ (Fin 3 → Fin g → ℂ))
      simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using this
    have h3 : (fun x : Fin 3 → Fin g → ℂ => 3 * f x) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
      hfO.const_mul_left 3
    have hO : (fun x => f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x)) =O[𝓝 0]
        fun x : Fin 3 → Fin g → ℂ => ‖x‖ ^ 3 :=
      ((h2x.add (hDO φ hφO)).sub h3).sub hnx
    have ht : Tendsto (fun x : Fin 3 → Fin g → ℂ => ‖x‖ ^ 3) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun x : Fin 3 → Fin g → ℂ => ‖x‖ ^ 3 := by fun_prop
      simpa using hc.tendsto 0
    filter_upwards [(hO.trans_tendsto ht).eventually
      (Metric.ball_mem_nhds 0 (by positivity : (0 : ℝ) < 2 * π))] with x hx
    exact mem_ball_zero_iff.1 hx
  have hE : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x) = 0 := by
    filter_upwards [heq, hFexp, ev2, evn, evI, hEt] with x hx hx1 hx2 hx3 hx4 hx5
    have hprod : ∏ I : Finset (Fin 3),
        F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card)) =
          cexp (∑ I : Finset (Fin 3),
            ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * (L + φ (∑ a ∈ I, x a))) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Complex.exp_int_mul, ← hM, hx4 I]
    rw [hprod, hx2, hx3, hx1, ← hL'] at hx
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add] at hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hx
    have hsum : ∑ I : Finset (Fin 3),
        ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * (L + φ (∑ a ∈ I, x a)) = D φ x := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsign, zero_mul, zero_add, D]
    rw [hsum] at hn
    have hEx : f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x) = n * (2 * π * Complex.I) := by
      linear_combination hn
    have hn0 : n = 0 := by
      rw [hEx] at hx5
      have h1 : ‖(n : ℂ) * (2 * π * Complex.I)‖ = |(n : ℝ)| * (2 * π) := by
        simp [abs_of_pos Real.pi_pos]
      rw [h1] at hx5
      have h2 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left (by positivity)).1 hx5
      have h3 : |n| < 1 := by exact_mod_cast h2
      exact Int.abs_lt_one_iff.1 h3
    rw [hEx, hn0]
    simp
  have hGeq : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), Gf ((2 : ℂ) • x) = 3 * Gf x + Gf (-x) := by
    filter_upwards [hE, evk] with x hx hk
    have e1 : ∀ I : Finset (Fin 3), ∑ a ∈ I, ((2 : ℂ) • x) a = (2 : ℂ) • ∑ a ∈ I, x a :=
      fun I => by simp [Finset.smul_sum]
    have e2 : ∀ I : Finset (Fin 3), ∑ a ∈ I, (-x) a = -∑ a ∈ I, x a :=
      fun I => by simp [Finset.sum_neg_distrib]
    have hD : D k ((2 : ℂ) • x) - 3 * D k x - D k (-x) = -D φ x := by
      simp only [D, e1, e2]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun I _ => ?_
      linear_combination ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * hk I
    show f ((2 : ℂ) • x) - D k ((2 : ℂ) • x) = 3 * (f x - D k x) + (f (-x) - D k (-x))
    linear_combination hx - hD
  have hG0 := hB (Fin 3 → Fin g → ℂ) Gf hGO hGeq
  refine ⟨k, hka, hk0, ?_⟩
  filter_upwards [hG0, hFexp] with x hx hx1
  have hprod2 : ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card)) =
      cexp (D k x) := by
    simp only [D]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun I _ => (Complex.exp_int_mul _ _).symm
  rw [hx1, ← hL', hprod2, ← Complex.exp_add]
  have hfx : f x - D k x = 0 := hx
  congr 1
  linear_combination hfx
end _root_.GlobalTheory.LocalCube
end GlobalTheory.LocalCube
