-- Prove2me | solution 1 for NonsmoothQN.LineSearch.theorem_4_7_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T19:59:29.6719+00:00
-- url     : https://prove2.me/submissions/01625f7c-930a-442a-b409-a38b8120d79f

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace NQN5ec

open NonsmoothQN.LineSearch

theorem lsRun_succ (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (n : ℕ) :
    lsRun h c₁ c₂ s (n + 1) = lsStep h c₁ c₂ s (lsRun h c₁ c₂ s n) := by
  simp only [lsRun]
  exact Function.iterate_succ_apply' _ _ _

theorem nextTrial_top (α : ℝ) : nextTrial α ⊤ = 2 * α := by
  simp [nextTrial]

theorem nextTrial_coe (α b : ℝ) : nextTrial α (b : WithTop ℝ) = (α + b) / 2 := by
  simp [nextTrial]

structure Inv (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (σ : LSState) : Prop where
  α_nonneg : 0 ≤ σ.α
  α_good : 0 < σ.α → ArmijoA h c₁ s σ.α ∧ ¬ WolfeW h c₂ s σ.α
  top_t : σ.β = ⊤ → (σ.α = 0 ∧ σ.t = 1) ∨ (0 < σ.α ∧ σ.t = 2 * σ.α)
  fin : ∀ b : ℝ, σ.β = (b : WithTop ℝ) → σ.α < b ∧ ¬ ArmijoA h c₁ s b ∧ σ.t = (σ.α + b) / 2

theorem Inv.lt_t {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hI : Inv h c₁ c₂ s σ) :
    σ.α < σ.t := by
  rcases eq_or_ne σ.β ⊤ with hβ | hβ
  · rcases hI.top_t hβ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; norm_num
    · rw [h2]; linarith
  · obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hβ
    obtain ⟨h1, -, h3⟩ := hI.fin b hb.symm
    rw [h3]; linarith

theorem Inv.init (h : ℝ → ℝ) (c₁ c₂ s : ℝ) : Inv h c₁ c₂ s LSState.init where
  α_nonneg := by simp [LSState.init]
  α_good := by intro h0; simp [LSState.init] at h0
  top_t := fun _ => Or.inl ⟨rfl, rfl⟩
  fin := fun b hb => by simp [LSState.init] at hb

theorem lsStep_nA {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hA : ¬ ArmijoA h c₁ s σ.t) :
    lsStep h c₁ c₂ s σ = ⟨σ.α, (σ.t : WithTop ℝ), nextTrial σ.α (σ.t : WithTop ℝ)⟩ := by
  unfold lsStep; rw [if_pos hA]

theorem lsStep_AnW {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hA : ArmijoA h c₁ s σ.t)
    (hW : ¬ WolfeW h c₂ s σ.t) :
    lsStep h c₁ c₂ s σ = ⟨σ.t, σ.β, nextTrial σ.t σ.β⟩ := by
  unfold lsStep; rw [if_neg (not_not.2 hA), if_pos hW]

theorem lsStep_AW {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hA : ArmijoA h c₁ s σ.t)
    (hW : WolfeW h c₂ s σ.t) : lsStep h c₁ c₂ s σ = σ := by
  unfold lsStep; rw [if_neg (not_not.2 hA), if_neg (not_not.2 hW)]

theorem Inv.step {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hI : Inv h c₁ c₂ s σ) :
    Inv h c₁ c₂ s (lsStep h c₁ c₂ s σ) := by
  have hαt := hI.lt_t
  have hα0 := hI.α_nonneg
  by_cases hA : ArmijoA h c₁ s σ.t
  · by_cases hW : WolfeW h c₂ s σ.t
    · rw [lsStep_AW hA hW]; exact hI
    · rw [lsStep_AnW hA hW]
      refine ⟨show 0 ≤ σ.t by linarith, fun _ => ⟨hA, hW⟩, ?_, ?_⟩
      · intro hβ
        change σ.β = ⊤ at hβ
        right
        exact ⟨show 0 < σ.t by linarith, show nextTrial σ.t σ.β = 2 * σ.t by rw [hβ, nextTrial_top]⟩
      · intro b hb
        change σ.β = b at hb
        obtain ⟨h1, h2, h3⟩ := hI.fin b hb
        exact ⟨show σ.t < b by linarith, h2,
          show nextTrial σ.t σ.β = (σ.t + b) / 2 by rw [hb, nextTrial_coe]⟩
  · rw [lsStep_nA hA]
    refine ⟨hα0, hI.α_good, ?_, ?_⟩
    · intro hβ
      change ((σ.t : ℝ) : WithTop ℝ) = ⊤ at hβ
      exact absurd hβ WithTop.coe_ne_top
    · intro b hb
      change ((σ.t : ℝ) : WithTop ℝ) = b at hb
      have hb' : σ.t = b := WithTop.coe_injective hb
      subst hb'
      exact ⟨hαt, hA, nextTrial_coe _ _⟩

theorem inv_run (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (n : ℕ) : Inv h c₁ c₂ s (lsRun h c₁ c₂ s n) := by
  induction n with
  | zero => exact Inv.init h c₁ c₂ s
  | succ n ih => rw [lsRun_succ]; exact ih.step

theorem t_pos (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (n : ℕ) : 0 < (lsRun h c₁ c₂ s n).t := by
  have hI := inv_run h c₁ c₂ s n
  linarith [hI.lt_t, hI.α_nonneg]

theorem α_le_step {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hI : Inv h c₁ c₂ s σ) :
    σ.α ≤ (lsStep h c₁ c₂ s σ).α := by
  have := hI.lt_t
  by_cases hA : ArmijoA h c₁ s σ.t
  · by_cases hW : WolfeW h c₂ s σ.t
    · rw [lsStep_AW hA hW]
    · rw [lsStep_AnW hA hW]; exact this.le
  · rw [lsStep_nA hA]

theorem step_fin {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState} (hI : Inv h c₁ c₂ s σ)
    (hnt : ¬ (ArmijoA h c₁ s σ.t ∧ WolfeW h c₂ s σ.t)) (b : ℝ) (hb : σ.β = (b : WithTop ℝ)) :
    ∃ b' : ℝ, (lsStep h c₁ c₂ s σ).β = (b' : WithTop ℝ) ∧ b' ≤ b ∧
      b' - (lsStep h c₁ c₂ s σ).α = (b - σ.α) / 2 := by
  obtain ⟨h1, -, h3⟩ := hI.fin b hb
  by_cases hA : ArmijoA h c₁ s σ.t
  · by_cases hW : WolfeW h c₂ s σ.t
    · exact absurd ⟨hA, hW⟩ hnt
    · rw [lsStep_AnW hA hW]
      exact ⟨b, hb, le_rfl, show b - σ.t = (b - σ.α) / 2 by rw [h3]; ring⟩
  · rw [lsStep_nA hA]
    exact ⟨σ.t, rfl, by rw [h3]; linarith, show σ.t - σ.α = (b - σ.α) / 2 by rw [h3]; ring⟩

theorem step_top {h : ℝ → ℝ} {c₁ c₂ s : ℝ} {σ : LSState}
    (hnt : ¬ (ArmijoA h c₁ s σ.t ∧ WolfeW h c₂ s σ.t))
    (htop : (lsStep h c₁ c₂ s σ).β = ⊤) :
    ArmijoA h c₁ s σ.t ∧ (lsStep h c₁ c₂ s σ).t = 2 * σ.t := by
  by_cases hA : ArmijoA h c₁ s σ.t
  · by_cases hW : WolfeW h c₂ s σ.t
    · exact absurd ⟨hA, hW⟩ hnt
    · rw [lsStep_AnW hA hW] at htop ⊢
      change σ.β = ⊤ at htop
      exact ⟨hA, show nextTrial σ.t σ.β = 2 * σ.t by rw [htop, nextTrial_top]⟩
  · rw [lsStep_nA hA] at htop
    change ((σ.t : ℝ) : WithTop ℝ) = ⊤ at htop
    exact absurd htop WithTop.coe_ne_top

theorem first_cross {φ : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q) (hc : ContinuousOn φ (Icc p q))
    (hp : φ p < 0) (hq : 0 ≤ φ q) :
    ∃ r, p < r ∧ r ≤ q ∧ 0 ≤ φ r ∧ ∀ t, p ≤ t → t < r → φ t < 0 := by
  let S := Icc p q ∩ φ ⁻¹' Ici 0
  have hS : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hne : S.Nonempty := ⟨q, ⟨hpq, le_rfl⟩, hq⟩
  have hbdd : BddBelow S := ⟨p, fun x hx => hx.1.1⟩
  have hmem : sInf S ∈ S := hS.csInf_mem hne hbdd
  have hr0 : 0 ≤ φ (sInf S) := hmem.2
  have hpr : p ≤ sInf S := hmem.1.1
  have hrq : sInf S ≤ q := hmem.1.2
  refine ⟨sInf S, ?_, hrq, hr0, ?_⟩
  · rcases hpr.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hr0; linarith
  · intro t ht1 ht2
    by_contra hcon
    push Not at hcon
    have htS : t ∈ S := ⟨⟨ht1, (ht2.trans_le hrq).le⟩, hcon⟩
    exact absurd (csInf_le hbdd htS) (not_le.2 ht2)

theorem key {h : ℝ → ℝ} {p r c : ℝ} (hpr : p < r) (hac : AbsolutelyContinuousOnInterval h p r)
    (Q : ℝ → Prop) (hQ : ∀ t ∈ Ioo p r, Q t) (hgt : c * (r - p) < h r - h p) :
    volume {t | t ∈ Ioo p r ∧ Q t ∧ DifferentiableAt ℝ h t ∧ c < deriv h t} ≠ 0 := by
  intro h0
  have hnot := measure_eq_zero_iff_ae_notMem.1 h0
  have hdiff := hac.ae_differentiableAt
  have hpne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ p := by
    simpa using measure_eq_zero_iff_ae_notMem.1 (show volume ({p} : Set ℝ) = 0 from measure_singleton p)
  have hrne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ r := by
    simpa using measure_eq_zero_iff_ae_notMem.1 (show volume ({r} : Set ℝ) = 0 from measure_singleton r)
  have hle_ae : (fun t => deriv h t) ≤ᵐ[volume.restrict (Icc p r)] (fun _ => c) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hnot, hdiff, hpne, hrne] with t h1 h2 h3 h4 ht
    have htI : t ∈ Ioo p r := ⟨lt_of_le_of_ne ht.1 (Ne.symm h3), lt_of_le_of_ne ht.2 h4⟩
    have hd : DifferentiableAt ℝ h t := h2 (by rw [uIcc_of_le hpr.le]; exact ht)
    by_contra hlt
    push Not at hlt
    exact h1 ⟨htI, hQ t htI, hd, hlt⟩
  have hint := intervalIntegral.integral_mono_ae_restrict hpr.le hac.intervalIntegrable_deriv
    intervalIntegrable_const hle_ae
  rw [hac.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hint
  linarith [mul_comm c (r - p)]

theorem exists_deriv_gt {h : ℝ → ℝ} {p r c : ℝ} (hpr : p < r)
    (hac : AbsolutelyContinuousOnInterval h p r) (hgt : c * (r - p) < h r - h p) :
    ∃ ξ, p < ξ ∧ ξ < r ∧ DifferentiableAt ℝ h ξ ∧ c < deriv h ξ := by
  have := key hpr hac (fun _ => True) (fun _ _ => trivial) hgt
  obtain ⟨ξ, hξ1, -, hξ3, hξ4⟩ := nonempty_of_measure_ne_zero this
  exact ⟨ξ, hξ1.1, hξ1.2, hξ3, hξ4⟩

theorem meas_AW {h : ℝ → ℝ} {c₁ c₂ s p q : ℝ} (hA41 : Assumption41 h s) (hc₁₂ : c₁ < c₂)
    (hp : 0 < p) (hpq : p < q) (hAp : ArmijoA h c₁ s p) (hAq : ¬ ArmijoA h c₁ s q) :
    volume {t | t ∈ Icc p q ∧ IsAWStep h c₁ c₂ s t} ≠ 0 := by
  have hs := hA41.neg
  have hac : AbsolutelyContinuousOnInterval h p q := hA41.absCont p q hp.le hpq.le
  have hcont : ContinuousOn (fun t => h t - c₁ * s * t) (Icc p q) := by
    have := hac.continuousOn
    rw [uIcc_of_le hpq.le] at this
    exact this.sub (continuous_const.mul continuous_id).continuousOn
  unfold ArmijoA at hAp hAq
  push Not at hAq
  obtain ⟨r, hpr, hrq, hr0, hlt⟩ := first_cross (φ := fun t => h t - c₁ * s * t) hpq.le hcont
    (show h p - c₁ * s * p < 0 by linarith) (show 0 ≤ h q - c₁ * s * q by linarith)
  have hr0' : 0 ≤ h r - c₁ * s * r := hr0
  have hgt : c₂ * s * (r - p) < h r - h p := by
    have := mul_pos (mul_pos (sub_pos.2 hc₁₂) (neg_pos.2 hs)) (sub_pos.2 hpr)
    nlinarith
  have hK := key hpr (hA41.absCont p r hp.le hpr.le) (fun t => 0 < t ∧ ArmijoA h c₁ s t)
    (fun t ht => ⟨hp.trans ht.1, by
      have h' : h t - c₁ * s * t < 0 := hlt t ht.1.le ht.2
      unfold ArmijoA; linarith⟩) hgt
  intro h0
  apply hK
  apply measure_mono_null _ h0
  intro t ht
  obtain ⟨ht1, ⟨ht2, ht3⟩, ht4, ht5⟩ := ht
  exact ⟨⟨ht1.1.le, (ht1.2.trans_le hrq).le⟩, ht2, ht3, ht4, ht5⟩

theorem core (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (hA41 : Assumption41 h s) (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) (hnt : ¬ Terminates h c₁ c₂ s) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, ∃ tt : ℝ, ∃ ξ : ℕ → ℝ,
      (∀ n ≥ N, (lsRun h c₁ c₂ s n).β = (b n : WithTop ℝ) ∧ 0 < (lsRun h c₁ c₂ s n).α ∧
        (lsRun h c₁ c₂ s n).α < b n ∧ ArmijoA h c₁ s (lsRun h c₁ c₂ s n).α ∧
        ¬ WolfeW h c₂ s (lsRun h c₁ c₂ s n).α ∧ ¬ ArmijoA h c₁ s (b n) ∧
        (lsRun h c₁ c₂ s n).α ≤ (lsRun h c₁ c₂ s (n + 1)).α ∧ b (n + 1) ≤ b n ∧
        b (n + 1) - (lsRun h c₁ c₂ s (n + 1)).α = (b n - (lsRun h c₁ c₂ s n).α) / 2 ∧
        (lsRun h c₁ c₂ s n).α < tt) ∧
      0 < tt ∧ Tendsto (fun n => (lsRun h c₁ c₂ s n).α) atTop (𝓝 tt) ∧
      Tendsto b atTop (𝓝 tt) ∧ h tt = c₁ * s * tt ∧
      Tendsto ξ atTop (𝓝[<] tt) ∧
      (∀ n, ξ n < tt ∧ DifferentiableAt ℝ h (ξ n) ∧ c₁ * s < deriv h (ξ n)) := by
  have hs := hA41.neg
  have hI : ∀ n, Inv h c₁ c₂ s (lsRun h c₁ c₂ s n) := inv_run h c₁ c₂ s
  have hnt' : ∀ n, ¬ (ArmijoA h c₁ s (lsRun h c₁ c₂ s n).t ∧
      WolfeW h c₂ s (lsRun h c₁ c₂ s n).t) := fun n hn => hnt ⟨n, hn⟩
  have hαmono : Monotone (fun n => (lsRun h c₁ c₂ s n).α) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    show (lsRun h c₁ c₂ s n).α ≤ (lsRun h c₁ c₂ s (n + 1)).α
    rw [lsRun_succ]; exact α_le_step (hI n)
  -- the doubling phase ends
  have hN1 : ∃ N, (lsRun h c₁ c₂ s N).β ≠ ⊤ := by
    by_contra hall
    push Not at hall
    have ht : ∀ n, (lsRun h c₁ c₂ s n).t = 2 ^ n := by
      intro n
      induction n with
      | zero => show LSState.init.t = (2 : ℝ) ^ 0; simp [LSState.init]
      | succ n ih =>
        have := step_top (hnt' n) (by rw [← lsRun_succ]; exact hall (n + 1))
        rw [lsRun_succ, this.2, ih]; ring
    have hA : ∀ n, ArmijoA h c₁ s (2 ^ n) := fun n => by
      have := (step_top (hnt' n) (by rw [← lsRun_succ]; exact hall (n + 1))).1
      rwa [ht n] at this
    obtain ⟨m, hm⟩ := hA41.bddBelow
    have hk : 0 < -(c₁ * s) := by have := mul_pos hc₁ (neg_pos.2 hs); linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (-m / -(c₁ * s)) (by norm_num : (1 : ℝ) < 2)
    have h1 : m ≤ h (2 ^ n) := hm ⟨2 ^ n, Set.mem_Ici.2 (by positivity), rfl⟩
    have h2 := hA n
    unfold ArmijoA at h2
    rw [div_lt_iff₀ hk] at hn
    nlinarith
  obtain ⟨N₁, hN₁⟩ := hN1
  have hfinβ : ∀ n ≥ N₁, (lsRun h c₁ c₂ s n).β ≠ ⊤ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hN₁
    | succ n hn ih =>
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ih
      obtain ⟨b', hb', -⟩ := step_fin (hI n) (hnt' n) b hb.symm
      rw [lsRun_succ, hb']; exact WithTop.coe_ne_top
  have hex : ∀ n, ∃ x : ℝ, n ≥ N₁ → (lsRun h c₁ c₂ s n).β = (x : WithTop ℝ) := by
    intro n
    by_cases hn : n ≥ N₁
    · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 (hfinβ n hn)
      exact ⟨x, fun _ => hx.symm⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose bf hbf using hex
  have hstep : ∀ n ≥ N₁, bf (n + 1) ≤ bf n ∧
      bf (n + 1) - (lsRun h c₁ c₂ s (n + 1)).α = (bf n - (lsRun h c₁ c₂ s n).α) / 2 := by
    intro n hn
    obtain ⟨b', hb', h1, h2⟩ := step_fin (hI n) (hnt' n) (bf n) (hbf n hn)
    rw [← lsRun_succ] at hb' h2
    have e : b' = bf (n + 1) := by
      have := hbf (n + 1) (by omega)
      rw [hb'] at this
      exact WithTop.coe_injective this
    subst e
    exact ⟨h1, h2⟩
  have hInvb : ∀ n ≥ N₁, (lsRun h c₁ c₂ s n).α < bf n ∧ ¬ ArmijoA h c₁ s (bf n) := by
    intro n hn
    have H := (hI n).fin (bf n) (hbf n hn)
    exact ⟨H.1, H.2.1⟩
  have hlen : ∀ m : ℕ, bf (m + N₁) - (lsRun h c₁ c₂ s (m + N₁)).α =
      (bf N₁ - (lsRun h c₁ c₂ s N₁).α) / 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show m + 1 + N₁ = (m + N₁) + 1 by omega, (hstep (m + N₁) (by omega)).2, ih, pow_succ]
      ring
  have hL0 : Tendsto (fun m : ℕ => (bf N₁ - (lsRun h c₁ c₂ s N₁).α) / 2 ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (bf N₁ - (lsRun h c₁ c₂ s N₁).α)
    rw [mul_zero] at this
    refine this.congr (fun m => ?_)
    rw [one_div_pow, mul_one_div]
  -- the lower bound becomes positive
  have hN2 : ∃ N ≥ N₁, 0 < (lsRun h c₁ c₂ s N).α := by
    by_contra hall
    push Not at hall
    have hαN : (lsRun h c₁ c₂ s N₁).α = 0 := le_antisymm (hall N₁ le_rfl) (hI _).α_nonneg
    have hα0 : ∀ m : ℕ, (lsRun h c₁ c₂ s (m + N₁)).α = 0 := fun m =>
      le_antisymm (hall _ (by omega)) (hI _).α_nonneg
    have hb : ∀ m : ℕ, bf (m + N₁) = bf N₁ / 2 ^ m := fun m => by
      have := hlen m
      rwa [hα0 m, hαN, sub_zero, sub_zero] at this
    have hbpos : ∀ m : ℕ, 0 < bf (m + N₁) := fun m => by
      have := (hInvb (m + N₁) (by omega)).1
      rwa [hα0 m] at this
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ((h t / t : ℝ) : EReal) < ((c₁ * s : ℝ) : EReal) := by
      have hlt : s < c₁ * s := by
        have := mul_pos (sub_pos.2 (hc₁₂.trans hc₂)) (neg_pos.2 hs)
        nlinarith
      exact eventually_lt_of_limsup_lt (by rw [hA41.limsup_eq]; exact EReal.coe_lt_coe_iff.2 hlt)
    have hL0' := hL0
    rw [hαN, sub_zero] at hL0'
    have htend : Tendsto (fun m : ℕ => bf (m + N₁)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hL0'.congr (fun m => (hb m).symm), Eventually.of_forall hbpos⟩
    obtain ⟨m, hm⟩ := (htend.eventually hev).exists
    have hm' := EReal.coe_lt_coe_iff.1 hm
    have hnA := (hInvb (m + N₁) (by omega)).2
    unfold ArmijoA at hnA
    push Not at hnA
    rw [div_lt_iff₀ (hbpos m)] at hm'
    linarith
  obtain ⟨N, hNN₁, hαNpos⟩ := hN2
  have hαpos : ∀ n ≥ N, 0 < (lsRun h c₁ c₂ s n).α := fun n hn => hαNpos.trans_le (hαmono hn)
  have hbleN : ∀ n ≥ N₁, bf n ≤ bf N₁ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hstep n hn).1.trans ih
  have hbdd : BddAbove (Set.range (fun n => (lsRun h c₁ c₂ s n).α)) := by
    refine ⟨bf N₁, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc (lsRun h c₁ c₂ s n).α ≤ (lsRun h c₁ c₂ s (n + N₁)).α := hαmono (by omega)
      _ ≤ bf (n + N₁) := (hInvb _ (by omega)).1.le
      _ ≤ bf N₁ := hbleN _ (by omega)
  obtain ⟨tt, htt_def⟩ : ∃ tt : ℝ, tt = ⨆ n, (lsRun h c₁ c₂ s n).α := ⟨_, rfl⟩
  have hαt : Tendsto (fun n => (lsRun h c₁ c₂ s n).α) atTop (𝓝 tt) := by
    rw [htt_def]; exact tendsto_atTop_ciSup hαmono hbdd
  have hαle : ∀ n, (lsRun h c₁ c₂ s n).α ≤ tt := fun n => by rw [htt_def]; exact le_ciSup hbdd n
  have httpos : 0 < tt := hαNpos.trans_le (hαle N)
  have hbt : Tendsto bf atTop (𝓝 tt) := by
    refine (tendsto_add_atTop_iff_nat N₁).1 ?_
    have h1 : Tendsto (fun m : ℕ => (lsRun h c₁ c₂ s (m + N₁)).α) atTop (𝓝 tt) :=
      (tendsto_add_atTop_iff_nat N₁).2 hαt
    have h2 := h1.add hL0
    rw [add_zero] at h2
    refine h2.congr (fun m => ?_)
    have := hlen m
    linarith
  have hcAt : ContinuousAt h tt := by
    have hc := (hA41.absCont 0 (tt + 1) le_rfl (by linarith)).continuousOn
    rw [uIcc_of_le (by linarith)] at hc
    exact hc.continuousAt (Icc_mem_nhds httpos (by linarith))
  have hφα : ∀ n ≥ N, h (lsRun h c₁ c₂ s n).α < c₁ * s * (lsRun h c₁ c₂ s n).α :=
    fun n hn => ((hI n).α_good (hαpos n hn)).1
  have hhtt : h tt = c₁ * s * tt := by
    have hlim1 : Tendsto (fun n => h (lsRun h c₁ c₂ s n).α - c₁ * s * (lsRun h c₁ c₂ s n).α)
        atTop (𝓝 (h tt - c₁ * s * tt)) :=
      (hcAt.tendsto.comp hαt).sub (tendsto_const_nhds.mul hαt)
    have hlim2 : Tendsto (fun n => h (bf n) - c₁ * s * bf n) atTop (𝓝 (h tt - c₁ * s * tt)) :=
      (hcAt.tendsto.comp hbt).sub (tendsto_const_nhds.mul hbt)
    have e1 : h tt - c₁ * s * tt ≤ 0 :=
      le_of_tendsto hlim1 (eventually_atTop.2 ⟨N, fun n hn => by linarith [hφα n hn]⟩)
    have e2 : 0 ≤ h tt - c₁ * s * tt :=
      ge_of_tendsto hlim2 (eventually_atTop.2 ⟨N₁, fun n hn => by
        have := (hInvb n hn).2
        unfold ArmijoA at this
        push Not at this
        linarith⟩)
    linarith
  have hαlt : ∀ n ≥ N, (lsRun h c₁ c₂ s n).α < tt := by
    intro n hn
    refine lt_of_le_of_ne (hαle n) (fun heq => ?_)
    have := hφα n hn
    rw [heq] at this
    linarith
  have hξex : ∀ m : ℕ, ∃ ξ, (lsRun h c₁ c₂ s (m + N)).α < ξ ∧ ξ < tt ∧
      DifferentiableAt ℝ h ξ ∧ c₁ * s < deriv h ξ := by
    intro m
    have hlt := hαlt (m + N) (by omega)
    have hA := hφα (m + N) (by omega)
    exact exists_deriv_gt hlt (hA41.absCont _ _ (hI _).α_nonneg hlt.le) (by linarith)
  choose ξ hξ using hξex
  have hξt : Tendsto ξ atTop (𝓝[<] tt) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun m => (hξ m).2.1)⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le ((tendsto_add_atTop_iff_nat N).2 hαt)
      tendsto_const_nhds (fun m => (hξ m).1.le) (fun m => (hξ m).2.1.le)
  refine ⟨N, bf, tt, ξ, fun n hn => ?_, httpos, hαt, hbt, hhtt, hξt,
    fun m => ⟨(hξ m).2.1, (hξ m).2.2⟩⟩
  have hn1 : n ≥ N₁ := le_trans hNN₁ hn
  have hg := (hI n).α_good (hαpos n hn)
  exact ⟨hbf n hn1, hαpos n hn, (hInvb n hn1).1, hg.1, hg.2, (hInvb n hn1).2,
    hαmono (Nat.le_succ n), (hstep n hn1).1, (hstep n hn1).2, hαlt n hn⟩

end NQN5ec

open Filter Topology MeasureTheory Set NonsmoothQN.LineSearch in
theorem solution (h : ℝ → ℝ) (c₁ c₂ s : ℝ)
    (hA41 : Assumption41 h s) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    (∀ n : ℕ, ArmijoA h c₁ s (lsRun h c₁ c₂ s n).t → WolfeW h c₂ s (lsRun h c₁ c₂ s n).t →
        IsAWStep h c₁ c₂ s (lsRun h c₁ c₂ s n).t) ∧
    (Cond48 h → Terminates h c₁ c₂ s) ∧
    (¬ Terminates h c₁ c₂ s →
      ∃ N : ℕ, ∃ b : ℕ → ℝ,
        (∀ n ≥ N,
          (lsRun h c₁ c₂ s n).β = (b n : WithTop ℝ) ∧
          0 < (lsRun h c₁ c₂ s n).α ∧
          Set.Icc (lsRun h c₁ c₂ s (n + 1)).α (b (n + 1)) ⊆
            Set.Icc (lsRun h c₁ c₂ s n).α (b n) ∧
          b (n + 1) - (lsRun h c₁ c₂ s (n + 1)).α = (b n - (lsRun h c₁ c₂ s n).α) / 2 ∧
          volume {t | t ∈ Set.Icc (lsRun h c₁ c₂ s n).α (b n) ∧ IsAWStep h c₁ c₂ s t} ≠ 0) ∧
        ∃ tt : ℝ, 0 < tt ∧
          Tendsto (fun n => (lsRun h c₁ c₂ s n).α) atTop (𝓝 tt) ∧
          Tendsto b atTop (𝓝 tt) ∧
          h tt = c₁ * s * tt ∧
          ((c₂ * s : ℝ) : EReal) ≤
            Filter.limsup (fun t => ((deriv h t : ℝ) : EReal))
              (𝓝[Set.Iio tt ∩ {t | DifferentiableAt ℝ h t}] tt)) := by
  have hs := hA41.neg
  have hcs : c₂ * s < c₁ * s := by
    have := mul_pos (sub_pos.2 hc₁₂) (neg_pos.2 hs)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro n hA hW
    exact ⟨NQN5ec.t_pos h c₁ c₂ s n, hA, hW⟩
  · intro hC
    by_contra hnt
    obtain ⟨N, b, tt, ξ, hN, htt, hαt, -, -, hξt, hξ⟩ :=
      NQN5ec.core h c₁ c₂ s hA41 hc₁ hc₁₂ hc₂ hnt
    obtain ⟨hdiffev, L, hL⟩ := hC tt htt
    have hL1 : ((c₁ * s : ℝ) : EReal) ≤ L :=
      ge_of_tendsto' (hL.comp hξt) (fun n => EReal.coe_le_coe_iff.2 (hξ n).2.2.le)
    have hαw : Tendsto (fun n => (lsRun h c₁ c₂ s n).α) atTop (𝓝[<] tt) :=
      tendsto_nhdsWithin_iff.2
        ⟨hαt, eventually_atTop.2 ⟨N, fun n hn => (hN n hn).2.2.2.2.2.2.2.2.2⟩⟩
    have hL2 : L ≤ ((c₂ * s : ℝ) : EReal) := by
      refine le_of_tendsto (hL.comp hαw) ?_
      filter_upwards [hαw.eventually hdiffev, eventually_ge_atTop N] with n hd hn
      have hnw := (hN n hn).2.2.2.2.1
      refine EReal.coe_le_coe_iff.2 ?_
      by_contra hlt
      push Not at hlt
      exact hnw ⟨hd, hlt⟩
    have := EReal.coe_le_coe_iff.1 (hL1.trans hL2)
    linarith
  · intro hnt
    obtain ⟨N, b, tt, ξ, hN, htt, hαt, hbt, hhtt, hξt, hξ⟩ :=
      NQN5ec.core h c₁ c₂ s hA41 hc₁ hc₁₂ hc₂ hnt
    refine ⟨N, b, fun n hn => ?_, tt, htt, hαt, hbt, hhtt, ?_⟩
    · obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, -⟩ := hN n hn
      exact ⟨h1, h2, Icc_subset_Icc h7 h8, h9, NQN5ec.meas_AW hA41 hc₁₂ h2 h3 h4 h6⟩
    · apply le_limsup_of_frequently_le'
      have hξS : Tendsto ξ atTop (𝓝[Iio tt ∩ {t | DifferentiableAt ℝ h t}] tt) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_nhds_of_tendsto_nhdsWithin hξt,
          Eventually.of_forall (fun n => ⟨(hξ n).1, (hξ n).2.1⟩)⟩
      refine hξS.frequently (Frequently.of_forall (fun n => ?_))
      exact EReal.coe_le_coe_iff.2 (by linarith [(hξ n).2.2])
