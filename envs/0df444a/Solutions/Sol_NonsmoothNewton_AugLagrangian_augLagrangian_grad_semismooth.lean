-- Prove2me | solution 1 for NonsmoothNewton.AugLagrangian.augLagrangian_grad_semismooth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-29T23:52:37.248668+00:00
-- url     : https://prove2.me/submissions/2b68e877-2d5f-4b40-b31b-5c51e42b2761

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

set_option autoImplicit false
open Filter Topology

namespace P2Mcc48

noncomputable def dd (σ a : ℝ) : ℝ := if 0 < σ then a else if σ < 0 then 0 else max a 0

lemma line_quot {W X : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : W → X} {x : W} (hf : DifferentiableAt ℝ f x) (v : W) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (f (x + τ • v) - f x)) (𝓝[>] 0) (𝓝 (fderiv ℝ f x v)) := by
  have h1 : HasDerivAt (fun τ : ℝ => x + τ • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have h2 : HasDerivAt (fun τ : ℝ => f (x + τ • v)) (fderiv ℝ f x v) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • v) := by simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt (0:ℝ) h1
  simpa using h2.tendsto_slope_zero_right

/-- The filter of parameters `(t, g, h')`, `t → 0+`, `g → h`, `h' → h`. -/
abbrev FF {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (h : W) : Filter (ℝ × W × W) :=
  𝓝[>] (0:ℝ) ×ˢ (𝓝 h ×ˢ 𝓝 h)

lemma FF_tendsto {W Y : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace Y]
    (h : W) {g : ℝ × W × W → Y} (hg : Continuous g) :
    Tendsto g (FF h) (𝓝 (g (0, h, h))) := by
  have hF : Tendsto (id : ℝ × W × W → ℝ × W × W) (FF h) (𝓝 (0, h, h)) := by
    rw [nhds_prod_eq, nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  exact (hg.tendsto (0, h, h)).comp hF

lemma FF_pos {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (h : W) :
    ∀ᶠ p in FF h, 0 < p.1 := by
  have : Tendsto (Prod.fst : ℝ × W × W → ℝ) (FF h) (𝓝[>] 0) := Filter.tendsto_fst
  exact this.eventually (eventually_mem_nhdsWithin)

lemma FF_pt {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (h z0 : W) :
    Tendsto (fun p : ℝ × W × W => z0 + p.1 • p.2.1) (FF h) (𝓝 z0) := by
  have := FF_tendsto h (g := fun p : ℝ × W × W => z0 + p.1 • p.2.1)
    (continuous_const.add (continuous_fst.smul (continuous_fst.comp continuous_snd)))
  simpa using this

lemma ray_pos {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : W → ℝ}
    (hs : ContDiff ℝ 1 s) (z0 h : W)
    (hc : 0 < s z0 ∨ (s z0 = 0 ∧ 0 < fderiv ℝ s z0 h)) :
    ∀ᶠ p in FF h, 0 < s (z0 + p.1 • p.2.1) := by
  rcases hc with hc | ⟨h0, ha⟩
  · have : ∀ᶠ z in 𝓝 z0, 0 < s z :=
      hs.continuous.continuousAt.eventually (lt_mem_nhds hc)
    exact (FF_pt h z0).eventually this
  · set D := fderiv ℝ s z0 with hD
    set a := D h with ha_def
    have hlo := (hs.differentiable one_ne_zero z0).hasFDerivAt.isLittleO
    have hcpos : 0 < a / (4 * (‖h‖ + 1)) := by positivity
    have hev := hlo.def hcpos
    have h1 := (FF_pt h z0).eventually hev
    have h2 : ∀ᶠ p in FF h, a / 2 < D p.2.1 := by
      have := FF_tendsto h (g := fun p : ℝ × W × W => D p.2.1)
        (D.continuous.comp (continuous_fst.comp continuous_snd))
      have h2d : a / 2 < D h := by have := ha_def; linarith
      exact this.eventually (lt_mem_nhds h2d)
    have h3 : ∀ᶠ p in FF h, ‖p.2.1‖ < ‖h‖ + 1 := by
      have := FF_tendsto h (g := fun p : ℝ × W × W => ‖p.2.1‖)
        (continuous_norm.comp (continuous_fst.comp continuous_snd))
      exact this.eventually (gt_mem_nhds (by simp))
    filter_upwards [h1, h2, h3, FF_pos h] with p hp1 hp2 hp3 hp4
    obtain ⟨t, g, h'⟩ := p
    simp only at hp1 hp2 hp3 hp4 ⊢
    rw [h0] at hp1
    have e1 : z0 + t • g - z0 = t • g := by abel
    rw [e1] at hp1
    rw [Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_pos hp4] at hp1
    rw [map_smul, smul_eq_mul] at hp1
    have hb := neg_abs_le (s (z0 + t • g) - 0 - t * D g)
    have hb2 : -(a / (4 * (‖h‖ + 1)) * (t * ‖g‖)) ≤ s (z0 + t • g) - 0 - t * D g := by
      have := neg_le_of_abs_le hp1
      linarith
    have hkey : a / (4 * (‖h‖ + 1)) * (t * ‖g‖) ≤ t * (a / 4) := by
      have hpos : 0 < ‖h‖ + 1 := by positivity
      have : a / (4 * (‖h‖ + 1)) * (‖h‖ + 1) = a / 4 := by field_simp
      calc a / (4 * (‖h‖ + 1)) * (t * ‖g‖) = t * (a / (4 * (‖h‖ + 1)) * ‖g‖) := by ring
        _ ≤ t * (a / (4 * (‖h‖ + 1)) * (‖h‖ + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hp4.le
          exact mul_le_mul_of_nonneg_left hp3.le hcpos.le
        _ = t * (a / 4) := by rw [this]
    have : t * (a / 2) < t * D g := mul_lt_mul_of_pos_left hp2 hp4
    nlinarith

lemma ray_neg {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : W → ℝ}
    (hs : ContDiff ℝ 1 s) (z0 h : W)
    (hc : s z0 < 0 ∨ (s z0 = 0 ∧ fderiv ℝ s z0 h < 0)) :
    ∀ᶠ p in FF h, s (z0 + p.1 • p.2.1) < 0 := by
  have hs' : ContDiff ℝ 1 (fun z => -s z) := hs.neg
  have hc' : 0 < (fun z => -s z) z0 ∨
      ((fun z => -s z) z0 = 0 ∧ 0 < fderiv ℝ (fun z => -s z) z0 h) := by
    rcases hc with hc | ⟨h0, ha⟩
    · left; simpa using hc
    · right; refine ⟨by simpa using h0, ?_⟩
      have hfd : fderiv ℝ (fun z => -s z) z0 = -fderiv ℝ s z0 :=
        (hs.differentiable one_ne_zero z0).hasFDerivAt.neg.fderiv
      rw [hfd]; simpa using ha
  filter_upwards [ray_pos hs' z0 h hc'] with p hp
  simpa using hp

lemma single_step {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : W → ℝ}
    (hs : ContDiff ℝ 1 s) (w' h' : W) (a d η : ℝ) (hη : 0 < η)
    (hclose : |fderiv ℝ s w' h' - a| < η)
    (hcase : (0 < s w' ∧ d = a) ∨ (s w' < 0 ∧ d = 0) ∨ (a = 0 ∧ d = 0)) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),
      |τ⁻¹ * (max (s (w' + τ • h')) 0 - max (s w') 0) - d| ≤ η := by
  have hq := line_quot (hs.differentiable one_ne_zero w') h'
  have hq' : ∀ᶠ τ in 𝓝[>] (0:ℝ), |τ⁻¹ * (s (w' + τ • h') - s w') - fderiv ℝ s w' h'|
      < η - |fderiv ℝ s w' h' - a| := by
    have := hq.eventually (Metric.ball_mem_nhds (fderiv ℝ s w' h') (by linarith : 0 < η - |fderiv ℝ s w' h' - a|))
    filter_upwards [this] with τ hτ
    simpa [Real.dist_eq, smul_eq_mul] using hτ
  have hcont : Tendsto (fun τ : ℝ => s (w' + τ • h')) (𝓝[>] (0:ℝ)) (𝓝 (s w')) := by
    have : Continuous (fun τ : ℝ => s (w' + τ • h')) :=
      hs.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hτpos : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := eventually_mem_nhdsWithin
  rcases hcase with ⟨hp, hd⟩ | ⟨hn, hd⟩ | ⟨ha, hd⟩
  · have hpos : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < s (w' + τ • h') :=
      hcont.eventually (lt_mem_nhds hp)
    filter_upwards [hq', hpos] with τ h1 h2
    rw [max_eq_left h2.le, max_eq_left hp.le, hd]
    have := abs_sub_abs_le_abs_sub (τ⁻¹ * (s (w' + τ • h') - s w') - fderiv ℝ s w' h')
      (a - fderiv ℝ s w' h')
    have h3 : |τ⁻¹ * (s (w' + τ • h') - s w') - a| ≤
        |τ⁻¹ * (s (w' + τ • h') - s w') - fderiv ℝ s w' h'| + |fderiv ℝ s w' h' - a| := by
      have := abs_add_le (τ⁻¹ * (s (w' + τ • h') - s w') - fderiv ℝ s w' h')
        (fderiv ℝ s w' h' - a)
      simpa using this
    linarith
  · have hneg : ∀ᶠ τ in 𝓝[>] (0:ℝ), s (w' + τ • h') < 0 :=
      hcont.eventually (gt_mem_nhds hn)
    filter_upwards [hneg] with τ h2
    rw [max_eq_right h2.le, max_eq_right hn.le, hd]
    simp [hη.le]
  · subst ha
    subst hd
    filter_upwards [hq', hτpos] with τ h1 h2
    have hb : |max (s (w' + τ • h')) 0 - max (s w') 0| ≤ |s (w' + τ • h') - s w'| :=
      abs_max_sub_max_le_abs _ _ _
    have habs : |τ⁻¹ * (s (w' + τ • h') - s w')| = τ⁻¹ * |s (w' + τ • h') - s w'| := by
      rw [abs_mul, abs_inv, abs_of_pos h2]
    have h3 : |τ⁻¹ * (s (w' + τ • h') - s w')| < η := by
      have e : τ⁻¹ * (s (w' + τ • h') - s w') =
          (τ⁻¹ * (s (w' + τ • h') - s w') - fderiv ℝ s w' h') + fderiv ℝ s w' h' := by ring
      have h5 := abs_add_le (τ⁻¹ * (s (w' + τ • h') - s w') - fderiv ℝ s w' h')
        (fderiv ℝ s w' h')
      rw [← e] at h5
      have h6 : |fderiv ℝ s w' h' - 0| = |fderiv ℝ s w' h'| := by rw [sub_zero]
      rw [h6] at h1
      linarith
    have h7 : τ⁻¹ * |max (s (w' + τ • h')) 0 - max (s w') 0| ≤
        τ⁻¹ * |s (w' + τ • h') - s w'| :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr h2.le)
    have h8 : |τ⁻¹ * (max (s (w' + τ • h')) 0 - max (s w') 0) - 0| =
        τ⁻¹ * |max (s (w' + τ • h')) 0 - max (s w') 0| := by
      rw [sub_zero, abs_mul, abs_inv, abs_of_pos h2]
    rw [h8]
    linarith


lemma lemA {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : W → ℝ}
    (hs : ContDiff ℝ 1 s) (z0 h : W) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ p in FF h, ∀ᶠ τ in 𝓝[>] (0:ℝ),
      |τ⁻¹ * (max (s (z0 + p.1 • p.2.1 + τ • p.2.2)) 0 - max (s (z0 + p.1 • p.2.1)) 0)
        - dd (s z0) (fderiv ℝ s z0 h)| ≤ η := by
  have hcl : ∀ᶠ p in FF h, |fderiv ℝ s (z0 + p.1 • p.2.1) p.2.2 - fderiv ℝ s z0 h| < η := by
    have hc : Continuous (fun p : ℝ × W × W => fderiv ℝ s (z0 + p.1 • p.2.1) p.2.2) :=
      ((hs.continuous_fderiv one_ne_zero).comp
        (continuous_const.add (continuous_fst.smul (continuous_fst.comp continuous_snd)))).clm_apply
        (continuous_snd.comp continuous_snd)
    have h1 := FF_tendsto h hc
    simp only [zero_smul, add_zero] at h1
    have h2 := h1.eventually (Metric.ball_mem_nhds _ hη)
    filter_upwards [h2] with p hp
    simpa [Real.dist_eq] using hp
  have hcase : ∀ᶠ p in FF h,
      (0 < s (z0 + p.1 • p.2.1) ∧ dd (s z0) (fderiv ℝ s z0 h) = fderiv ℝ s z0 h) ∨
      (s (z0 + p.1 • p.2.1) < 0 ∧ dd (s z0) (fderiv ℝ s z0 h) = 0) ∨
      (fderiv ℝ s z0 h = 0 ∧ dd (s z0) (fderiv ℝ s z0 h) = 0) := by
    by_cases hσ : 0 < s z0
    · filter_upwards [ray_pos hs z0 h (Or.inl hσ)] with p hp
      left; exact ⟨hp, by simp [dd, hσ]⟩
    by_cases hσ' : s z0 < 0
    · filter_upwards [ray_neg hs z0 h (Or.inl hσ')] with p hp
      right; left; exact ⟨hp, by simp [dd, hσ, hσ']⟩
    have h0 : s z0 = 0 := le_antisymm (not_lt.mp hσ) (not_lt.mp hσ')
    rcases lt_trichotomy (fderiv ℝ s z0 h) 0 with ha | ha | ha
    · filter_upwards [ray_neg hs z0 h (Or.inr ⟨h0, ha⟩)] with p hp
      right; left; exact ⟨hp, by simp [dd, hσ, hσ', max_eq_right ha.le]⟩
    · exact Filter.Eventually.of_forall fun p =>
        Or.inr (Or.inr ⟨ha, by simp [dd, hσ, hσ', ha]⟩)
    · filter_upwards [ray_pos hs z0 h (Or.inr ⟨h0, ha⟩)] with p hp
      left; exact ⟨hp, by simp [dd, hσ, hσ', max_eq_left ha.le]⟩
  filter_upwards [hcl, hcase] with p h1 h2
  exact single_step hs _ _ _ _ η hη h1 h2

noncomputable def Fd {W G ι : Type*} [AddCommGroup G] [Module ℝ G] (S : Finset ι)
    (P : W → G) (R : ι → W → G) (s : ι → W → ℝ) (z : W) : G :=
  P z + ∑ i ∈ S, max (s i z) 0 • R i z

noncomputable def Lval {W G ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (S : Finset ι)
    (P : W → G) (R : ι → W → G) (s : ι → W → ℝ) (z0 h : W) : G :=
  fderiv ℝ P z0 h + ∑ i ∈ S, (dd (s i z0) (fderiv ℝ (s i) z0 h) • R i z0
    + max (s i z0) 0 • fderiv ℝ (R i) z0 h)

lemma core {W G ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (S : Finset ι) (P : W → G) (R : ι → W → G)
    (s : ι → W → ℝ) (hP : ContDiff ℝ 1 P) (hR : ∀ i, ContDiff ℝ 1 (R i))
    (hs : ∀ i, ContDiff ℝ 1 (s i)) (w' h' : W) (d : ι → ℝ) (η : ℝ) (hη : 0 < η)
    (hdiff : DifferentiableAt ℝ (Fd S P R s) w')
    (hq : ∀ i ∈ S, ∀ᶠ τ in 𝓝[>] (0:ℝ),
      |τ⁻¹ * (max (s i (w' + τ • h')) 0 - max (s i w') 0) - d i| ≤ η)
    (Lv : G) :
    ‖fderiv ℝ (Fd S P R s) w' h' - Lv‖ ≤
      ‖(fderiv ℝ P w' h' + ∑ i ∈ S, (d i • R i w' + max (s i w') 0 • fderiv ℝ (R i) w' h'))
        - Lv‖ + η * ∑ i ∈ S, ‖R i w'‖ := by
  obtain ⟨q, hq_def⟩ : ∃ q : ι → ℝ → ℝ, ∀ i τ,
      q i τ = τ⁻¹ * (max (s i (w' + τ • h')) 0 - max (s i w') 0) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Pq, hPq⟩ : ∃ Pq : ℝ → G, ∀ τ, Pq τ = τ⁻¹ • (P (w' + τ • h') - P w') :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Rq, hRq⟩ : ∃ Rq : ι → ℝ → G, ∀ i τ,
      Rq i τ = τ⁻¹ • (R i (w' + τ • h') - R i w') := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → G, ∀ τ,
      Q τ = τ⁻¹ • (Fd S P R s (w' + τ • h') - Fd S P R s w') := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ0, hΨ0⟩ : ∃ Ψ0 : G, Ψ0 = fderiv ℝ P w' h' +
      ∑ i ∈ S, (d i • R i w' + max (s i w') 0 • fderiv ℝ (R i) w' h') := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ → G, ∀ τ, e τ =
      ((Pq τ - fderiv ℝ P w' h') + ∑ i ∈ S, q i τ • (R i (w' + τ • h') - R i w')
        + ∑ i ∈ S, max (s i w') 0 • (Rq i τ - fderiv ℝ (R i) w' h')) := ⟨_, fun _ => rfl⟩
  have hQlim : Tendsto Q (𝓝[>] (0:ℝ)) (𝓝 (fderiv ℝ (Fd S P R s) w' h')) := by
    have := line_quot hdiff h'
    refine this.congr (fun τ => ?_)
    rw [hQ]
  have hid : ∀ τ : ℝ, Q τ = e τ + (Ψ0 + ∑ i ∈ S, ((q i τ - d i) • R i w')) := by
    intro τ
    have h1 : Q τ = Pq τ + ∑ i ∈ S, τ⁻¹ • (max (s i (w' + τ • h')) 0 • R i (w' + τ • h')
        - max (s i w') 0 • R i w') := by
      rw [hQ, hPq]
      simp only [Fd]
      rw [add_sub_add_comm, ← Finset.sum_sub_distrib, smul_add, Finset.smul_sum]
    have hi : ∀ i, τ⁻¹ • (max (s i (w' + τ • h')) 0 • R i (w' + τ • h')
        - max (s i w') 0 • R i w') = q i τ • (R i (w' + τ • h') - R i w')
          + max (s i w') 0 • (Rq i τ - fderiv ℝ (R i) w' h')
          + (d i • R i w' + max (s i w') 0 • fderiv ℝ (R i) w' h')
          + (q i τ - d i) • R i w' := by
      intro i
      rw [hq_def, hRq]
      module
    rw [h1, Finset.sum_congr rfl (fun i _ => hi i), he, hΨ0]
    simp only [Finset.sum_add_distrib]
    abel
  have hT1 : Tendsto (fun τ => Pq τ - fderiv ℝ P w' h') (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := (line_quot (hP.differentiable one_ne_zero w') h').sub_const (fderiv ℝ P w' h')
    simp only [sub_self] at this
    refine this.congr (fun τ => ?_)
    rw [hPq]
  have hcontR : ∀ i, Tendsto (fun τ : ℝ => R i (w' + τ • h') - R i w') (𝓝[>] (0:ℝ)) (𝓝 0) := by
    intro i
    have hc : Continuous (fun τ : ℝ => R i (w' + τ • h')) :=
      (hR i).continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    have h0 : Tendsto (fun τ : ℝ => R i (w' + τ • h')) (𝓝[>] (0:ℝ)) (𝓝 (R i w')) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    simpa using h0.sub_const (R i w')
  have hX : ∀ i ∈ S, Tendsto (fun τ => q i τ • (R i (w' + τ • h') - R i w'))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    intro i hi
    have hnorm : Tendsto (fun τ : ℝ => (|d i| + η) * ‖R i (w' + τ • h') - R i w'‖)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := (tendsto_zero_iff_norm_tendsto_zero.1 (hcontR i)).const_mul (|d i| + η)
      simpa using this
    refine squeeze_zero_norm' ?_ hnorm
    filter_upwards [hq i hi] with τ hτ
    rw [norm_smul, Real.norm_eq_abs, hq_def]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have := abs_add_le (τ⁻¹ * (max (s i (w' + τ • h')) 0 - max (s i w') 0) - d i) (d i)
    rw [sub_add_cancel] at this
    linarith
  have hY : ∀ i ∈ S, Tendsto (fun τ => max (s i w') 0 • (Rq i τ - fderiv ℝ (R i) w' h'))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    intro i hi
    have := ((line_quot ((hR i).differentiable one_ne_zero w') h').sub_const
      (fderiv ℝ (R i) w' h')).const_smul (max (s i w') 0)
    simp only [sub_self, smul_zero] at this
    refine this.congr (fun τ => ?_)
    rw [hRq]
  have hE0 : Tendsto e (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := (hT1.add (tendsto_finsetSum S hX)).add (tendsto_finsetSum S hY)
    simp only [Finset.sum_const_zero, add_zero] at h1
    refine h1.congr (fun τ => ?_)
    rw [he]
  have hVlim : Tendsto (fun τ => Ψ0 + ∑ i ∈ S, ((q i τ - d i) • R i w'))
      (𝓝[>] (0:ℝ)) (𝓝 (fderiv ℝ (Fd S P R s) w' h')) := by
    have := hQlim.sub hE0
    simp only [sub_zero] at this
    refine this.congr (fun τ => ?_)
    rw [hid τ]; abel
  have hall : ∀ᶠ τ in 𝓝[>] (0:ℝ), ∀ i ∈ S, |q i τ - d i| ≤ η := by
    rw [Filter.eventually_all_finset]
    intro i hi
    filter_upwards [hq i hi] with τ hτ
    rwa [hq_def]
  have hlim := (hVlim.sub_const Lv).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [hall] with τ hτ
  have e1 : Ψ0 + ∑ i ∈ S, ((q i τ - d i) • R i w') - Lv
      = (Ψ0 - Lv) + ∑ i ∈ S, ((q i τ - d i) • R i w') := by abel
  rw [e1, ← hΨ0]
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hτ i hi) (norm_nonneg _)

lemma KE {W G ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (S : Finset ι) (P : W → G) (R : ι → W → G)
    (s : ι → W → ℝ) (hP : ContDiff ℝ 1 P) (hR : ∀ i, ContDiff ℝ 1 (R i))
    (hs : ∀ i, ContDiff ℝ 1 (s i)) (z0 h : W) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p in FF h, DifferentiableAt ℝ (Fd S P R s) (z0 + p.1 • p.2.1) →
      ‖fderiv ℝ (Fd S P R s) (z0 + p.1 • p.2.1) p.2.2 - Lval S P R s z0 h‖ ≤ ε := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ i ∈ S, (‖R i z0‖ + 1) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact Finset.sum_nonneg (fun i _ => by positivity)
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (B + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; positivity
  have hηB : η * B ≤ ε / 2 := by
    have : η * (B + 1) = ε / 2 := by rw [hη_def]; field_simp
    nlinarith
  obtain ⟨Ψ, hΨ_def⟩ : ∃ Ψ : W × W → G, ∀ q, Ψ q = fderiv ℝ P q.1 q.2 +
      ∑ i ∈ S, (dd (s i z0) (fderiv ℝ (s i) z0 h) • R i q.1
        + max (s i q.1) 0 • fderiv ℝ (R i) q.1 q.2) := ⟨_, fun _ => rfl⟩
  have hΨc : Continuous Ψ := by
    have : Ψ = fun q => fderiv ℝ P q.1 q.2 +
      ∑ i ∈ S, (dd (s i z0) (fderiv ℝ (s i) z0 h) • R i q.1
        + max (s i q.1) 0 • fderiv ℝ (R i) q.1 q.2) := funext hΨ_def
    rw [this]
    refine Continuous.add
      (((hP.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd)
      (continuous_finsetSum _ (fun i _ => ?_))
    exact (continuous_const.smul ((hR i).continuous.comp continuous_fst)).add
      ((((hs i).continuous.comp continuous_fst).max continuous_const).smul
        ((((hR i).continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd))
  have hE1 : ∀ᶠ p in FF h, ‖Ψ (z0 + p.1 • p.2.1, p.2.2) - Lval S P R s z0 h‖ < ε / 2 := by
    have hc : Continuous (fun p : ℝ × W × W => Ψ (z0 + p.1 • p.2.1, p.2.2)) :=
      hΨc.comp (Continuous.prodMk
        (continuous_const.add (continuous_fst.smul (continuous_fst.comp continuous_snd)))
        (continuous_snd.comp continuous_snd))
    have h1 := FF_tendsto h hc
    simp only [zero_smul, add_zero] at h1
    have h0 : Ψ (z0, h) = Lval S P R s z0 h := by
      rw [hΨ_def]; rfl
    rw [h0] at h1
    have h2 := h1.eventually (Metric.ball_mem_nhds _ (half_pos hε))
    filter_upwards [h2] with p hp
    simpa [dist_eq_norm] using hp
  have hE2 : ∀ᶠ p in FF h, ∀ i ∈ S, ‖R i (z0 + p.1 • p.2.1)‖ < ‖R i z0‖ + 1 := by
    rw [Filter.eventually_all_finset]
    intro i _
    have hc : Continuous (fun p : ℝ × W × W => ‖R i (z0 + p.1 • p.2.1)‖) :=
      continuous_norm.comp ((hR i).continuous.comp
        (continuous_const.add (continuous_fst.smul (continuous_fst.comp continuous_snd))))
    have h1 := FF_tendsto h hc
    simp only [zero_smul, add_zero] at h1
    exact h1.eventually (gt_mem_nhds (lt_add_one _))
  have hE3 : ∀ᶠ p in FF h, ∀ i ∈ S, ∀ᶠ τ in 𝓝[>] (0:ℝ),
      |τ⁻¹ * (max (s i (z0 + p.1 • p.2.1 + τ • p.2.2)) 0
        - max (s i (z0 + p.1 • p.2.1)) 0) - dd (s i z0) (fderiv ℝ (s i) z0 h)| ≤ η := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact lemA (hs i) z0 h η hη
  filter_upwards [hE1, hE2, hE3] with p h1 h2 h3 hdiff
  have hΨeq : Ψ (z0 + p.1 • p.2.1, p.2.2) = fderiv ℝ P (z0 + p.1 • p.2.1) p.2.2 +
      ∑ i ∈ S, (dd (s i z0) (fderiv ℝ (s i) z0 h) • R i (z0 + p.1 • p.2.1)
        + max (s i (z0 + p.1 • p.2.1)) 0 • fderiv ℝ (R i) (z0 + p.1 • p.2.1) p.2.2) :=
    hΨ_def _
  have hc : ‖fderiv ℝ (Fd S P R s) (z0 + p.1 • p.2.1) p.2.2 - Lval S P R s z0 h‖ ≤
      ‖Ψ (z0 + p.1 • p.2.1, p.2.2) - Lval S P R s z0 h‖
        + η * ∑ i ∈ S, ‖R i (z0 + p.1 • p.2.1)‖ := by
    rw [hΨeq]
    exact core S P R s hP hR hs (z0 + p.1 • p.2.1) p.2.2
      (fun i => dd (s i z0) (fderiv ℝ (s i) z0 h)) η hη hdiff h3 (Lval S P R s z0 h)
  have hsum : ∑ i ∈ S, ‖R i (z0 + p.1 • p.2.1)‖ ≤ B := by
    rw [hB]
    exact Finset.sum_le_sum (fun i hi => (h2 i hi).le)
  have : η * ∑ i ∈ S, ‖R i (z0 + p.1 • p.2.1)‖ ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left hsum hη.le).trans hηB
  linarith

lemma FF_extract {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (h : W)
    {P : ℝ × W × W → Prop} (hP : ∀ᶠ p in FF h, P p) :
    ∃ δ > 0, ∀ t : ℝ, ∀ g h' : W, 0 < t → t < δ → dist g h < δ → dist h' h < δ →
      P (t, g, h') := by
  rw [Filter.eventually_prod_iff] at hP
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hP
  rw [Filter.eventually_prod_iff] at hpb
  obtain ⟨pc, hpc, pd, hpd, hcd⟩ := hpb
  obtain ⟨u, hu, hu2⟩ := (mem_nhdsGT_iff_exists_Ioo_subset (a := (0:ℝ))).1 hpa
  obtain ⟨e1, he1, hpc'⟩ := Metric.eventually_nhds_iff.1 hpc
  obtain ⟨e2, he2, hpd'⟩ := Metric.eventually_nhds_iff.1 hpd
  refine ⟨min u (min e1 e2), lt_min (Set.mem_Ioi.1 hu) (lt_min he1 he2), fun t g h' ht ht2 hg hh => ?_⟩
  apply hab (x := t)
  · exact hu2 ⟨ht, lt_of_lt_of_le ht2 (min_le_left _ _)⟩
  · apply hcd
    · exact hpc' (lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_left _ _)))
    · exact hpd' (lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_right _ _)))

lemma locLip_Fd {W G ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (S : Finset ι) (P : W → G) (R : ι → W → G)
    (s : ι → W → ℝ) (hP : ContDiff ℝ 1 P) (hR : ∀ i, ContDiff ℝ 1 (R i))
    (hs : ∀ i, ContDiff ℝ 1 (s i)) : LocallyLipschitz (Fd S P R s) := by
  classical
  have hsm : LocallyLipschitz (fun q : ℝ × G => q.1 • q.2) :=
    (contDiff_fst.smul contDiff_snd : ContDiff ℝ 1 (fun q : ℝ × G => q.1 • q.2)).locallyLipschitz
  have hterm : ∀ i, LocallyLipschitz (fun z => max (s i z) 0 • R i z) := fun i =>
    hsm.comp (((hs i).locallyLipschitz.max_const 0).prodMk (hR i).locallyLipschitz)
  have hsum : ∀ T : Finset ι, LocallyLipschitz (fun z => ∑ i ∈ T, max (s i z) 0 • R i z) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using LocallyLipschitz.const (0 : G)
    | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hterm a).add ih
  exact hP.locallyLipschitz.add (hsum S)

lemma semismooth_Fd {W G ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (S : Finset ι) (P : W → G) (R : ι → W → G)
    (s : ι → W → ℝ) (hP : ContDiff ℝ 1 P) (hR : ∀ i, ContDiff ℝ 1 (R i))
    (hs : ∀ i, ContDiff ℝ 1 (s i)) (z0 : W) :
    NonsmoothNewton.AugLagrangian.SemismoothAt (Fd S P R s) z0 := by
  refine ⟨?_, fun h => ⟨Lval S P R s z0 h, fun ε hε => ?_⟩⟩
  · obtain ⟨K, U, hU, hK⟩ := locLip_Fd S P R s hP hR hs z0
    exact ⟨K, U, hU, hK⟩
  · obtain ⟨δe, hδe, hδ⟩ := FF_extract h (KE S P R s hP hR hs z0 h (ε / 2) (half_pos hε))
    refine ⟨δe / 2, half_pos hδe, fun t h' ht htδ hh V hV => ?_⟩
    have hconv : Convex ℝ {V : W →L[ℝ] G | ‖V h' - Lval S P R s z0 h‖ ≤ ε / 2} := by
      have := (convex_closedBall (Lval S P R s z0 h) (ε / 2)).linear_preimage
        (ContinuousLinearMap.apply ℝ G h').toLinearMap
      have e : {V : W →L[ℝ] G | ‖V h' - Lval S P R s z0 h‖ ≤ ε / 2} =
          (ContinuousLinearMap.apply ℝ G h').toLinearMap ⁻¹'
            Metric.closedBall (Lval S P R s z0 h) (ε / 2) := by
        ext V
        simp [Metric.mem_closedBall, dist_eq_norm]
      rw [e]
      exact this
    have hsub : NonsmoothNewton.Shared.bJac (Fd S P R s) (z0 + t • h') ⊆
        {V : W →L[ℝ] G | ‖V h' - Lval S P R s z0 h‖ ≤ ε / 2} := by
      rintro V ⟨u, hu, hdiff, hlim⟩
      have hg : Tendsto (fun k => h' + t⁻¹ • (u k - (z0 + t • h'))) atTop (𝓝 h') := by
        have := (((hu.sub_const (z0 + t • h')).const_smul t⁻¹).const_add h')
        simpa using this
      have hev1 := (Metric.tendsto_nhds.1 hg) (δe / 2) (half_pos hδe)
      have hT : Tendsto (fun k => (ContinuousLinearMap.apply ℝ G h')
          (fderiv ℝ (Fd S P R s) (u k))) atTop (𝓝 ((ContinuousLinearMap.apply ℝ G h') V)) :=
        ((ContinuousLinearMap.apply ℝ G h').continuous.tendsto V).comp hlim
      have hmem : ((ContinuousLinearMap.apply ℝ G h') V) ∈
          Metric.closedBall (Lval S P R s z0 h) (ε / 2) := by
        refine Metric.isClosed_closedBall.mem_of_tendsto hT ?_
        filter_upwards [hev1, Filter.Eventually.of_forall hdiff] with k hk1 hk2
        have hd : dist (h' + t⁻¹ • (u k - (z0 + t • h'))) h < δe := by
          calc dist (h' + t⁻¹ • (u k - (z0 + t • h'))) h
              ≤ dist (h' + t⁻¹ • (u k - (z0 + t • h'))) h' + dist h' h := dist_triangle _ _ _
            _ < δe / 2 + δe / 2 := add_lt_add hk1 (by rw [dist_eq_norm]; exact hh)
            _ = δe := by ring
        have hdh : dist h' h < δe := by rw [dist_eq_norm]; linarith
        have e : z0 + t • (h' + t⁻¹ • (u k - (z0 + t • h'))) = u k := by
          rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
          abel
        have key : DifferentiableAt ℝ (Fd S P R s)
              (z0 + t • (h' + t⁻¹ • (u k - (z0 + t • h')))) →
            ‖fderiv ℝ (Fd S P R s) (z0 + t • (h' + t⁻¹ • (u k - (z0 + t • h')))) h'
              - Lval S P R s z0 h‖ ≤ ε / 2 :=
          hδ t (h' + t⁻¹ • (u k - (z0 + t • h'))) h' ht (by linarith) hd hdh
        rw [e] at key
        have := key hk2
        simpa [Metric.mem_closedBall, dist_eq_norm] using this
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
    have h2 : ‖V h' - Lval S P R s z0 h‖ ≤ ε / 2 := convexHull_min hsub hconv hV
    linarith

lemma psi_deriv (t : ℝ) : HasDerivAt (fun x : ℝ => (max x 0) ^ 2 / 2) (max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have h1 : HasDerivAt (fun _ : ℝ => (0:ℝ)) 0 t := hasDerivAt_const t 0
    have h2 : (fun x : ℝ => (max x 0) ^ 2 / 2) =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
      filter_upwards [gt_mem_nhds ht] with x hx
      simp only [max_eq_right hx.le]
      norm_num
    rw [max_eq_right ht.le]
    exact h1.congr_of_eventuallyEq h2
  · subst ht
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (show 0 < 2 * c by linarith)] with x hx
    show ‖(max (0 + x) 0) ^ 2 / 2 - (max (0:ℝ) 0) ^ 2 / 2 - x • max (0:ℝ) 0‖ ≤ c * ‖x‖
    have e : (max (0 + x) 0) ^ 2 / 2 - (max (0:ℝ) 0) ^ 2 / 2 - x • max (0:ℝ) 0
        = (max x 0) ^ 2 / 2 := by simp
    rw [e]
    have hm0 : 0 ≤ max x 0 := le_max_right _ _
    have hm1 : max x 0 ≤ |x| := max_le (le_abs_self x) (abs_nonneg x)
    have hx' : |x| < 2 * c := by simpa [Real.dist_eq] using hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [abs_nonneg x, mul_le_mul hm1 hm1 hm0 (abs_nonneg x)]
  · have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
      have h : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (((2:ℕ) : ℝ) * t ^ (2 - 1) / 2) t :=
        (hasDerivAt_pow 2 t).div_const 2
      have e : ((2:ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by
        first | (norm_num; done) | (norm_num; ring) | (push_cast; ring)
      rwa [e] at h
    have h2 : (fun x : ℝ => (max x 0) ^ 2 / 2) =ᶠ[𝓝 t] (fun x : ℝ => x ^ 2 / 2) := by
      filter_upwards [lt_mem_nhds ht] with x hx
      simp only [max_eq_left hx.le]
    rw [max_eq_left ht.le]
    exact h1.congr_of_eventuallyEq h2

noncomputable def Lg {W ι : Type*} (S : Finset ι) (r : ℝ) (A : W → ℝ) (s : ι → W → ℝ) (z : W) : ℝ :=
  A z + ∑ i ∈ S, r⁻¹ * ((max (s i z) 0) ^ 2 / 2)

lemma Lg_hasFDeriv {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Finset ι)
    (r : ℝ) (A : W → ℝ) (hA : ContDiff ℝ 2 A) (s : ι → W → ℝ) (hs : ∀ i, ContDiff ℝ 2 (s i))
    (z : W) :
    HasFDerivAt (Lg S r A s)
      (Fd S (fderiv ℝ A) (fun i z => r⁻¹ • fderiv ℝ (s i) z) s z) z := by
  have h1 : HasFDerivAt A (fderiv ℝ A z) z :=
    ((hA.differentiable (by norm_num)) z).hasFDerivAt
  have h2 : ∀ i ∈ S, HasFDerivAt (fun z => r⁻¹ * ((max (s i z) 0) ^ 2 / 2))
      (max (s i z) 0 • (r⁻¹ • fderiv ℝ (s i) z)) z := by
    intro i _
    have hsi : HasFDerivAt (s i) (fderiv ℝ (s i) z) z :=
      (((hs i).differentiable (by norm_num)) z).hasFDerivAt
    have := ((psi_deriv (s i z)).comp_hasFDerivAt z hsi).const_mul r⁻¹
    refine this.congr_fderiv ?_
    rw [smul_comm]
  exact h1.add (HasFDerivAt.fun_sum h2)

lemma Lg_main {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Finset ι)
    (r : ℝ) (A : W → ℝ) (hA : ContDiff ℝ 2 A) (s : ι → W → ℝ) (hs : ∀ i, ContDiff ℝ 2 (s i)) :
    ContDiff ℝ 1 (Lg S r A s) ∧
    (∀ z0, NonsmoothNewton.AugLagrangian.SemismoothAt (fun z => fderiv ℝ (Lg S r A s) z) z0) ∧
    (∀ z0, (∀ i ∈ S, s i z0 ≠ 0) →
      ContDiffAt ℝ 1 (fun z => fderiv ℝ (Lg S r A s) z) z0) := by
  have hP : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hs1 : ∀ i, ContDiff ℝ 1 (s i) := fun i => (hs i).of_le (by norm_num)
  have hR : ∀ i, ContDiff ℝ 1 (fun z => r⁻¹ • fderiv ℝ (s i) z) := fun i =>
    ((hs i).fderiv_right (by norm_num)).const_smul r⁻¹
  have hfd : (fun z => fderiv ℝ (Lg S r A s) z) =
      Fd S (fderiv ℝ A) (fun i z => r⁻¹ • fderiv ℝ (s i) z) s :=
    funext fun z => (Lg_hasFDeriv S r A hA s hs z).fderiv
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (Lg_hasFDeriv S r A hA s hs z).differentiableAt, ?_⟩
    have : fderiv ℝ (Lg S r A s) =
        Fd S (fderiv ℝ A) (fun i z => r⁻¹ • fderiv ℝ (s i) z) s := hfd
    rw [this]
    exact hP.continuous.add (continuous_finsetSum _ fun i _ =>
      ((hs1 i).continuous.max continuous_const).smul (hR i).continuous)
  · intro z0
    rw [hfd]
    exact semismooth_Fd S _ _ s hP hR hs1 z0
  · intro z0 hz
    rw [hfd]
    show ContDiffAt ℝ 1 (fun z => fderiv ℝ A z +
      ∑ i ∈ S, max (s i z) 0 • (r⁻¹ • fderiv ℝ (s i) z)) z0
    refine hP.contDiffAt.add (ContDiffAt.sum fun i hi => ?_)
    have hmax : ContDiffAt ℝ 1 (fun z => max (s i z) 0) z0 := by
      rcases lt_or_gt_of_ne (hz i hi) with hlt | hgt
      · have : (fun z => max (s i z) 0) =ᶠ[𝓝 z0] fun _ => (0:ℝ) := by
          filter_upwards [(hs1 i).continuous.continuousAt.eventually (gt_mem_nhds hlt)]
            with z hz'
          exact max_eq_right hz'.le
        exact contDiffAt_const.congr_of_eventuallyEq this
      · have : (fun z => max (s i z) 0) =ᶠ[𝓝 z0] s i := by
          filter_upwards [(hs1 i).continuous.continuousAt.eventually (lt_mem_nhds hgt)]
            with z hz'
          exact max_eq_left hz'.le
        exact (hs1 i).contDiffAt.congr_of_eventuallyEq this
    exact hmax.smul (hR i).contDiffAt

open NonsmoothNewton.AugLagrangian in
lemma phi_split {r : ℝ} (hr : 0 < r) (a y : ℝ) :
    phi r a y = -(y ^ 2 / (2 * r)) + r⁻¹ * ((max (y + r * a) 0) ^ 2 / 2) := by
  unfold phi
  split_ifs with h
  · rw [max_eq_left h]
    field_simp
    ring
  · rw [max_eq_right (not_le.1 h).le]
    ring

noncomputable def Afun {n m : ℕ} (p : ℕ) (r : ℝ) (f0 : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ := fun z =>
  f0 z.1
    + ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < p),
        (z.2 i * f i z.1 + r / 2 * f i z.1 ^ 2)
    + ∑ i ∈ Finset.univ.filter (fun i : Fin m => p ≤ i.val), (-(z.2 i ^ 2 / (2 * r)))

open NonsmoothNewton.AugLagrangian in
lemma Lag_eq {n m : ℕ} (p : ℕ) (r : ℝ) (hr : 0 < r) (f0 : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    augLagrangian p r f0 f =
      Lg (Finset.univ.filter (fun i : Fin m => p ≤ i.val)) r (Afun p r f0 f)
        (fun i z => z.2 i + r * f i z.1) := by
  funext z
  simp only [augLagrangian, Lg, Afun]
  have hsplit : ∑ i ∈ Finset.univ.filter (fun i : Fin m => p ≤ i.val),
        phi r (f i z.1) (z.2 i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => p ≤ i.val), (-(z.2 i ^ 2 / (2 * r)))
      + ∑ i ∈ Finset.univ.filter (fun i : Fin m => p ≤ i.val),
        r⁻¹ * ((max (z.2 i + r * f i z.1) 0) ^ 2 / 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => phi_split hr _ _)
  rw [hsplit]
  ring

lemma coord_cd {n m : ℕ} (i : Fin m) :
    ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => z.2 i) :=
  ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).contDiff).comp contDiff_snd

lemma Afun_cd {n m : ℕ} (p : ℕ) (r : ℝ) (f0 : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hf0 : ContDiff ℝ 2 f0)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (Afun p r f0 f) := by
  have hfi : ∀ i, ContDiff ℝ 2
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => f i z.1) :=
    fun i => (hf i).comp contDiff_fst
  unfold Afun
  refine ((hf0.comp contDiff_fst).add (ContDiff.sum fun i _ => ?_)).add
    (ContDiff.sum fun i _ => ?_)
  · exact ((coord_cd i).mul (hfi i)).add (contDiff_const.mul ((hfi i).pow 2))
  · exact (((coord_cd i).pow 2).div_const _).neg

lemma sfun_cd {n m : ℕ} (r : ℝ) (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (i : Fin m) :
    ContDiff ℝ 2
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => z.2 i + r * f i z.1) :=
  (coord_cd i).add (contDiff_const.mul ((hf i).comp contDiff_fst))

end P2Mcc48

open NonsmoothNewton.AugLagrangian in
theorem solution {n m : ℕ} (p : ℕ) (r : ℝ) (hr : 0 < r)
    (f0 : EuclideanSpace ℝ (Fin n) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ContDiff ℝ 2 f0) (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 1 (augLagrangian p r f0 f) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      (∃ i : Fin m, p ≤ i.val ∧ y i + r * f i x = 0) →
        SemismoothAt (fun z => fderiv ℝ (augLagrangian p r f0 f) z) (x, y)) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      (∀ i : Fin m, p ≤ i.val → y i + r * f i x ≠ 0) →
        ContDiffAt ℝ 1 (fun z => fderiv ℝ (augLagrangian p r f0 f) z) (x, y)) := by
  have hL := P2Mcc48.Lag_eq p r hr f0 f
  obtain ⟨h1, h2, h3⟩ := P2Mcc48.Lg_main (Finset.univ.filter (fun i : Fin m => p ≤ i.val)) r
    (P2Mcc48.Afun p r f0 f) (P2Mcc48.Afun_cd p r f0 f hf0 hf)
    (fun i z => z.2 i + r * f i z.1) (P2Mcc48.sfun_cd r f hf)
  rw [hL]
  refine ⟨h1, fun x y _ => h2 (x, y), fun x y hxy => h3 (x, y) ?_⟩
  intro i hi
  rw [Finset.mem_filter] at hi
  exact hxy i hi.2
