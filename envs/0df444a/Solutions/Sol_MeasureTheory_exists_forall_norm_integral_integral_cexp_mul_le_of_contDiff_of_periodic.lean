-- Prove2me | solution 1 for MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/91a906a6-4157-586f-a702-8ee5776aa197

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic

set_option autoImplicit false

open MeasureTheory Set

namespace K2Reg

noncomputable def ch (c t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)))

lemma norm_ch (c t : ℝ) : ‖ch c t‖ = 1 := by
  unfold ch
  rw [Complex.norm_exp]
  simp

lemma hasDerivAt_ch (c t : ℝ) : HasDerivAt (ch c) (-(2 * Real.pi * Complex.I * c) * ch c t) t := by
  unfold ch
  have h1 : HasDerivAt (fun t : ℝ => (((c * t : ℝ)) : ℂ)) (c : ℂ) t := by
    have : HasDerivAt (fun t : ℝ => c * t) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    exact this.ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => -(2 * Real.pi * Complex.I * (((c * t : ℝ)) : ℂ)))
      (-(2 * Real.pi * Complex.I * c)) t := (h1.const_mul _).neg
  have h3 := h2.cexp
  convert h3 using 1
  ring

lemma continuous_ch (c : ℝ) : Continuous (ch c) := by
  unfold ch; fun_prop

lemma ch_int_add_one (m : ℤ) (θ : ℝ) : ch m (θ + 1) = ch m θ := by
  unfold ch
  have : (((m : ℝ) * (θ + 1) : ℝ) : ℂ) = ((m : ℝ) * θ : ℝ) + (m : ℂ) := by
    push_cast; ring
  rw [this, mul_add, neg_add, Complex.exp_add]
  have h1 : Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ))) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-m)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [h1, mul_one]

lemma kernel_eq (ξ : ℝ) (m : ℤ) (x θ : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) = ch ξ x * ch m θ := by
  unfold ch
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {F : ℝ × ℝ → ℂ}

noncomputable def D {n : ℕ} (w : Fin n → ℝ × ℝ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  iteratedFDeriv ℝ n F p w

lemma D_zero (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : D (Fin.elim0 : Fin 0 → ℝ × ℝ) F p = F p := by
  simp [D]

lemma continuous_D (hF : ContDiff ℝ 4 F) {n : ℕ} (hn : n ≤ 4) (w : Fin n → ℝ × ℝ) :
    Continuous (D w F) := by
  unfold D
  have h : Continuous (iteratedFDeriv ℝ n F) :=
    hF.continuous_iteratedFDeriv (by exact_mod_cast hn)
  exact (continuous_eval_const w).comp h

lemma norm_D_le (F : ℝ × ℝ → ℂ) {n : ℕ} (w : Fin n → ℝ × ℝ) (hw : ∀ i, ‖w i‖ ≤ 1) (p : ℝ × ℝ) :
    ‖D w F p‖ ≤ ‖iteratedFDeriv ℝ n F p‖ := by
  unfold D
  calc ‖iteratedFDeriv ℝ n F p w‖ ≤ ‖iteratedFDeriv ℝ n F p‖ * ∏ i, ‖w i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖iteratedFDeriv ℝ n F p‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hw i)
    _ = ‖iteratedFDeriv ℝ n F p‖ := mul_one _

lemma hasFDerivAt_D (hF : ContDiff ℝ 4 F) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (D w F) (fderiv ℝ (D w F) p) p ∧
      ∀ v : ℝ × ℝ, fderiv ℝ (D w F) p v = D (Fin.cons v w) F p := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n F) p :=
    (hF.differentiable_iteratedFDeriv (by exact_mod_cast hn)).differentiableAt
  have hdD : DifferentiableAt ℝ (D w F) p := by
    unfold D
    exact hd.continuousMultilinear_apply_const w
  refine ⟨hdD.hasFDerivAt, fun v => ?_⟩
  unfold D
  rw [fderiv_continuousMultilinear_apply_const_apply hd w v, iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]

lemma hasDerivAt_D_x (hF : ContDiff ℝ 4 F) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) (x θ : ℝ) :
    HasDerivAt (fun x => D w F (x, θ)) (D (Fin.cons ((1 : ℝ), (0 : ℝ)) w) F (x, θ)) x := by
  obtain ⟨h1, h2⟩ := hasFDerivAt_D hF hn w (x, θ)
  have hc : HasDerivAt (fun x : ℝ => (x, θ)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
  have := h1.comp_hasDerivAt x hc
  rw [h2] at this
  exact this

lemma hasDerivAt_D_θ (hF : ContDiff ℝ 4 F) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) (x θ : ℝ) :
    HasDerivAt (fun θ => D w F (x, θ)) (D (Fin.cons ((0 : ℝ), (1 : ℝ)) w) F (x, θ)) θ := by
  obtain ⟨h1, h2⟩ := hasFDerivAt_D hF hn w (x, θ)
  have hc : HasDerivAt (fun θ : ℝ => (x, θ)) ((0 : ℝ), (1 : ℝ)) θ :=
    (hasDerivAt_const θ x).prodMk (hasDerivAt_id θ)
  have := h1.comp_hasDerivAt θ hc
  rw [h2] at this
  exact this

lemma D_eq_zero (R : ℝ) (hsupp : ∀ p : ℝ × ℝ, R < |p.1| → F p = 0) {n : ℕ} (w : Fin n → ℝ × ℝ)
    (p : ℝ × ℝ) (hp : R < |p.1|) : D w F p = 0 := by
  unfold D
  have hopen : IsOpen {q : ℝ × ℝ | R < |q.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : F =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hsupp q hq
  have := (hev.iteratedFDeriv ℝ n).eq_of_nhds
  rw [this, iteratedFDeriv_fun_zero]
  simp

lemma D_add_one (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) {n : ℕ} (w : Fin n → ℝ × ℝ)
    (x θ : ℝ) : D w F (x, θ + 1) = D w F (x, θ) := by
  unfold D
  have hfun : (fun z : ℝ × ℝ => F (z + ((0 : ℝ), (1 : ℝ)))) = F := by
    funext z
    have : z + ((0 : ℝ), (1 : ℝ)) = (z.1, z.2 + 1) := by
      ext <;> simp
    rw [this, hper z]
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) n ((0 : ℝ), (1 : ℝ)) (x, θ)
  rw [hfun] at h
  have : ((x, θ) : ℝ × ℝ) + ((0 : ℝ), (1 : ℝ)) = (x, θ + 1) := by ext <;> simp
  rw [this] at h
  rw [h]

lemma ibp_x (R : ℝ) (ξ : ℝ) (v v' : ℝ → ℂ) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hvc : Continuous v) (hv'c : Continuous v')
    (hv0 : ∀ x, R < |x| → v x = 0) (hv'0 : ∀ x, R < |x| → v' x = 0) :
    ∫ x, ch ξ x * v' x = (2 * Real.pi * Complex.I * ξ) * ∫ x, ch ξ x * v x := by
  have hK : IsCompact (Icc (-|R|) (|R|)) := isCompact_Icc
  have hout : ∀ x, x ∉ Icc (-|R|) (|R|) → R < |x| := by
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have : |R| < |x| := by
        rw [abs_of_neg (by linarith [abs_nonneg R] : x < 0)]; linarith
      exact lt_of_le_of_lt (le_abs_self R) this
    · have : |R| < |x| := lt_of_lt_of_le hx (le_abs_self x)
      exact lt_of_le_of_lt (le_abs_self R) this
  have hcs : ∀ g : ℝ → ℂ, (∀ x, R < |x| → g x = 0) → HasCompactSupport g := by
    intro g hg
    exact HasCompactSupport.intro hK (fun x hx => hg x (hout x hx))
  have hint : ∀ g : ℝ → ℂ, Continuous g → (∀ x, R < |x| → g x = 0) →
      Integrable (fun x => ch ξ x * g x) := by
    intro g hg hg0
    apply Continuous.integrable_of_hasCompactSupport ((continuous_ch ξ).mul hg)
    exact (hcs g hg0).mul_left
  have hint' : Integrable (fun x => (-(2 * Real.pi * Complex.I * ξ) * ch ξ x) * v x) := by
    have := (hint v hvc hv0).const_mul (-(2 * Real.pi * Complex.I * ξ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := ch ξ) (v := v)
    (u' := fun t => -(2 * Real.pi * Complex.I * ξ) * ch ξ t) (v' := v')
    (fun x _ => hasDerivAt_ch ξ x) (fun x _ => hv x) (hint v' hv'c hv'0) hint' (hint v hvc hv0)
  rw [h, ← integral_neg, ← integral_const_mul]
  congr 1
  funext x
  ring

lemma ibp_θ (m : ℤ) (v v' : ℝ → ℂ) (hv : ∀ θ, HasDerivAt v (v' θ) θ)
    (hv'c : Continuous v') (hper : v 1 = v 0) :
    ∫ θ in Ico (0 : ℝ) 1, ch m θ * v' θ =
      (2 * Real.pi * Complex.I * m) * ∫ θ in Ico (0 : ℝ) 1, ch m θ * v θ := by
  rw [integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  have hvc : Continuous v := by
    have : Differentiable ℝ v := fun θ => (hv θ).differentiableAt
    exact this.continuous
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := ch m) (v := v)
    (u' := fun t => -(2 * Real.pi * Complex.I * m) * ch m t) (v' := v')
    (fun x _ => hasDerivAt_ch m x) (fun x _ => hv x)
    (((continuous_ch (m : ℝ)).const_mul _).intervalIntegrable 0 1) (hv'c.intervalIntegrable 0 1)
  rw [h]
  have hb : ch m 1 * v 1 - ch m 0 * v 0 = 0 := by
    rw [hper]
    have : ch m 1 = ch m 0 := by
      have := ch_int_add_one m 0
      rw [zero_add] at this
      exact this
    rw [this]; ring
  rw [hb, zero_sub, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  ring

noncomputable def J (ξ : ℝ) (m : ℤ) {n : ℕ} (w : Fin n → ℝ × ℝ) (F : ℝ × ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1, ch ξ x * ch m θ * D w F (x, θ)

section rules

variable (R : ℝ) (hF : ContDiff ℝ 4 F) (hsupp : ∀ p : ℝ × ℝ, R < |p.1| → F p = 0)
  (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p)

include hF hper in

lemma rule_θ (ξ : ℝ) (m : ℤ) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) :
    (2 * Real.pi * Complex.I * m) * J ξ m w F = J ξ m (Fin.cons ((0 : ℝ), (1 : ℝ)) w) F := by
  unfold J
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have h1 : ∀ (u : Fin (n + 1) → ℝ × ℝ) , (fun θ => ch ξ x * ch m θ * D u F (x, θ)) =
      fun θ => ch ξ x * (ch m θ * D u F (x, θ)) := by
    intro u; funext θ; ring
  have h0 : (fun θ => ch ξ x * ch m θ * D w F (x, θ)) =
      fun θ => ch ξ x * (ch m θ * D w F (x, θ)) := by
    funext θ; ring
  rw [h1, h0, integral_const_mul, integral_const_mul]
  have := ibp_θ m (fun θ => D w F (x, θ)) (fun θ => D (Fin.cons ((0 : ℝ), (1 : ℝ)) w) F (x, θ))
    (fun θ => hasDerivAt_D_θ hF hn w x θ)
    ((continuous_D hF (by omega) _).comp (Continuous.prodMk_right x))
    (by simpa using D_add_one hper w x 0)
  rw [this]
  ring

lemma integrable_prod (G : ℝ × ℝ → ℂ) (hG : Continuous G) (hG0 : ∀ p : ℝ × ℝ, R < |p.1| → G p = 0) :
    Integrable (Function.uncurry fun x θ => G (x, θ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))) := by
  have hG' : (Function.uncurry fun x θ => G (x, θ)) = G := by
    funext p; rfl
  rw [hG']
  have hμ : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))) =
      ((volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ico (0 : ℝ) 1)) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict,
      Measure.restrict_univ]
    rfl
  rw [hμ]
  change IntegrableOn G (univ ×ˢ Ico (0 : ℝ) 1) volume

  set K : Set (ℝ × ℝ) := Icc (-|R|) (|R|) ×ˢ Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn G K volume := hG.continuousOn.integrableOn_compact hKc
  have h2 : IntegrableOn G ((univ ×ˢ Ico (0 : ℝ) 1) \ K) volume := by
    apply (integrableOn_zero).congr_fun _ ((MeasurableSet.univ.prod measurableSet_Ico).diff
      hKc.isClosed.measurableSet)
    intro p hp
    simp only [mem_diff, mem_prod, mem_univ, true_and, mem_Ico, hK, mem_Icc, not_and_or,
      not_le] at hp
    obtain ⟨⟨h0, h1⟩, hp⟩ := hp
    symm
    apply hG0
    rcases hp with (hp | hp) | (hp | hp)
    · have : |R| < |p.1| := by
        rw [abs_of_neg (by linarith [abs_nonneg R] : p.1 < 0)]; linarith
      exact lt_of_le_of_lt (le_abs_self R) this
    · exact lt_of_le_of_lt (le_abs_self R) (lt_of_lt_of_le hp (le_abs_self _))
    · exact absurd h0 (not_le.2 hp)
    · exact absurd hp (not_lt.2 h1.le)
  have h3 : IntegrableOn G ((univ ×ˢ Ico (0 : ℝ) 1) ∩ K) volume := h1.mono_set inter_subset_right
  have := h3.union h2
  rwa [inter_union_diff] at this

include hF hsupp in

lemma rule_x (ξ : ℝ) (m : ℤ) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) :
    (2 * Real.pi * Complex.I * ξ) * J ξ m w F = J ξ m (Fin.cons ((1 : ℝ), (0 : ℝ)) w) F := by
  unfold J

  have hI : ∀ (k : ℕ) (hk : k ≤ 4) (u : Fin k → ℝ × ℝ),
      Integrable (Function.uncurry fun x θ => ch ξ x * ch m θ * D u F (x, θ))
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))) := by
    intro k hk u
    apply integrable_prod R (fun p => ch ξ p.1 * ch m p.2 * D u F (p.1, p.2))
    · exact (((continuous_ch ξ).comp continuous_fst).mul ((continuous_ch (m : ℝ)).comp
        continuous_snd)).mul ((continuous_D hF hk u).comp (continuous_fst.prodMk continuous_snd))
    · intro p hp
      rw [D_eq_zero R hsupp u (p.1, p.2) hp, mul_zero]
  rw [integral_integral_swap (hI n hn.le w), integral_integral_swap (hI (n + 1) (by omega) _),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  have h1 : ∀ (k : ℕ) (u : Fin k → ℝ × ℝ), (fun x => ch ξ x * ch m θ * D u F (x, θ)) =
      fun x => ch m θ * (ch ξ x * D u F (x, θ)) := by
    intro k u; funext x; ring
  rw [h1, h1, integral_const_mul, integral_const_mul]
  have := ibp_x R ξ (fun x => D w F (x, θ)) (fun x => D (Fin.cons ((1 : ℝ), (0 : ℝ)) w) F (x, θ))
    (fun x => hasDerivAt_D_x hF hn w x θ)
    ((continuous_D hF hn.le _).comp (Continuous.prodMk_left θ))
    ((continuous_D hF (by omega) _).comp (Continuous.prodMk_left θ))
    (fun x hx => D_eq_zero R hsupp w (x, θ) hx)
    (fun x hx => D_eq_zero R hsupp _ (x, θ) hx)
  rw [this]
  ring

include hF hsupp in

lemma norm_J_le (hR : 0 ≤ R) (ξ : ℝ) (m : ℤ) {n : ℕ} (hn : n ≤ 4) (w : Fin n → ℝ × ℝ)
    (hw : ∀ i, ‖w i‖ ≤ 1) (B : ℝ) (hB : ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ B) :
    ‖J ξ m w F‖ ≤ 2 * R * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  unfold J

  have hinner : ∀ x, ‖∫ θ in Ico (0 : ℝ) 1, ch ξ x * ch m θ * D w F (x, θ)‖ ≤ B := by
    intro x
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      (s := Ico (0 : ℝ) 1) (f := fun θ => ch ξ x * ch m θ * D w F (x, θ)) (C := B)
      (by simp) (fun θ _ => by
        rw [norm_mul, norm_mul, norm_ch, norm_ch, one_mul, one_mul]
        exact (norm_D_le F w hw _).trans (hB _))
    simpa using h
  have hinner0 : ∀ x, R < |x| → (∫ θ in Ico (0 : ℝ) 1, ch ξ x * ch m θ * D w F (x, θ)) = 0 := by
    intro x hx
    have : (fun θ => ch ξ x * ch m θ * D w F (x, θ)) = fun _ => 0 := by
      funext θ
      rw [D_eq_zero R hsupp w (x, θ) hx, mul_zero]
    rw [this, integral_zero]
  have hbound : ∀ x, ‖∫ θ in Ico (0 : ℝ) 1, ch ξ x * ch m θ * D w F (x, θ)‖ ≤
      (Icc (-R) R).indicator (fun _ => B) x := by
    intro x
    by_cases hx : x ∈ Icc (-R) R
    · rw [indicator_of_mem hx]; exact hinner x
    · rw [indicator_of_notMem hx]
      have : R < |x| := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · exact lt_of_lt_of_le hx (le_abs_self x)
      rw [hinner0 x this, norm_zero]
  have hgi : Integrable ((Icc (-R) R).indicator (fun _ : ℝ => B)) := by
    have h : IntegrableOn (fun _ : ℝ => B) (Icc (-R) R) volume :=
      continuousOn_const.integrableOn_compact isCompact_Icc
    exact h.integrable_indicator measurableSet_Icc
  calc ‖∫ x, ∫ θ in Ico (0 : ℝ) 1, ch ξ x * ch m θ * D w F (x, θ)‖
      ≤ ∫ x, (Icc (-R) R).indicator (fun _ => B) x :=
        norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)
    _ = 2 * R * B := by
        rw [integral_indicator_const _ measurableSet_Icc]
        simp only [smul_eq_mul]
        rw [Real.volume_real_Icc_of_le (by linarith)]
        ring

end rules

theorem main (R : ℝ) (hR : 0 ≤ R) (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 4 F)
    (hsupp : ∀ p : ℝ × ℝ, R < |p.1| → F p = 0) (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p)
    (B : ℝ) (hB : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ B) (ξ : ℝ) (m : ℤ) :
    ‖∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1,
        Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) * F (x, θ)‖ ≤
      (32 * R) * B * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) 0)

  have hJ : (∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1,
      Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) * F (x, θ)) =
      J ξ m (Fin.elim0 : Fin 0 → ℝ × ℝ) F := by
    unfold J
    congr 1; funext x; congr 1; funext θ
    rw [kernel_eq, D_zero]
  rw [hJ]
  set e₁ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ))
  set e₂ : ℝ × ℝ := ((0 : ℝ), (1 : ℝ))
  have he₁ : ‖e₁‖ ≤ 1 := by simp [e₁, Prod.norm_def]
  have he₂ : ‖e₂‖ ≤ 1 := by simp [e₂, Prod.norm_def]

  set w0 : Fin 0 → ℝ × ℝ := Fin.elim0
  have hw0 : ∀ i, ‖w0 i‖ ≤ 1 := fun i => Fin.elim0 i
  have hcons : ∀ {k : ℕ} (v : ℝ × ℝ) (u : Fin k → ℝ × ℝ), ‖v‖ ≤ 1 → (∀ i, ‖u i‖ ≤ 1) →
      ∀ i, ‖(Fin.cons v u : Fin (k + 1) → ℝ × ℝ) i‖ ≤ 1 := by
    intro k v u hv hu i
    refine Fin.cases ?_ ?_ i
    · simpa using hv
    · intro j; simpa using hu j

  set A := ‖J ξ m w0 F‖ with hA
  have cξ : (2 * Real.pi * Complex.I * ξ) * ((2 * Real.pi * Complex.I * ξ) * J ξ m w0 F) =
      J ξ m (Fin.cons e₁ (Fin.cons e₁ w0)) F := by
    rw [rule_x R hF hsupp ξ m (by norm_num) w0, rule_x R hF hsupp ξ m (by norm_num)]
  have cm : (2 * Real.pi * Complex.I * m) * ((2 * Real.pi * Complex.I * m) * J ξ m w0 F) =
      J ξ m (Fin.cons e₂ (Fin.cons e₂ w0)) F := by
    rw [rule_θ hF hper ξ m (by norm_num) w0, rule_θ hF hper ξ m (by norm_num)]
  have cξm : (2 * Real.pi * Complex.I * m) * ((2 * Real.pi * Complex.I * m) *
      ((2 * Real.pi * Complex.I * ξ) * ((2 * Real.pi * Complex.I * ξ) * J ξ m w0 F))) =
      J ξ m (Fin.cons e₂ (Fin.cons e₂ (Fin.cons e₁ (Fin.cons e₁ w0)))) F := by
    rw [cξ, rule_θ hF hper ξ m (by norm_num), rule_θ hF hper ξ m (by norm_num)]
  have b0 : A ≤ 2 * R * B := norm_J_le R hF hsupp hR ξ m (by norm_num) w0 hw0 B (hB 0 (by norm_num))
  set c : ℂ := 2 * Real.pi * Complex.I * ξ with hc_def
  set d : ℂ := 2 * Real.pi * Complex.I * m with hd_def
  clear_value c d
  have hc : ‖c‖ = 2 * Real.pi * |ξ| := by
    rw [hc_def]; simp [abs_of_pos Real.pi_pos]
  have hd : ‖d‖ = 2 * Real.pi * |(m : ℝ)| := by
    rw [hd_def]; simp [abs_of_pos Real.pi_pos]
  have bξ : (2 * Real.pi * |ξ|) ^ 2 * A ≤ 2 * R * B := by
    have h := norm_J_le R hF hsupp hR ξ m (n := 2) (by norm_num) (Fin.cons e₁ (Fin.cons e₁ w0))
      (hcons _ _ he₁ (hcons _ _ he₁ hw0)) B (hB 2 (by norm_num))
    rw [← cξ, norm_mul, norm_mul, hc] at h
    have : (2 * Real.pi * |ξ|) ^ 2 * A = 2 * Real.pi * |ξ| * (2 * Real.pi * |ξ| * A) := by ring
    rw [this]; exact h
  have bm : (2 * Real.pi * |(m : ℝ)|) ^ 2 * A ≤ 2 * R * B := by
    have h := norm_J_le R hF hsupp hR ξ m (n := 2) (by norm_num) (Fin.cons e₂ (Fin.cons e₂ w0))
      (hcons _ _ he₂ (hcons _ _ he₂ hw0)) B (hB 2 (by norm_num))
    rw [← cm, norm_mul, norm_mul, hd] at h
    have : (2 * Real.pi * |(m : ℝ)|) ^ 2 * A =
        2 * Real.pi * |(m : ℝ)| * (2 * Real.pi * |(m : ℝ)| * A) := by ring
    rw [this]; exact h
  have bξm : (2 * Real.pi * |(m : ℝ)|) ^ 2 * (2 * Real.pi * |ξ|) ^ 2 * A ≤ 2 * R * B := by
    have h := norm_J_le R hF hsupp hR ξ m (n := 4) (by norm_num)
      (Fin.cons e₂ (Fin.cons e₂ (Fin.cons e₁ (Fin.cons e₁ w0))))
      (hcons _ _ he₂ (hcons _ _ he₂ (hcons _ _ he₁ (hcons _ _ he₁ hw0)))) B (hB 4 (by norm_num))
    rw [← cξm, norm_mul, norm_mul, norm_mul, norm_mul, hc, hd] at h
    have : (2 * Real.pi * |(m : ℝ)|) ^ 2 * (2 * Real.pi * |ξ|) ^ 2 * A =
        2 * Real.pi * |(m : ℝ)| * (2 * Real.pi * |(m : ℝ)| *
          (2 * Real.pi * |ξ| * (2 * Real.pi * |ξ| * A))) := by ring
    rw [this]; exact h

  have hπ : 3 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hA0 : 0 ≤ A := norm_nonneg _
  set a := |ξ| with ha
  set b := |(m : ℝ)| with hb
  have ha0 : 0 ≤ a := abs_nonneg _
  have hb0 : 0 ≤ b := abs_nonneg _
  have hsq : ∀ t : ℝ, t ^ 2 ≤ (2 * Real.pi * t) ^ 2 := by
    intro t
    have h4 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith
    calc t ^ 2 = 1 * t ^ 2 := by ring
      _ ≤ (2 * Real.pi) ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg t)
      _ = (2 * Real.pi * t) ^ 2 := by ring
  have key : (1 + a) ^ 2 * (1 + b) ^ 2 * A ≤ 32 * R * B := by
    have e1 : a ^ 2 * A ≤ 2 * R * B :=
      (mul_le_mul_of_nonneg_right (hsq a) hA0).trans bξ
    have e2 : b ^ 2 * A ≤ 2 * R * B :=
      (mul_le_mul_of_nonneg_right (hsq b) hA0).trans bm
    have e3 : a ^ 2 * b ^ 2 * A ≤ 2 * R * B := by
      have : a ^ 2 * b ^ 2 ≤ (2 * Real.pi * b) ^ 2 * (2 * Real.pi * a) ^ 2 := by
        calc a ^ 2 * b ^ 2 ≤ (2 * Real.pi * a) ^ 2 * (2 * Real.pi * b) ^ 2 :=
              mul_le_mul (hsq a) (hsq b) (sq_nonneg b) (sq_nonneg _)
          _ = (2 * Real.pi * b) ^ 2 * (2 * Real.pi * a) ^ 2 := by ring
      exact (mul_le_mul_of_nonneg_right this hA0).trans bξm
    have expand : (1 + a) ^ 2 * (1 + b) ^ 2 * A ≤ 4 * ((1 + a ^ 2) * (1 + b ^ 2)) * A := by
      apply mul_le_mul_of_nonneg_right _ hA0
      have h1 : (1 + a) ^ 2 ≤ 2 * (1 + a ^ 2) := by nlinarith [sq_nonneg (a - 1)]
      have h2 : (1 + b) ^ 2 ≤ 2 * (1 + b ^ 2) := by nlinarith [sq_nonneg (b - 1)]
      calc (1 + a) ^ 2 * (1 + b) ^ 2 ≤ (2 * (1 + a ^ 2)) * (2 * (1 + b ^ 2)) :=
            mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
        _ = 4 * ((1 + a ^ 2) * (1 + b ^ 2)) := by ring
    calc (1 + a) ^ 2 * (1 + b) ^ 2 * A ≤ 4 * ((1 + a ^ 2) * (1 + b ^ 2)) * A := expand
      _ = 4 * (A + a ^ 2 * A + b ^ 2 * A + a ^ 2 * b ^ 2 * A) := by ring
      _ ≤ 4 * (2 * R * B + 2 * R * B + 2 * R * B + 2 * R * B) := by linarith
      _ = 32 * R * B := by ring
  have h1a : 0 < 1 + a := by linarith
  have h1b : 0 < 1 + b := by linarith
  rw [inv_pow, inv_pow]
  rw [le_mul_inv_iff₀ (by positivity), le_mul_inv_iff₀ (by positivity)]
  calc A * (1 + b) ^ 2 * (1 + a) ^ 2 = (1 + a) ^ 2 * (1 + b) ^ 2 * A := by ring
    _ ≤ 32 * R * B := key

end K2Reg

open K2Reg in
theorem solution
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ℝ × ℝ → ℂ), ContDiff ℝ 4 F → (∀ p : ℝ × ℝ, R < |p.1| → F p = 0) →
        (∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) →
      ∀ B : ℝ, (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ B) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) * F (x, θ)‖ ≤
          C * B * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2 :=
  ⟨32 * R, by positivity, fun F hF hsupp hper B hB ξ m => main R hR F hF hsupp hper B hB ξ m⟩

end S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic
end P2MW
export P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic (solution)
