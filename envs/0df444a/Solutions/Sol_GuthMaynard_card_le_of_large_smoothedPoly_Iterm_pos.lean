-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_smoothedPoly_Iterm_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:47:21.632622+00:00
-- url     : https://prove2.me/submissions/e93eabc1-f69c-47d6-b20d-76692b84c495

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_card_le_mul_topSingularValue_sq
import Theorems.Thm_GuthMaynard_topSingularValue_le_trace
section
namespace GuthMaynardS4.PartBP

open Complex MeasureTheory FourierTransform

lemma supp_ends (g : ℝ → ℝ) (hg : Continuous g) (hs : Function.support g ⊆ Set.Icc 1 2) :
    g 1 = 0 ∧ g 2 = 0 := by
  have h := interior_maximal hs (isOpen_ne_fun hg continuous_const)
  rw [interior_Icc] at h
  constructor
  · by_contra hne
    exact (h hne).1.ne rfl
  · by_contra hne
    exact (h hne).2.ne rfl

lemma int_eq_interval (f : ℝ → ℂ) (hf : ∀ x, x ∉ Set.Icc (1:ℝ) 2 → f x = 0) :
    ∫ x, f x = ∫ x in (1:ℝ)..2, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hf x hx)).symm

lemma norm_cpow_it (t u : ℝ) (hu : 0 < u) : ‖(u : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]; simp

lemma step (j : ℕ) : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → Function.support g ⊆ Set.Icc 1 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 →
      ‖∫ u : ℝ, ((g u : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)‖ ≤ C / |t| ^ j := by
  induction j with
  | zero =>
    intro g hg hs
    refine ⟨∫ u, ‖((g u : ℝ) : ℂ)‖, integral_nonneg (fun _ => norm_nonneg _), fun t ht => ?_⟩
    simp only [pow_zero, div_one]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
    refine Filter.Eventually.of_forall (fun u => ?_)
    by_cases hu : g u = 0
    · simp [hu]
    · have : 0 < u := by have := hs hu; simp at this; linarith [this.1]
      simp [norm_cpow_it t u this]
  | succ j ih =>
    intro g hg hs
    have hgd : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := by
      exact (contDiff_infty_iff_deriv.mp hg).2
    have hg1 : ContDiff ℝ (⊤ : ℕ∞) (fun u => deriv g u * u) := hgd.mul contDiff_id
    have hs1 : Function.support (fun u => deriv g u * u) ⊆ Set.Icc 1 2 := by
      intro x hx
      have : deriv g x ≠ 0 := left_ne_zero_of_mul hx
      exact (support_deriv_subset (f := g) this |> fun h => (closure_minimal hs isClosed_Icc) h)
    obtain ⟨C, hC0, hC⟩ := ih _ hg1 hs1
    refine ⟨C, hC0, fun t ht => ?_⟩
    set c : ℂ := (t : ℂ) * I + 1 with hc
    have hc0 : c ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp [hc] at this
      exact ht this
    have hcn : |t| ≤ ‖c‖ := by
      calc |t| = |c.im| := by simp [hc]
        _ ≤ ‖c‖ := Complex.abs_im_le_norm c
    have hends := supp_ends g hg.continuous hs
    set F : ℝ → ℂ := fun u => (u : ℂ) ^ c / c with hF
    have hFd : ∀ x ∈ Set.uIcc (1:ℝ) 2, HasDerivAt F ((x : ℂ) ^ ((t : ℂ) * I)) x := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hx0 : (0:ℝ) < x := by linarith [hx.1]
      have hx0' : (x:ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      have h1 := ((hasDerivAt_id (x:ℂ)).cpow_const (c := c) (by simpa using Complex.ofReal_mem_slitPlane.2 hx0))
      have h2 := (h1.div_const c).comp_ofReal
      have h3 : HasDerivAt (fun y : ℝ => (y:ℂ) ^ c / c) ((x:ℂ) ^ ((t : ℂ) * I)) x := by
        have hcm : c - 1 = (t : ℂ) * I := by rw [hc]; ring
        convert h2 using 1
        simp only [id]
        rw [hcm]
        field_simp
        rfl
      exact h3
    have hgd1 : ∀ x, HasDerivAt (fun y => ((g y : ℝ) : ℂ)) ((deriv g x : ℝ) : ℂ) x := fun x =>
      ((hg.differentiable (by simp)) x).hasDerivAt.ofReal_comp
    have hF_cont : ContinuousOn F (Set.uIcc 1 2) := fun x hx => (hFd x hx).continuousAt.continuousWithinAt
    have hcont_gd : Continuous (fun x => ((deriv g x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hgd.continuous
    have hcont_g : Continuous (fun x => ((g x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hg.continuous
    have hF'_cont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ ((t : ℂ) * I)) (Set.uIcc 1 2) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hx0 : (0:ℝ) < x := by linarith [hx.1]
      exact (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).comp
        Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := 1) (b := 2) (u := fun y => ((g y : ℝ) : ℂ)) (v := F)
      (u' := fun x => ((deriv g x : ℝ) : ℂ)) (v' := fun x : ℝ => (x : ℂ) ^ ((t : ℂ) * I))
      hcont_g.continuousOn hF_cont (fun x _ => hgd1 x)
      (fun x hx => hFd x (by rw [Set.uIcc_of_le (by norm_num)]; exact Set.Ioo_subset_Icc_self (by simpa using hx)))
      (hcont_gd.intervalIntegrable _ _) (hF'_cont.intervalIntegrable)
    rw [hends.1, hends.2] at hparts
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at hparts
    have hI : ∫ u : ℝ, ((g u : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I) =
        -∫ x in (1:ℝ)..2, ((deriv g x : ℝ) : ℂ) * F x := by
      rw [int_eq_interval _ (fun x hx => by
        have : g x = 0 := by by_contra h; exact hx (hs h)
        simp [this])]
      exact hparts
    have hI2 : ∫ x in (1:ℝ)..2, ((deriv g x : ℝ) : ℂ) * F x =
        c⁻¹ * ∫ u : ℝ, ((deriv g u * u : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I) := by
      rw [int_eq_interval _ (fun x hx => by
        have : deriv g x * x = 0 := by
          by_contra h; exact hx (hs1 h)
        simp [this]), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hx0' : (x:ℂ) ≠ 0 := by exact_mod_cast (by linarith [hx.1] : (0:ℝ) < x).ne'
      simp only [hF]
      rw [hc, Complex.cpow_add _ _ hx0', Complex.cpow_one]
      push_cast
      field_simp
    rw [hI, hI2, norm_neg, norm_mul, norm_inv]
    have hCt := hC t ht
    have hpos : 0 < |t| := abs_pos.2 ht
    have hpj : 0 < |t| ^ j := pow_pos hpos j
    calc ‖c‖⁻¹ * ‖∫ u : ℝ, ((deriv g u * u : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)‖
        ≤ |t|⁻¹ * (C / |t| ^ j) := by
          apply mul_le_mul (inv_anti₀ hpos hcn) hCt (norm_nonneg _) (by positivity)
      _ = C / |t| ^ (j + 1) := by rw [pow_succ]; field_simp

theorem decay_t_zero (w : ℝ → ℝ) (hw : GuthMaynard.IsWeight w) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → ‖GuthMaynard.hHat w t 0‖ ≤ C / |t| ^ j := by
  obtain ⟨C, hC0, hC⟩ := step j (fun u => w u ^ 2) (hw.smooth.pow 2) (by
    intro x hx
    exact hw.support_subset (fun h => hx (by simp [h])))
  refine ⟨C, hC0, fun t ht => ?_⟩
  have := hC t ht
  simpa [GuthMaynard.hHat, Real.fourier_real_eq_integral_exp_smul] using this

lemma h_smooth (w : ℝ → ℝ) (hw : GuthMaynard.IsWeight w) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ((w u ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => ((w u ^ 2 : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.contDiff.comp (hw.smooth.pow 2)).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (u : ℂ) ^ ((t : ℂ) * I)) x := by
      have hl : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => Complex.exp (((Real.log u : ℝ) : ℂ) * ((t : ℂ) * I))) x :=
        (Complex.contDiff_exp.contDiffAt).comp x
          (((Complex.ofRealCLM.contDiff.contDiffAt).comp x
            (Real.contDiffAt_log.2 hx.ne')).mul contDiffAt_const)
      refine hl.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with u hu
      have hu' : (u:ℂ) ≠ 0 := by exact_mod_cast (show (0:ℝ) < u from hu).ne'
      rw [Complex.cpow_def_of_ne_zero hu', Complex.ofReal_log (le_of_lt hu)]
    exact h1.mul h2
  · have : (fun u : ℝ => ((w u ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < 1 by linarith [not_lt.1 hx])] with u hu
      have : w u = 0 := by
        by_contra h; have := hw.support_subset h; simp at this; linarith [this.1, hu.out]
      simp [this]
    exact (contDiffAt_const).congr_of_eventuallyEq this

lemma h_zero (w : ℝ → ℝ) (hw : GuthMaynard.IsWeight w) (t : ℝ) (u : ℝ) (hu : u ∉ Set.Icc (1:ℝ) 2) :
    ((w u ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I) = 0 := by
  have : w u = 0 := by by_contra h; exact hu (hw.support_subset h)
  simp [this]

theorem poisson_h (w : ℝ → ℝ) (hw : GuthMaynard.IsWeight w) (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℤ => GuthMaynard.hHat w t ((m : ℝ) * N)) ∧
    ∑' n : ℤ, (((w ((n : ℝ) / N) ^ 2 : ℝ) : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) ^ ((t : ℂ) * I)) =
      (N : ℂ) * ∑' m : ℤ, GuthMaynard.hHat w t ((m : ℝ) * N) := by
  set h : ℝ → ℂ := fun u : ℝ => ((w u ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I) with hh
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := hNpos.ne'
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => h (x / N)) :=
    (h_smooth w hw t).comp (contDiff_id.div_const _)
  have hcs : HasCompactSupport (fun x : ℝ => h (x / N)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (N:ℝ)) (b := 2 * N))
    intro x hx
    apply h_zero w hw t
    intro hx'
    apply hx
    constructor
    · have := (le_div_iff₀ hNpos).1 hx'.1; linarith
    · have := (div_le_iff₀ hNpos).1 hx'.2; linarith
  let G : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hsm
  have hG : ∀ x, G x = h (x / N) := fun x => rfl
  have hF : ∀ m : ℤ, 𝓕 (G : ℝ → ℂ) m = (N : ℂ) * GuthMaynard.hHat w t ((m : ℝ) * N) := by
    intro m
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [GuthMaynard.hHat, Real.fourier_real_eq_integral_exp_smul, hG]
    have : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * m) * I) • h (v / N) =
        (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * ((m:ℝ) * N)) * I) • h y) (v / N) := by
      intro v
      congr 3
      field_simp
    simp_rw [this]
    rw [Measure.integral_comp_div (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * ((m:ℝ) * N)) * I) • h y) (N:ℝ)]
    rw [abs_of_pos hNpos]
    simp [Complex.real_smul, hh]
  have hsum : Summable (fun m : ℤ => 𝓕 (G : ℝ → ℂ) m) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 G).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have hsum2 : Summable (fun m : ℤ => GuthMaynard.hHat w t ((m : ℝ) * N)) := by
    have := hsum.mul_left ((N:ℂ)⁻¹)
    refine this.congr (fun m => ?_)
    rw [hF]
    have : (N:ℂ) ≠ 0 := by exact_mod_cast hNne
    field_simp
  refine ⟨hsum2, ?_⟩
  have hp := SchwartzMap.tsum_eq_tsum_fourier G 0
  simp only [zero_add, hG] at hp
  rw [SchwartzMap.fourier_coe] at hp
  have h0 : ∀ n : ℤ, (fourier n (((0:ℝ)) : UnitAddCircle)) = 1 := by
    intro n; simp
  simp_rw [h0, mul_one] at hp
  have : ∑' n : ℤ, 𝓕 (G : ℝ → ℂ) n = (N:ℂ) * ∑' m : ℤ, GuthMaynard.hHat w t ((m : ℝ) * N) := by
    simp_rw [hF]; rw [tsum_mul_left]
  rw [← this]; exact hp

end GuthMaynardS4.PartBP
end

section
namespace GuthMaynardS4.PartA

open Complex Set Filter Topology FourierTransform

/-- Smooth functions supported in `[1,2]`, divided by `u`, stay smooth. -/
lemma div_id_smooth {φ : ℝ → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) φ) (s : ∀ u, u ∉ Icc (1:ℝ) 2 → φ u = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => φ u / (u : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have : (fun u : ℝ => φ u / (u : ℂ)) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with u hu
      rw [s u (fun h' => by have : u < 1 := hu; linarith [h'.1]), zero_div]
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (u : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt
    have e : (fun u : ℝ => φ u / (u : ℂ)) = fun u => φ u * ((u⁻¹ : ℝ) : ℂ) := by
      funext u; simp [div_eq_mul_inv]
    rw [e]
    exact h.contDiffAt.mul ((Complex.ofRealCLM.contDiff.contDiffAt (x := x⁻¹)).comp x
      (contDiffAt_inv ℝ hx))

lemma deriv_zero_out {φ : ℝ → ℂ} (s : ∀ u, u ∉ Icc (1:ℝ) 2 → φ u = 0) (u : ℝ)
    (hu : u ∉ Icc (1:ℝ) 2) : deriv φ u = 0 := by
  have : φ =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hu] with v hv using s v hv
  rw [this.deriv_eq]; simp

inductive K : ℕ → (ℝ → ℝ → ℂ) → Prop
  | base (φ : ℝ → ℂ) (h : ContDiff ℝ (⊤ : ℕ∞) φ) (s : ∀ u, u ∉ Icc (1:ℝ) 2 → φ u = 0) :
      K 0 (fun _ u => φ u)
  | add {n f g} : K n f → K n g → K n (fun t u => f t u + g t u)
  | lift {n f} : K n f → K (n+1) f
  | mulT {n f} : K n f → K (n+1) (fun t u => I * (t : ℂ) * f t u)

lemma K.congr {n f g} (h : K n f) (e : ∀ t u, f t u = g t u) : K n g := by
  have : f = g := funext fun t => funext fun u => e t u
  exact this ▸ h

lemma K_props {n f} (h : K n f) :
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (f t)) ∧ (∀ t u, u ∉ Icc (1:ℝ) 2 → f t u = 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t u, ‖f t u‖ ≤ C * (1 + |t|) ^ n := by
  induction h with
  | base φ h s =>
    refine ⟨fun _ => h, fun _ => s, ?_⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
      h.continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun t u => ?_⟩
    simp only [pow_zero, mul_one]
    by_cases hu : u ∈ Icc (1:ℝ) 2
    · exact (hC u hu).trans (le_max_left _ _)
    · rw [s u hu]; simp
  | add _ _ ih1 ih2 =>
    obtain ⟨a1, b1, C1, c1, d1⟩ := ih1
    obtain ⟨a2, b2, C2, c2, d2⟩ := ih2
    refine ⟨fun t => (a1 t).add (a2 t), fun t u hu => by simp [b1 t u hu, b2 t u hu],
      C1 + C2, by positivity, fun t u => ?_⟩
    calc _ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ _ := by linarith [d1 t u, d2 t u]
  | lift _ ih =>
    obtain ⟨a, b, C, c, d⟩ := ih
    refine ⟨a, b, C, c, fun t u => (d t u).trans ?_⟩
    gcongr
    · linarith [abs_nonneg t]
    · linarith
  | mulT _ ih =>
    obtain ⟨a, b, C, c, d⟩ := ih
    refine ⟨fun t => contDiff_const.mul (a t), fun t u hu => by simp [b t u hu], C, c,
      fun t u => ?_⟩
    rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    calc |t| * ‖_‖ ≤ |t| * (C * (1 + |t|) ^ _) := by gcongr; exact d t u
      _ ≤ (1 + |t|) * (C * (1 + |t|) ^ _) := by gcongr; linarith
      _ = _ := by ring

lemma K_deriv {n f} (h : K n f) :
    K (n+1) (fun t u => deriv (f t) u + I * (t : ℂ) * f t u / (u : ℂ)) := by
  induction h with
  | base φ h s =>
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv φ) := by
      have := (contDiff_infty_iff_deriv.mp h).2
      simpa using this
    have k1 := K.base (deriv φ) h1 (deriv_zero_out s)
    have k2 := (K.base _ (div_id_smooth h s) (fun u hu => by simp [s u hu])).mulT
    exact (k1.lift.add k2).congr fun t u => by simp only; ring
  | add h1 h2 ih1 ih2 =>
    rename_i n f g
    have a := (K_props h1).1
    have b := (K_props h2).1
    refine (ih1.add ih2).congr fun t u => ?_
    have da := ((a t).differentiable (by simp)) u
    have db := ((b t).differentiable (by simp)) u
    have : deriv (fun u => f t u + g t u) u = deriv (f t) u + deriv (g t) u :=
      deriv_add da db
    simp only [this]; ring
  | lift h ih => exact ih.lift
  | mulT h ih =>
    rename_i n f
    have a := (K_props h).1
    refine (ih.mulT).congr fun t u => ?_
    have da := ((a t).differentiable (by simp)) u
    have : deriv (fun u => I * (t:ℂ) * f t u) u = I * (t:ℂ) * deriv (f t) u := deriv_const_mul _ da
    simp only [this]; ring

lemma cpow_hasDerivAt (c : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ c) (c * (x : ℂ) ^ c / (x : ℂ)) x := by
  by_cases hc : c = 0
  · subst hc; simpa using hasDerivAt_const x (1:ℂ)
  · have := hasDerivAt_ofReal_cpow_const hx.ne' hc
    convert this using 1
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [Complex.cpow_sub _ _ hx', Complex.cpow_one]; ring

lemma cpow_contDiffAt (c : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ) ^ c) x := by
  have e : (fun y : ℝ => (y : ℂ) ^ c) =ᶠ[𝓝 x] fun y => Complex.exp ((Real.log y : ℂ) * c) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast (show (0:ℝ) < y from hy).ne'
    rw [Complex.cpow_def_of_ne_zero hy', ← Complex.ofReal_log (le_of_lt hy), mul_comm]
  refine ContDiffAt.congr_of_eventuallyEq ?_ e
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (Real.log y : ℂ)) x :=
    ContDiffAt.comp (g := fun y : ℝ => (y : ℂ)) x
      (Complex.ofRealCLM.contDiff.contDiffAt (x := Real.log x))
      (Real.contDiffAt_log.mpr hx.ne')
  have hE : ContDiff ℝ (⊤ : ℕ∞) Complex.exp :=
    ContDiff.restrict_scalars ℝ (𝕜' := ℂ) Complex.contDiff_exp
  exact hE.contDiffAt.comp x (h1.mul contDiffAt_const)

/-- The function `h_t`. -/
noncomputable def h (w : ℝ → ℝ) (t : ℝ) : ℝ → ℂ :=
  fun u : ℝ => ((w u ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)

lemma w_out {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (u : ℝ) (hu : u ∉ Icc (1:ℝ) 2) :
    w u = 0 := by
  by_contra h'
  exact hu (hw.support_subset h')

lemma a_smooth {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => ((w u ^ 2 : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hw.smooth.pow 2)

lemma h_smooth {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (h w t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact (a_smooth hw).contDiffAt.mul (cpow_contDiffAt _ hx)
  · have : h w t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < 1 by linarith [not_lt.mp hx])] with u hu
      simp [h, w_out hw u (fun h' => by have : u < 1 := hu; linarith [h'.1])]
    exact contDiffAt_const.congr_of_eventuallyEq this

lemma iter {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (j : ℕ) :
    ∃ f, K j f ∧ ∀ t, iteratedDeriv j (h w t) = fun u => f t u * (u : ℂ) ^ ((t : ℂ) * I) := by
  induction j with
  | zero =>
    refine ⟨fun _ u => ((w u ^ 2 : ℝ) : ℂ), K.base _ (a_smooth hw) ?_, fun t => ?_⟩
    · intro u hu; simp [w_out hw u hu]
    · funext u; simp [h]
  | succ j ih =>
    obtain ⟨f, hf, he⟩ := ih
    refine ⟨_, K_deriv hf, fun t => ?_⟩
    rw [iteratedDeriv_succ, he t]
    funext u
    have a := (K_props hf).1 t
    have b := (K_props hf).2.1 t
    by_cases hu : u < 1
    · have hu' : u ∉ Icc (1:ℝ) 2 := fun h' => by linarith [h'.1]
      have e : (fun u => f t u * (u : ℂ) ^ ((t : ℂ) * I)) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        rw [b v (fun h' => by have : v < 1 := hv; linarith [h'.1]), zero_mul]
      rw [e.deriv_eq, deriv_zero_out (b) u hu', b u hu']; simp
    · have hu0 : 0 < u := by linarith [not_lt.mp hu]
      have d1 := (a.differentiable (by simp) u).hasDerivAt
      have d2 := cpow_hasDerivAt ((t : ℂ) * I) hu0
      rw [show (fun u : ℝ => f t u * (u : ℂ) ^ ((t : ℂ) * I)) =
        f t * fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I) from rfl, (d1.mul d2).deriv]
      have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
      field_simp

lemma bound {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, MeasureTheory.Integrable (iteratedDeriv n (h w t)) ∧
      ∫ u, ‖iteratedDeriv n (h w t) u‖ ≤ C * (1 + |t|) ^ n := by
  obtain ⟨f, hf, he⟩ := iter hw n
  obtain ⟨a, b, C, c, d⟩ := K_props hf
  refine ⟨C, c, fun t => ?_⟩
  have hc : Continuous (iteratedDeriv n (h w t)) :=
    (h_smooth hw t).continuous_iteratedDeriv n (by exact_mod_cast le_top)
  refine ⟨?_, ?_⟩
  · refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc 1 2) isCompact_Icc ?_
    intro u hu
    by_contra hu'
    apply hu
    simp [he t, b t u hu']
  · have hb : ∀ u, ‖iteratedDeriv n (h w t) u‖ ≤ C * (1 + |t|) ^ n := by
      intro u
      rw [he t]
      by_cases hu : u ∈ Icc (1:ℝ) 2
      · simp only [norm_mul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1])]
        simpa using d t u
      · simp [b t u hu]; positivity
    have hz : ∀ u ∉ Icc (1:ℝ) 2, ‖iteratedDeriv n (h w t) u‖ = 0 := by
      intro u hu; simp [he t, b t u hu]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    calc ∫ u in Icc (1:ℝ) 2, ‖iteratedDeriv n (h w t) u‖
        ≤ ∫ u in Icc (1:ℝ) 2, C * (1 + |t|) ^ n := by
          apply MeasureTheory.setIntegral_mono_on
          · exact hc.norm.continuousOn.integrableOn_Icc
          · exact MeasureTheory.integrableOn_const (by simp)
          · exact measurableSet_Icc
          · intro u _; exact hb u
      _ = _ := by simp <;> norm_num

theorem decay_xi (w : ℝ → ℝ) (hw : GuthMaynard.IsWeight w) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, ξ ≠ 0 → ‖GuthMaynard.hHat w t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j := by
  choose C hC0 hC using bound hw
  refine ⟨C j, hC0 j, fun t ξ hξ => ?_⟩
  have key := congrFun (Real.fourier_iteratedDeriv (N := (j : ℕ∞)) (n := j)
    ((h_smooth hw t).of_le (by exact_mod_cast le_top))
    (fun n hn => (hC n t).1) le_rfl) ξ
  have hle : ‖𝓕 (iteratedDeriv j (h w t)) ξ‖ ≤ ∫ x, ‖iteratedDeriv j (h w t) x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [key] at hle
  have hpos : 0 < |ξ| ^ j := pow_pos (abs_pos.mpr hξ) j
  rw [le_div_iff₀ hpos]
  have hn : ‖(2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ j‖ = (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow]; congr 1
    simp [Real.pi_pos.le, abs_of_pos Real.pi_pos]
  rw [norm_smul, hn] at hle
  have h1 : |ξ| ^ j ≤ (2 * Real.pi * |ξ|) ^ j := by
    apply pow_le_pow_left₀ (abs_nonneg _)
    nlinarith [Real.pi_gt_three, abs_nonneg ξ, abs_pos.mpr hξ]
  have h2 := (hC j t).2
  show ‖GuthMaynard.hHat w t ξ‖ * |ξ| ^ j ≤ _
  have : GuthMaynard.hHat w t ξ = 𝓕 (h w t) ξ := rfl
  rw [this]
  nlinarith [norm_nonneg (𝓕 (h w t) ξ), mul_le_mul_of_nonneg_right h1 (norm_nonneg (𝓕 (h w t) ξ))]

end GuthMaynardS4.PartA
end

section
namespace GuthMaynardS4

end GuthMaynardS4
end

section
namespace GuthMaynardS4

open Module

theorem trace_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    B.trace.re = ∑ i, hB.eigenvalues i := by
  rw [hB.trace_eq_sum_eigenvalues]; simp [Complex.re_sum]

theorem trace_cube_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    (B ^ 3).trace.re = ∑ i, hB.eigenvalues i ^ 3 := by
  have h := hB.spectral_theorem
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have e : B ^ 3 = (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hB.eigenvectorUnitary) (D ^ 3) := by
    rw [map_pow, ← h]
  rw [e, Unitary.conjStarAlgAut_apply]
  have hu : star (hB.eigenvectorUnitary : Matrix ι ι ℂ) * (hB.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simp
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have : D ^ 3 = Matrix.diagonal (fun i => ((hB.eigenvalues i ^ 3 : ℝ) : ℂ)) := by
    simp only [D, Matrix.diagonal_pow]
    congr 1; ext i; simp
  rw [this, Matrix.trace_diagonal]
  simp [Complex.re_sum, ← Complex.ofReal_pow]

end GuthMaynardS4

namespace GuthMaynardS4

open Module

end GuthMaynardS4
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
/-! Blueprint for the corrected Proposition 4.6
(`GuthMaynard.card_le_of_large_smoothedPoly_Iterm_pos`): Lemmas 4.1 and 4.2 (imported), the trace
identities of Lemmas 4.4 and 4.5, and a real inequality. -/
/-- `‖w‖₂² = ∫ w²`. -/
noncomputable def cW (w : ℝ → ℝ) : ℝ := ∫ u, w u ^ 2

/-- `A = ∑_{N < n ≤ 2N} w(n/N)²`, the diagonal entry of `M Mᴴ`. -/
noncomputable def Asum (w : ℝ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), w ((n : ℝ) / N) ^ 2

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartE
open GuthMaynard GuthMaynardGoal.P46
open scoped ComplexOrder
/-- The power-mean inequality `tr(P)³ / n² ≤ tr(P³)` for `P = A Aᴴ`. -/
theorem trace_pow_mean {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    (A * A.conjTranspose).trace.re ^ 3 / (Fintype.card ι : ℝ) ^ 2 ≤
      ((A * A.conjTranspose) ^ 3).trace.re := by
  have hB : (A * A.conjTranspose).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self A
  rw [GuthMaynardS4.trace_cube_sum _ hB, GuthMaynardS4.trace_sum _ hB]
  have hnn : ∀ i, 0 ≤ hB.eigenvalues i := fun i =>
    (Matrix.posSemidef_self_mul_conjTranspose A).eigenvalues_nonneg i
  have := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := hB.eigenvalues)
    (fun i _ => hnn i) 2
  simpa using this

end GuthMaynardGoal.P46.PartE
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias trace_pow_mean := GuthMaynardGoal.P46.PartE.trace_pow_mean

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartE
open GuthMaynard GuthMaynardGoal.P46
open scoped ComplexOrder
/-- `ĥ₀(0) = ‖w‖₂²`. -/
theorem hHat_zero_zero (w : ℝ → ℝ) : hHat w 0 0 = (cW w : ℂ) := by
  simp only [hHat, Real.fourier_real_eq_integral_exp_smul, cW]
  rw [← integral_complex_ofReal]; push_cast; simp

/-- A `δ`-separated set in an interval of length `T` has at most `T/δ + 1` points. -/
theorem card_le_of_separated (δ T a : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (W : Finset ℝ)
    (hsep : IsSeparated δ W) (hW : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) :
    (W.card : ℝ) ≤ T / δ + 1 := by
  set f : ℝ → ℕ := fun t => ⌊(t - a) / δ⌋₊ with hf
  have hmaps : ∀ t ∈ W, f t ∈ Finset.range (⌊T / δ⌋₊ + 1) := by
    intro t ht
    have h := hW t ht
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    exact div_le_div_of_nonneg_right (by linarith [h.2]) hδ.le
  have hinj : Set.InjOn f W := by
    intro t ht t' ht' he
    by_contra hne
    have hs := hsep t ht t' ht' hne
    have k1 := (hW t ht).1
    have k2 := (hW t' ht').1
    -- wlog-style: one of them is at least δ larger
    have key : ∀ u v : ℝ, a ≤ u → a ≤ v → u + δ ≤ v → f u < f v := by
      intro u v hu hv huv
      have h0 : 0 ≤ (u - a) / δ := div_nonneg (by linarith) hδ.le
      have h1 : (u - a) / δ + 1 ≤ (v - a) / δ := by
        rw [div_add_one hδ.ne']
        exact div_le_div_of_nonneg_right (by linarith) hδ.le
      have := Nat.floor_le_floor (R := ℝ) h1
      rw [Nat.floor_add_one h0] at this
      simp only [hf]; omega
    rcases le_total t t' with hle | hle
    · rw [abs_of_nonpos (by linarith)] at hs
      have := key t t' k1 k2 (by linarith); omega
    · rw [abs_of_nonneg (by linarith)] at hs
      have := key t' t k2 k1 (by linarith); omega
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range] at hc
  have hc' : (W.card : ℝ) ≤ (⌊T / δ⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  have := Nat.floor_le (div_nonneg hT hδ.le)
  linarith

end GuthMaynardGoal.P46.PartE
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias card_le_of_separated := GuthMaynardGoal.P46.PartE.card_le_of_separated

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartE
open GuthMaynard GuthMaynardGoal.P46
open scoped ComplexOrder
/-- The real inequality that assembles everything (all constants explicit). -/
theorem final_real (C1 K1 K2 c : ℝ) (hC1 : 0 ≤ C1) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N T m x A tr3 I0 s σ : ℝ), 1 ≤ N → 1 ≤ m → T ≤ N ^ (4 / 3 : ℝ) → m ≤ 2 * T →
      0 ≤ x → 0 ≤ A →
      m ≤ C1 * N ^ (1 - 2 * σ) * x ^ 2 →
      x ≤ 2 * (tr3 - (m * A) ^ 3 / m ^ 2) ^ (1 / 6 : ℝ) + 2 * (m * A / m) ^ (1 / 2 : ℝ) →
      (m * A) ^ 3 / m ^ 2 ≤ tr3 →
      tr3 = I0 + s →
      I0 ≤ N ^ 3 * m * c ^ 3 + K1 * N ^ 3 →
      |A - N * c| ≤ K2 / N →
      m ≤ C * (N ^ (2 - 2 * σ) + N ^ (1 - 2 * σ) * max s 0 ^ (1 / 3 : ℝ)) := by
  set K3 : ℝ := K1 + 6 * c ^ 2 * K2 with hK3
  have hK3n : 0 ≤ K3 := by positivity
  set R : ℝ := K3 ^ (1 / 3 : ℝ) with hR
  have hRn : 0 ≤ R := Real.rpow_nonneg hK3n _
  refine ⟨8 * C1 * (1 + R + c + K2), by positivity, ?_⟩
  intro N T m x A tr3 I0 s σ hN hm hT hmT hx hA hmx hxX hX htr hI0 hAc
  have hN0 : 0 < N := by linarith
  have hm0 : 0 < m := by linarith
  have e1 : (m * A) ^ 3 / m ^ 2 = m * A ^ 3 := by field_simp
  have e2 : m * A / m = A := by field_simp
  rw [e1] at hxX hX; rw [e2] at hxX
  set X := tr3 - m * A ^ 3 with hXdef
  have hX0 : 0 ≤ X := by linarith
  -- m ≤ 2 N²
  have hN2 : m ≤ 2 * N ^ 2 := by
    have h1 : N ^ (4 / 3 : ℝ) ≤ N ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    rw [Real.rpow_two] at h1
    linarith
  -- (Nc)³ - A³ ≤ 3 c² K2 N
  have hcube : N ^ 3 * c ^ 3 - A ^ 3 ≤ 3 * c ^ 2 * K2 * N := by
    by_cases hAN : N * c ≤ A
    · have : (N * c) ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (by positivity) hAN 3
      have : 0 ≤ 3 * c ^ 2 * K2 * N := by positivity
      nlinarith
    · push Not at hAN
      have hd : N * c - A ≤ K2 / N := by
        have := neg_abs_le (A - N * c); have := abs_le.1 hAc; linarith
      have hd' : (N * c - A) * N ≤ K2 := by
        rw [le_div_iff₀ hN0] at hd; exact hd
      have hq : (N * c) ^ 2 + N * c * A + A ^ 2 ≤ 3 * (N * c) ^ 2 := by nlinarith
      have hpos : 0 ≤ N * c - A := by linarith
      calc N ^ 3 * c ^ 3 - A ^ 3 = (N * c - A) * ((N * c) ^ 2 + N * c * A + A ^ 2) := by ring
        _ ≤ (N * c - A) * (3 * (N * c) ^ 2) := mul_le_mul_of_nonneg_left hq hpos
        _ = ((N * c - A) * N) * (3 * c ^ 2 * N) := by ring
        _ ≤ K2 * (3 * c ^ 2 * N) := mul_le_mul_of_nonneg_right hd' (by positivity)
        _ = 3 * c ^ 2 * K2 * N := by ring
  have hXle : X ≤ max s 0 + K3 * N ^ 3 := by
    have h1 : m * (N ^ 3 * c ^ 3 - A ^ 3) ≤ m * (3 * c ^ 2 * K2 * N) :=
      mul_le_mul_of_nonneg_left hcube hm0.le
    have h2 : m * (3 * c ^ 2 * K2 * N) ≤ (2 * N ^ 2) * (3 * c ^ 2 * K2 * N) :=
      mul_le_mul_of_nonneg_right hN2 (by positivity)
    have h3 := le_max_left s 0
    simp only [hXdef, hK3]
    linarith
  -- X^{1/3} ≤ S + R N
  set S := max s 0 ^ (1 / 3 : ℝ) with hS
  have hSn : 0 ≤ S := Real.rpow_nonneg (le_max_right _ _) _
  have hX13 : X ^ (1 / 3 : ℝ) ≤ S + R * N := by
    calc X ^ (1 / 3 : ℝ) ≤ (max s 0 + K3 * N ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hX0 hXle (by norm_num)
      _ ≤ S + (K3 * N ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_add_le_add_rpow (le_max_right _ _) (by positivity) (by norm_num) (by norm_num)
      _ = S + R * N := by
          rw [Real.mul_rpow hK3n (by positivity)]
          have : (N ^ 3) ^ (1 / 3 : ℝ) = N := by
            rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
            exact Real.pow_rpow_inv_natCast hN0.le (by norm_num)
          rw [this]
  -- x² ≤ 8 X^{1/3} + 8 A
  have hx2 : x ^ 2 ≤ 8 * X ^ (1 / 3 : ℝ) + 8 * A := by
    set p := X ^ (1 / 6 : ℝ) with hp
    set q := A ^ (1 / 2 : ℝ) with hq
    have hp0 : 0 ≤ p := Real.rpow_nonneg hX0 _
    have hq0 : 0 ≤ q := Real.rpow_nonneg hA _
    have hp2 : p ^ 2 = X ^ (1 / 3 : ℝ) := by
      rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
    have hq2 : q ^ 2 = A := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hA]; norm_num
    have : x ^ 2 ≤ (2 * p + 2 * q) ^ 2 := pow_le_pow_left₀ hx hxX 2
    nlinarith [sq_nonneg (p - q)]
  have hAle : A ≤ N * (c + K2) := by
    have h1 : A - N * c ≤ K2 / N := (le_abs_self _).trans hAc
    have h2 : K2 / N ≤ K2 := div_le_self hK2 hN
    have h3 : K2 ≤ K2 * N := le_mul_of_one_le_right hK2 hN
    linarith
  set P := N ^ (1 - 2 * σ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hN0.le _
  have hQ : N ^ (2 - 2 * σ) = P * N := by
    rw [hP, ← Real.rpow_add_one hN0.ne']; ring_nf
  rw [hQ]
  have hx2' : x ^ 2 ≤ 8 * S + 8 * (R + c + K2) * N := by
    linarith only [hx2, hX13, hAle]
  have hfin : m ≤ C1 * P * (8 * S + 8 * (R + c + K2) * N) :=
    hmx.trans (mul_le_mul_of_nonneg_left hx2' (by positivity))
  have k1 : 0 ≤ C1 * P * N := by positivity
  have k2 : 0 ≤ C1 * P * S := by positivity
  have k3 : 0 ≤ C1 * (R + c + K2) * P * S := by positivity
  linarith only [hfin, k1, k3]

theorem w_one_two (w : ℝ → ℝ) (hw : IsWeight w) : w 1 = 0 ∧ w 2 = 0 :=
  GuthMaynardS4.PartBP.supp_ends w hw.smooth.continuous hw.support_subset

theorem tsum_w_sq (w : ℝ → ℝ) (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N) :
    ∑' n : ℤ, w ((n : ℝ) / N) ^ 2 = Asum w N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tsum_eq_sum (s := (Finset.Ioc N (2 * N)).map Nat.castEmbedding)]
  · rw [Finset.sum_map]; rfl
  · intro b hb
    by_contra hne
    have hne' : w ((b : ℝ) / N) ≠ 0 := fun h => hne (by rw [h]; ring)
    have hI := hw.support_subset hne'
    have h1 : (b : ℝ) / N ≠ 1 := fun h => hne' (by rw [h]; exact (w_one_two w hw).1)
    have h2 : (b : ℝ) / N ≠ 2 := fun h => hne' (by rw [h]; exact (w_one_two w hw).2)
    have l1 : 1 < (b : ℝ) / N := lt_of_le_of_ne hI.1 (Ne.symm h1)
    have l2 : (b : ℝ) / N < 2 := lt_of_le_of_ne hI.2 h2
    rw [lt_div_iff₀ hN0] at l1
    rw [div_lt_iff₀ hN0] at l2
    have i1 : (N : ℤ) < b := by exact_mod_cast (by push_cast; linarith : ((N : ℤ) : ℝ) < b)
    have i2 : b < 2 * (N : ℤ) := by exact_mod_cast (by push_cast; linarith : (b : ℝ) < ((2 * (N : ℤ) : ℤ) : ℝ))
    apply hb
    rw [Finset.mem_map]
    refine ⟨b.toNat, ?_, ?_⟩
    · rw [Finset.mem_Ioc]; omega
    · simp only [Nat.castEmbedding_apply]; omega

/-- Lemma 4.4's main term: `A = N ‖w‖₂² + O(1/N)` (Poisson summation and Lemma 4.3). -/
theorem Asum_close (w : ℝ → ℝ) (hw : IsWeight w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → |Asum w N - N * cW w| ≤ K / N := by
  obtain ⟨C, hC0, hC⟩ := GuthMaynardS4.PartA.decay_xi w hw 2
  have hZs : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  set Z := ∑' m : ℤ, 1 / (m : ℝ) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun m => by positivity
  refine ⟨C * Z, by positivity, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hs, hp⟩ := GuthMaynardS4.PartBP.poisson_h w hw 0 N hN
  have hL : ∑' n : ℤ, (((w ((n : ℝ) / N) ^ 2 : ℝ) : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) ^ (((0:ℝ) : ℂ) * Complex.I))
      = (Asum w N : ℂ) := by
    simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
    rw [← Complex.ofReal_tsum, tsum_w_sq w hw N hN]
  rw [hL, hs.tsum_eq_add_tsum_ite 0] at hp
  simp only [Int.cast_zero, zero_mul, hHat_zero_zero] at hp
  set g : ℤ → ℂ := fun m => if m = 0 then 0 else hHat w 0 ((m : ℝ) * N) with hg
  have hbound : ‖∑' m, g m‖ ≤ C / (N : ℝ) ^ 2 * Z := by
    have hpt : ∀ m : ℤ, ‖g m‖ ≤ C / (N : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) := by
      intro m
      by_cases hm : m = 0
      · simp [hg, hm]
      · simp only [hg, if_neg hm]
        have hmN : (m : ℝ) * N ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hm) hN0.ne'
        have := hC 0 ((m : ℝ) * N) hmN
        refine this.trans (le_of_eq ?_)
        rw [abs_zero, add_zero, one_pow, mul_one, sq_abs]
        have : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
        field_simp
    have := tsum_of_norm_bounded (hZs.mul_left (C / (N : ℝ) ^ 2)).hasSum hpt
    rwa [tsum_mul_left] at this
  have hdiff : (((Asum w N - N * cW w : ℝ)) : ℂ) = (N : ℂ) * ∑' m, g m := by
    push_cast; rw [hp]; ring
  have habs : |Asum w N - N * cW w| = (N : ℝ) * ‖∑' m, g m‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff, norm_mul, Complex.norm_natCast]
  rw [habs]
  calc (N : ℝ) * ‖∑' m, g m‖ ≤ N * (C / (N : ℝ) ^ 2 * Z) :=
        mul_le_mul_of_nonneg_left hbound hN0.le
    _ = C * Z / N := by field_simp

end GuthMaynardGoal.P46.PartE
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias Asum_close := GuthMaynardGoal.P46.PartE.Asum_close

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartE
open GuthMaynard GuthMaynardGoal.P46
open scoped ComplexOrder
theorem w_sq_integrable (w : ℝ → ℝ) (hw : IsWeight w) :
    MeasureTheory.Integrable (fun u => w u ^ 2) := by
  apply (hw.smooth.continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2))
  intro x hx
  have : w x = 0 := by by_contra h; exact hx (hw.support_subset h)
  simp [this]

theorem hHat_norm_le (w : ℝ → ℝ) (hw : IsWeight w) (τ : ℝ) : ‖hHat w τ 0‖ ≤ cW w := by
  simp only [hHat, Real.fourier_real_eq_integral_exp_smul, cW, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, one_smul]
  apply MeasureTheory.norm_integral_le_of_norm_le (w_sq_integrable w hw)
  refine MeasureTheory.ae_of_all _ fun v => ?_
  by_cases h : w v = 0
  · simp [h]
  · have hv := hw.support_subset h
    have hv0 : (0:ℝ) < v := by linarith [hv.1]
    rw [norm_mul, GuthMaynardS4.PartBP.norm_cpow_it τ v hv0, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

theorem diag_sum (W : Finset ℝ) (c : ℂ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, (if t₁ = t₂ ∧ t₂ = t₃ then c else 0) = W.card * c := by
  have : ∀ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, (if t₁ = t₂ ∧ t₂ = t₃ then c else 0) = c := by
    intro t₁ h₁
    simp_rw [ite_and]
    rw [Finset.sum_eq_single t₁]
    · simp [Finset.sum_ite_eq, h₁]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd h₁ h
  rw [Finset.sum_congr rfl this]; simp

end GuthMaynardGoal.P46.PartE
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias final_real := GuthMaynardGoal.P46.PartE.final_real

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartT
open GuthMaynard GuthMaynardGoal.P46 Complex
theorem tsum_split (f : (Fin 3 → ℤ) → ℂ) (hf : Summable f) :
    ∑' m, f m = f 0 + ∑' m : {m : Fin 3 → ℤ // m ≠ 0}, f m := by
  classical
  rw [hf.tsum_eq_add_tsum_ite 0]
  congr 1
  rw [show (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, f m) = ∑' m : ({m | m ≠ 0} : Set (Fin 3 → ℤ)), f m
    from rfl, tsum_subtype]
  congr 1
  ext m
  by_cases h : m = 0 <;> simp [h]

end GuthMaynardGoal.P46.PartT
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias tsum_split := GuthMaynardGoal.P46.PartT.tsum_split

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartT
open GuthMaynard GuthMaynardGoal.P46 Complex
theorem smoothedPoly_zero (w : ℝ → ℝ) (hw : IsWeight w) (b : ℕ → ℂ) (t : ℝ) :
    smoothedPoly w 0 b t = 0 := by
  have h0 : w 0 = 0 := by
    by_contra h
    have := hw.support_subset h
    norm_num at this
  simp [smoothedPoly, h0]

theorem trace_one (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) :
    ((weightMatrix w N W) * (weightMatrix w N W).conjTranspose).trace.re = W.card * Asum w N := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    weightMatrix, Complex.re_sum]
  have : ∀ (t : W) (n : Finset.Ioc N (2 * N)),
      ((w ((n : ℕ) / N : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (((t : ℝ) : ℂ) * I) *
        star ((w ((n : ℕ) / N : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (((t : ℝ) : ℂ) * I))).re =
        w ((n : ℕ) / N : ℝ) ^ 2 := by
    intro t n
    rw [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl, Complex.mul_conj']
    have hn : (0:ℝ) < ((n : ℕ) : ℝ) := by
      have := (Finset.mem_Ioc.1 n.2).1; exact_mod_cast (Nat.zero_le N).trans_lt this
    rw [norm_mul, show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by simp,
      GuthMaynardS4.PartBP.norm_cpow_it _ _ hn]
    simp [Complex.norm_real, ← Complex.ofReal_pow]
  simp only [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, Asum]
  congr 1
  exact Finset.sum_coe_sort (Finset.Ioc N (2 * N)) (fun n : ℕ => w ((n : ℝ) / N) ^ 2)

end GuthMaynardGoal.P46.PartT
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias trace_one := GuthMaynardGoal.P46.PartT.trace_one

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartT
open GuthMaynard GuthMaynardGoal.P46 Complex
noncomputable def Ssum (w : ℝ → ℝ) (N : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), ((w ((n : ℝ) / N) ^ 2 : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ ((τ : ℂ) * I)

lemma conj_cpow_nat (n : ℕ) (s : ℂ) :
    starRingEnd ℂ ((n : ℂ) ^ s) = (n : ℂ) ^ (starRingEnd ℂ s) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)]
  simp

lemma entry (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (t t' : W) :
    ((weightMatrix w N W) * (weightMatrix w N W).conjTranspose) t t' =
      Ssum w N ((t : ℝ) - t') := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, weightMatrix, Ssum]
  rw [← Finset.sum_coe_sort (Finset.Ioc N (2 * N))]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by
    have := (Finset.mem_Ioc.1 n.2).1
    exact_mod_cast ((Nat.zero_le N).trans_lt this).ne'
  rw [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl, map_mul, conj_cpow_nat,
    Complex.conj_ofReal]
  rw [show ((w ((n : ℕ) / N : ℝ) ^ 2 : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ ((((t : ℝ) - t' : ℝ) : ℂ) * I) =
      (w ((n : ℕ) / N : ℝ) : ℂ) * (w ((n : ℕ) / N : ℝ) : ℂ) *
        (((n : ℕ) : ℂ) ^ (((t : ℝ) : ℂ) * I) * ((n : ℕ) : ℂ) ^ ((starRingEnd ℂ) (((t' : ℝ) : ℂ) * I)))
    by rw [← Complex.cpow_add _ _ hn]; congr 1
       · push_cast; ring
       · congr 1; simp [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring]
  ring

lemma w_zero_of (w : ℝ → ℝ) (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N) (b : ℤ)
    (hb : b ∉ (Finset.Ioc N (2 * N)).image (Nat.cast : ℕ → ℤ)) : w ((b : ℝ) / N) = 0 := by
  by_contra h
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hmem := hw.support_subset h
  have h1 := (le_div_iff₀ hNpos).1 hmem.1
  have h2 := (div_le_iff₀ hNpos).1 hmem.2
  have hne : (b : ℝ) / N ≠ 1 := by
    intro he; rw [he] at h
    exact h (GuthMaynardS4.PartBP.supp_ends w hw.smooth.continuous hw.support_subset).1
  have hne' : (b : ℝ) ≠ N := by
    intro he; apply hne; rw [he, div_self hNpos.ne']
  have hb1 : (N : ℤ) < b := by
    have : (N : ℝ) < b := lt_of_le_of_ne (by linarith) (Ne.symm hne')
    exact_mod_cast this
  have hb2 : b ≤ 2 * (N : ℤ) := by
    have : (b : ℝ) ≤ 2 * N := by linarith
    exact_mod_cast this
  apply hb
  rw [Finset.mem_image]
  refine ⟨b.toNat, ?_, Int.toNat_of_nonneg (by omega)⟩
  rw [Finset.mem_Ioc]; omega

lemma Ssum_eq (w : ℝ → ℝ) (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) :
    Ssum w N τ = (N : ℂ) ^ ((τ : ℂ) * I) * ((N : ℂ) * ∑' m : ℤ, hHat w τ ((m : ℝ) * N)) := by
  rw [← (GuthMaynardS4.PartBP.poisson_h w hw τ N hN).2]
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  rw [tsum_eq_sum (s := (Finset.Ioc N (2 * N)).image (Nat.cast : ℕ → ℤ))
    (fun b hb => by simp [w_zero_of w hw N hN b hb])]
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h), Finset.mul_sum, Ssum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN : ((n : ℕ) : ℂ) = ((((n : ℝ) / N : ℝ)) : ℂ) * ((N : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hNpos.ne']; simp
  rw [hnN, Complex.mul_cpow_ofReal_nonneg (div_nonneg (Nat.cast_nonneg _) hNpos.le) hNpos.le]
  push_cast
  ring

def fin3Equiv : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun m := (m 0, m 1, m 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv m := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

lemma triple (f g h : ℤ → ℂ) (hf : Summable f) (hg : Summable g) (hh : Summable h) :
    Summable (fun m : Fin 3 → ℤ => f (m 0) * g (m 1) * h (m 2)) ∧
      (∑' a, f a) * (∑' b, g b) * (∑' c, h c) =
        ∑' m : Fin 3 → ℤ, f (m 0) * g (m 1) * h (m 2) := by
  have nf : Summable fun x => ‖f x‖ := summable_norm_iff.2 hf
  have ng : Summable fun x => ‖g x‖ := summable_norm_iff.2 hg
  have nh : Summable fun x => ‖h x‖ := summable_norm_iff.2 hh
  have ngh := Summable.mul_norm ng nh
  have key : Summable (fun p : ℤ × ℤ × ℤ => f p.1 * (g p.2.1 * h p.2.2)) :=
    summable_mul_of_summable_norm (g := fun q : ℤ × ℤ => g q.1 * h q.2) nf ngh
  have heq : (fun m : Fin 3 → ℤ => f (m 0) * g (m 1) * h (m 2)) =
      (fun p : ℤ × ℤ × ℤ => f p.1 * (g p.2.1 * h p.2.2)) ∘ fin3Equiv := by
    ext m; show _ = f (m 0) * (g (m 1) * h (m 2)); ring
  refine ⟨?_, ?_⟩
  · rw [heq]; exact (fin3Equiv.summable_iff).2 key
  · rw [heq, Function.comp_def,
      fin3Equiv.tsum_eq (fun p : ℤ × ℤ × ℤ => f p.1 * (g p.2.1 * h p.2.2)), mul_assoc,
      tsum_mul_tsum_of_summable_norm ng nh,
      tsum_mul_tsum_of_summable_norm (g := fun q : ℤ × ℤ => g q.1 * h q.2) nf ngh]

lemma trace_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) :
    (P ^ 3).trace = ∑ i, ∑ j, ∑ k, P i j * P j k * P k i := by
  rw [pow_succ, pow_succ, pow_one, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem trace_three (w : ℝ → ℝ) (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) :
    Summable (Iterm w N W) ∧
      (((weightMatrix w N W) * (weightMatrix w N W).conjTranspose) ^ 3).trace =
        ∑' m : Fin 3 → ℤ, Iterm w N W m := by
  set F : ℝ → ℤ → ℂ := fun τ m => hHat w τ ((m : ℝ) * N) with hF
  have hFs : ∀ τ, Summable (F τ) := fun τ => (GuthMaynardS4.PartBP.poisson_h w hw τ N hN).1
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  -- each triple term
  have hterm : ∀ t₁ t₂ t₃ : ℝ, Ssum w N (t₁ - t₂) * Ssum w N (t₂ - t₃) * Ssum w N (t₃ - t₁) =
      (N : ℂ) ^ 3 * ∑' m : Fin 3 → ℤ, F (t₁ - t₂) (m 0) * F (t₂ - t₃) (m 1) * F (t₃ - t₁) (m 2) := by
    intro t₁ t₂ t₃
    rw [Ssum_eq w hw N hN, Ssum_eq w hw N hN, Ssum_eq w hw N hN,
      ← (triple _ _ _ (hFs (t₁ - t₂)) (hFs (t₂ - t₃)) (hFs (t₃ - t₁))).2]
    have hph : (N : ℂ) ^ ((((t₁ - t₂ : ℝ)) : ℂ) * I) * (N : ℂ) ^ ((((t₂ - t₃ : ℝ)) : ℂ) * I) *
        (N : ℂ) ^ ((((t₃ - t₁ : ℝ)) : ℂ) * I) = 1 := by
      rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]
      rw [show (((t₁ - t₂ : ℝ)) : ℂ) * I + (((t₂ - t₃ : ℝ)) : ℂ) * I + (((t₃ - t₁ : ℝ)) : ℂ) * I = 0
        by push_cast; ring]
      simp
    simp only [hF]
    linear_combination ((N : ℂ) * ∑' m : ℤ, hHat w (t₁ - t₂) ((m : ℝ) * N)) *
      ((N : ℂ) * ∑' m : ℤ, hHat w (t₂ - t₃) ((m : ℝ) * N)) *
      ((N : ℂ) * ∑' m : ℤ, hHat w (t₃ - t₁) ((m : ℝ) * N)) * hph
  have hsumT : ∀ t₁ t₂ t₃ : ℝ, Summable (fun m : Fin 3 → ℤ =>
      F (t₁ - t₂) (m 0) * F (t₂ - t₃) (m 1) * F (t₃ - t₁) (m 2)) :=
    fun t₁ t₂ t₃ => (triple _ _ _ (hFs (t₁ - t₂)) (hFs (t₂ - t₃)) (hFs (t₃ - t₁))).1
  have hIt : Iterm w N W = fun m => (N : ℂ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      F (t₁ - t₂) (m 0) * F (t₂ - t₃) (m 1) * F (t₃ - t₁) (m 2) := by
    ext m; simp [Iterm, hF]
  have hS : Summable (Iterm w N W) := by
    rw [hIt]
    refine Summable.mul_left _ ?_
    refine summable_sum fun t₁ _ => summable_sum fun t₂ _ => summable_sum fun t₃ _ => hsumT _ _ _
  refine ⟨hS, ?_⟩
  rw [hIt, tsum_mul_left]
  rw [Summable.tsum_finsetSum (fun t₁ _ => summable_sum fun t₂ _ => summable_sum fun t₃ _ =>
    hsumT _ _ _)]
  simp_rw [Summable.tsum_finsetSum (fun t₂ _ => summable_sum fun t₃ _ => hsumT _ _ _)]
  simp_rw [Summable.tsum_finsetSum (fun t₃ _ => hsumT _ _ _)]
  simp only [Finset.mul_sum, ← hterm]
  rw [trace_cube]
  simp only [entry]
  rw [← Finset.sum_coe_sort W]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [← Finset.sum_coe_sort W]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [← Finset.sum_coe_sort W]

end GuthMaynardGoal.P46.PartT
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias trace_three := GuthMaynardGoal.P46.PartT.trace_three

alias smoothedPoly_zero := GuthMaynardGoal.P46.PartT.smoothedPoly_zero

theorem cW_nonneg (w : ℝ → ℝ) : 0 ≤ cW w := by
  unfold cW; exact MeasureTheory.integral_nonneg fun u => sq_nonneg _

end GuthMaynardGoal.P46
end

section
namespace GuthMaynardGoal.P46.PartE
open GuthMaynard GuthMaynardGoal.P46
open scoped ComplexOrder
/-- The `m = 0` term of Lemma 4.5: `I₀ = N³ |W| ‖w‖₂⁶ + O(N³)` for `T^ε`-separated `W` in an
interval of length `T ≥ 1` (Lemma 4.3 at `ξ = 0` kills the off-diagonal terms). -/
theorem Iterm_zero_close (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ), 1 ≤ T → ∀ (N : ℕ) (W : Finset ℝ) (a : ℝ),
      IsSeparated (T ^ ε) W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖Iterm w N W 0 - (N : ℂ) ^ 3 * W.card * (cW w : ℂ) ^ 3‖ ≤ K * (N : ℝ) ^ 3 := by
  set j : ℕ := ⌈3 / ε⌉₊ with hj
  obtain ⟨C, hC0, hC⟩ := GuthMaynardS4.PartBP.decay_t_zero w hw j
  have hc0 := cW_nonneg w
  refine ⟨8 * C * cW w ^ 2, by positivity, ?_⟩
  intro T hT N W a hsep hW
  have hT0 : 0 < T := by linarith
  have hεj : 3 ≤ ε * j := by
    have := Nat.le_ceil (3 / ε)
    rw [← hj] at this
    have := mul_le_mul_of_nonneg_left this hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have hdec : ∀ τ : ℝ, T ^ ε ≤ |τ| → ‖hHat w τ 0‖ ≤ C / T ^ 3 := by
    intro τ hτ
    have hτ0 : τ ≠ 0 := by
      intro h; rw [h, abs_zero] at hτ; linarith [Real.rpow_pos_of_pos hT0 ε]
    refine (hC τ hτ0).trans ?_
    apply div_le_div_of_nonneg_left hC0 (by positivity)
    calc T ^ 3 = T ^ (3:ℝ) := by norm_cast
      _ ≤ T ^ (ε * j) := Real.rpow_le_rpow_of_exponent_le hT hεj
      _ = (T ^ ε) ^ j := by rw [Real.rpow_mul hT0.le, Real.rpow_natCast]
      _ ≤ |τ| ^ j := pow_le_pow_left₀ (by positivity) hτ j
  set B : ℝ := C / T ^ 3 * cW w ^ 2 with hB
  have hpt : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
      ‖hHat w (t₁ - t₂) 0 * hHat w (t₂ - t₃) 0 * hHat w (t₃ - t₁) 0 -
        (if t₁ = t₂ ∧ t₂ = t₃ then (cW w : ℂ) ^ 3 else 0)‖ ≤ B := by
    intro t₁ h₁ t₂ h₂ t₃ h₃
    have n1 := hHat_norm_le w hw (t₁ - t₂)
    have n2 := hHat_norm_le w hw (t₂ - t₃)
    have n3 := hHat_norm_le w hw (t₃ - t₁)
    have hCT : 0 ≤ C / T ^ 3 := by positivity
    by_cases hd : t₁ = t₂ ∧ t₂ = t₃
    · obtain ⟨rfl, rfl⟩ := hd
      simp only [sub_self, and_self, if_true, hHat_zero_zero]
      rw [show (cW w : ℂ) * cW w * cW w - (cW w : ℂ) ^ 3 = 0 by ring, norm_zero]
      positivity
    · rw [if_neg hd, sub_zero, norm_mul, norm_mul]
      rcases not_and_or.1 hd with h12 | h23
      · have e := hdec _ (hsep t₁ h₁ t₂ h₂ h12)
        calc ‖hHat w (t₁ - t₂) 0‖ * ‖hHat w (t₂ - t₃) 0‖ * ‖hHat w (t₃ - t₁) 0‖
            ≤ C / T ^ 3 * cW w * cW w := by gcongr
          _ = B := by rw [hB]; ring
      · have e := hdec _ (hsep t₂ h₂ t₃ h₃ h23)
        calc ‖hHat w (t₁ - t₂) 0‖ * ‖hHat w (t₂ - t₃) 0‖ * ‖hHat w (t₃ - t₁) 0‖
            ≤ cW w * (C / T ^ 3) * cW w := by gcongr
          _ = B := by rw [hB]; ring
  have hIt : Iterm w N W 0 - (N : ℂ) ^ 3 * W.card * (cW w : ℂ) ^ 3 =
      (N : ℂ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        (hHat w (t₁ - t₂) 0 * hHat w (t₂ - t₃) 0 * hHat w (t₃ - t₁) 0 -
          (if t₁ = t₂ ∧ t₂ = t₃ then (cW w : ℂ) ^ 3 else 0)) := by
    simp only [Finset.sum_sub_distrib, diag_sum, mul_sub, Iterm, Pi.zero_apply, Int.cast_zero,
      zero_mul]
    ring
  have hsum : ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        (hHat w (t₁ - t₂) 0 * hHat w (t₂ - t₃) 0 * hHat w (t₃ - t₁) 0 -
          (if t₁ = t₂ ∧ t₂ = t₃ then (cW w : ℂ) ^ 3 else 0))‖ ≤ (W.card : ℝ) ^ 3 * B := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, B := by
          refine Finset.sum_le_sum fun t₁ h₁ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun t₂ h₂ => (norm_sum_le _ _).trans ?_
          exact Finset.sum_le_sum fun t₃ h₃ => hpt t₁ h₁ t₂ h₂ t₃ h₃
      _ = (W.card : ℝ) ^ 3 * B := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : (W.card : ℝ) ≤ 2 * T := by
    have hδ : 0 < T ^ ε := Real.rpow_pos_of_pos hT0 _
    have h := card_le_of_separated (T ^ ε) T a hδ hT0.le W hsep hW
    have h1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
    have h2 : T / T ^ ε ≤ T := div_le_self hT0.le h1
    linarith
  have hcard3 : (W.card : ℝ) ^ 3 * B ≤ 8 * C * cW w ^ 2 := by
    have : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 := pow_le_pow_left₀ (by positivity) hcard 3
    calc (W.card : ℝ) ^ 3 * B ≤ (2 * T) ^ 3 * B := mul_le_mul_of_nonneg_right this (by positivity)
      _ = 8 * C * cW w ^ 2 := by rw [hB]; field_simp; ring
  rw [hIt, norm_mul, norm_pow, Complex.norm_natCast, mul_comm]
  exact mul_le_mul_of_nonneg_right (hsum.trans hcard3) (by positivity)

end GuthMaynardGoal.P46.PartE
end

section
namespace GuthMaynardGoal.P46
open GuthMaynard
alias Iterm_zero_close := GuthMaynardGoal.P46.PartE.Iterm_zero_close

theorem Asum_nonneg (w : ℝ → ℝ) (N : ℕ) : 0 ≤ Asum w N := by
  unfold Asum; exact Finset.sum_nonneg fun n _ => sq_nonneg _

theorem main (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ),
      (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) → (∀ t ∈ W, (N : ℝ) ^ σ < ‖smoothedPoly w N b t‖) →
      let s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re
      (W.card : ℝ) ≤ C * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (1 - 2 * σ) * max s 0 ^ (1 / 3 : ℝ)) := by
  obtain ⟨C1, hC1⟩ := card_le_mul_topSingularValue_sq w hw
  obtain ⟨K1, hK1, hI0⟩ := Iterm_zero_close w hw ε hε
  obtain ⟨K2, hK2, hA⟩ := Asum_close w hw
  obtain ⟨C, hC0, hC⟩ := final_real |C1| K1 K2 (cW w) (abs_nonneg _) hK1 hK2 (cW_nonneg w)
  refine ⟨C, ?_⟩
  intro T N hNT σ b hb W a hsep hwin hD s
  rcases W.eq_empty_or_nonempty with hWe | ⟨t0, ht0⟩
  · subst hWe
    simp only [Finset.card_empty, Nat.cast_zero]
    apply mul_nonneg hC0
    have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
    exact add_nonneg (Real.rpow_nonneg hN0 _)
      (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg (le_max_right _ _) _))
  -- `N ≥ 1`, since `D_0 ≡ 0`
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have := hD t0 ht0
      rw [smoothedPoly_zero w hw] at this
      simp only [norm_zero] at this
      exact absurd this (not_lt.2 (Real.rpow_nonneg (by simp) _))
    · exact h0
  have hN1r : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hT1 : 1 ≤ T := hN1r.trans hNT.2
  have hT0 : 0 ≤ T := by linarith
  have hT43 : T ≤ (N : ℝ) ^ (4 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hT0 _) hNT.1 (by norm_num : (0:ℝ) ≤ 4 / 3)
    rwa [← Real.rpow_mul hT0, show (3 / 4 : ℝ) * (4 / 3) = 1 by norm_num, Real.rpow_one] at h
  have hm1 : (1:ℝ) ≤ W.card := by exact_mod_cast Finset.card_pos.2 ⟨t0, ht0⟩
  have hm2 : (W.card : ℝ) ≤ 2 * T := by
    have hδ : 0 < T ^ ε := Real.rpow_pos_of_pos (by linarith) _
    have h := card_le_of_separated (T ^ ε) T a hδ hT0 W hsep hwin
    have h1 : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
    have h2 : T / T ^ ε ≤ T := div_le_self hT0 h1
    linarith
  set M := weightMatrix w N W with hM
  have hcardι : (Fintype.card W : ℝ) = W.card := by simp
  have h41 := hC1 N hN1 σ b hb W (fun t ht => (hD t ht).le)
  have h41' : (W.card : ℝ) ≤ |C1| * (N : ℝ) ^ (1 - 2 * σ) * topSingularValue M ^ 2 := by
    refine h41.trans ?_
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
  have h42 := topSingularValue_le_trace M
  have hpm := trace_pow_mean M
  rw [trace_one w N W, hcardι] at h42 hpm
  obtain ⟨hsum, htr3⟩ := trace_three w hw N hN1 W
  have htr3re : ((M * M.conjTranspose) ^ 3).trace.re = (Iterm w N W 0).re + s := by
    rw [htr3, tsum_split _ hsum, Complex.add_re]
  have hI0re : (Iterm w N W 0).re ≤ (N : ℝ) ^ 3 * W.card * cW w ^ 3 + K1 * (N : ℝ) ^ 3 := by
    have h := hI0 T hT1 N W a hsep hwin
    have hre := (Complex.abs_re_le_norm _).trans h
    have e : (Iterm w N W 0 - (N : ℂ) ^ 3 * W.card * (cW w : ℂ) ^ 3).re =
        (Iterm w N W 0).re - (N : ℝ) ^ 3 * W.card * cW w ^ 3 := by
      simp [Complex.sub_re, Complex.mul_re, pow_succ, Complex.ofReal_re, Complex.ofReal_im]
    rw [e] at hre
    linarith [le_abs_self ((Iterm w N W 0).re - (N : ℝ) ^ 3 * W.card * cW w ^ 3)]
  have hsnn : 0 ≤ topSingularValue M := by
    unfold topSingularValue; exact LinearMap.singularValues_nonneg _ _
  exact hC (N : ℝ) T W.card (topSingularValue M) (Asum w N)
    (((M * M.conjTranspose) ^ 3).trace.re) (Iterm w N W 0).re s σ hN1r hm1 hT43 hm2 hsnn
    (Asum_nonneg w N) h41' h42 hpm htr3re hI0re (hA N hN1)

end GuthMaynardGoal.P46
end

section
open GuthMaynard

theorem solution (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ),
      (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) → (∀ t ∈ W, (N : ℝ) ^ σ < ‖smoothedPoly w N b t‖) →
      let s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re
      (W.card : ℝ) ≤ C * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (1 - 2 * σ) * max s 0 ^ (1 / 3 : ℝ)) :=
  GuthMaynardGoal.P46.main w hw ε hε

end
