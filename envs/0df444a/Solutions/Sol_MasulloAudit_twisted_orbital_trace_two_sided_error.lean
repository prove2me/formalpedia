-- Prove2me | solution 1 for MasulloAudit.twisted_orbital_trace_two_sided_error
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:48:42.852161+00:00
-- url     : https://prove2.me/submissions/e90369b0-a554-4382-b90f-b35484af8601

import Mathlib

open Real Complex MeasureTheory Set
open scoped FourierTransform ContDiff

theorem poisson_aux (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hpos : tsupport φ ⊆ Set.Ioi 0) (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℤ => φ (p ^ n)) ∧
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p) =
      (Real.log p : ℂ) * ∑' n : ℤ, φ (p ^ n) := by
  set L := Real.log p with hLdef
  have hL : 0 < L := Real.log_pos hp
  -- the rescaled pulled-back function h(v) = φ(exp(-L v))
  set h : ℝ → ℂ := fun v => φ (Real.exp (-(L * v))) with hhdef
  have hh_smooth : ContDiff ℝ ∞ h :=
    hφ.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)
  have hh_supp : HasCompactSupport h := by
    have hK : IsCompact ((fun t => -Real.log t / L) '' tsupport φ) := by
      refine hc.isCompact.image_of_continuousOn ?_
      refine ContinuousOn.div_const (ContinuousOn.neg ?_) _
      exact Real.continuousOn_log.mono fun t ht => (ne_of_gt (hpos ht))
    refine HasCompactSupport.intro hK fun v hv => ?_
    by_contra hne
    apply hv
    refine ⟨Real.exp (-(L * v)), subset_tsupport _ hne, ?_⟩
    simp only [Real.log_exp]
    field_simp
  let F : SchwartzMap ℝ ℂ := hh_supp.toSchwartzMap hh_smooth
  have hF : ∀ v, F v = h v := fun v => rfl
  -- Fourier transform of h at integers is a rescaled Mellin transform
  have hFour : ∀ k : ℤ, 𝓕 (h) (k : ℝ) = (L : ℂ)⁻¹ * mellin φ (2 * π * I * k / L) := by
    intro k
    have h1 := mellin_eq_fourier (fun t => φ (t ^ L)) (s := 2 * π * I * k)
    have h2 := mellin_comp_rpow φ (2 * π * I * k) L
    have hre : (2 * π * I * (k : ℂ)).re = 0 := by simp
    have him : (2 * π * I * (k : ℂ)).im / (2 * π) = k := by
      simp
    rw [hre, him] at h1
    have hfun : (fun u : ℝ => Real.exp (-0 * u) • φ (Real.exp (-u) ^ L)) = h := by
      funext u
      simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, hhdef]
      rw [← Real.exp_mul]; congr 2; ring
    rw [hfun] at h1
    rw [← h1, h2, abs_of_pos hL, Complex.real_smul]
    push_cast; ring_nf
  have hPoisson := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp only [zero_add, hF, SchwartzMap.fourier_coe] at hPoisson
  have hsumF : Summable fun k : ℤ => 𝓕 F (k : ℝ) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 F).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  simp only [SchwartzMap.fourier_coe] at hsumF
  have hcoe : (F : ℝ → ℂ) = h := rfl
  rw [hcoe] at hsumF hPoisson
  have hfour0 : ∀ k : ℤ, fourier k ((0 : ℝ) : UnitAddCircle) = 1 := by
    intro k; simp
  simp only [hfour0, mul_one, hFour] at hPoisson hsumF
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsum : Summable (fun k : ℤ => mellin φ (2 * π * I * k / L)) := by
    have := hsumF.mul_left (L : ℂ)
    refine this.congr fun k => ?_
    field_simp
  have hsumh : Summable fun k : ℤ => F (k : ℝ) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  rw [hcoe] at hsumh
  have hhn : ∀ n : ℤ, h (-n : ℤ) = φ (p ^ n) := by
    intro n
    simp only [hhdef]
    congr 1
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith)]
    congr 1; push_cast; ring
  have hsumφ : Summable (fun n : ℤ => φ (p ^ n)) := by
    have := (Equiv.neg ℤ).summable_iff.mpr hsumh
    refine this.congr fun n => ?_
    simpa using hhn n
  refine ⟨hsumφ, hsum, ?_⟩
  have hlhs : ∑' n : ℤ, h n = ∑' n : ℤ, φ (p ^ n) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hhdef, Equiv.neg_apply]
    congr 1
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith)]
    congr 1; push_cast; ring
  rw [hlhs, tsum_mul_left] at hPoisson
  rw [hPoisson]
  field_simp

theorem solution (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Set.Ioi 0) (h1 : φ 1 = 0) (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p - 1 / 2)) ∧
    Summable (fun n : ℕ => ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) *
      (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹))) ∧
    Summable (fun n : ℕ => ((Real.log p * (Real.sqrt (p ^ (n + 1)) -
      1 / Real.sqrt (p ^ (n + 1))) : ℝ) : ℂ) * φ ((p ^ (n + 1))⁻¹)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p - 1 / 2) =
      ∑' n : ℕ, ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) *
        (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹)) +
      ∑' n : ℕ, ((Real.log p * (Real.sqrt (p ^ (n + 1)) -
        1 / Real.sqrt (p ^ (n + 1))) : ℝ) : ℂ) * φ ((p ^ (n + 1))⁻¹) := by
  set ψ : ℝ → ℂ := fun t => φ t * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hψdef
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hx0 : 0 < x := hsupp hx
      refine (hφ.contDiffAt).mul ?_
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (Real.contDiffAt_rpow_const_of_ne hx0.ne')
    · have hev : ψ =ᶠ[nhds x] fun _ => 0 := by
        have : (tsupport φ)ᶜ ∈ nhds x := (isClosed_tsupport φ).isOpen_compl.mem_nhds hx
        filter_upwards [this] with y hy
        simp [hψdef, image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hψ_sub0 : Function.support ψ ⊆ Function.support φ := by
    intro t ht
    simp only [Function.mem_support, hψdef] at ht ⊢
    intro h; exact ht (by simp [h])
  have hψ_sub : tsupport ψ ⊆ tsupport φ := closure_mono hψ_sub0
  have hψ_c : HasCompactSupport ψ := hc.mono hψ_sub0
  have hψ_pos : tsupport ψ ⊆ Set.Ioi 0 := hψ_sub.trans hsupp
  have hmel : ∀ s : ℂ, mellin ψ s = mellin φ (s - 1 / 2) := by
    intro s
    have h1 := mellin_cpow_smul φ s (-(1 / 2 : ℂ))
    rw [show s + -(1 / 2 : ℂ) = s - 1 / 2 by ring] at h1
    rw [← h1]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [hψdef, smul_eq_mul]
    rw [Complex.ofReal_cpow ht0]
    push_cast
    ring
  obtain ⟨hg, hS, hE⟩ := poisson_aux ψ hψ_smooth hψ_c hψ_pos p hp
  simp only [hmel] at hS hE
  have hp0 : 0 < p := by linarith
  set L := Real.log p with hLdef
  set g : ℤ → ℂ := fun n => ψ (p ^ n) with hgdef
  -- explicit forms
  set s : ℕ → ℝ := fun n => Real.sqrt (p ^ (n + 1)) with hsdef
  have hs1 : ∀ n, 1 ≤ s n := fun n => by
    simp only [hsdef]; rw [Real.one_le_sqrt]; exact one_le_pow₀ hp.le
  have hspos : ∀ n, 0 < s n := fun n => lt_of_lt_of_le one_pos (hs1 n)
  set a : ℕ → ℂ := fun n => ((1 / s n : ℝ) : ℂ) * φ (p ^ (n + 1)) with hadef
  set b : ℕ → ℂ := fun n => ((s n : ℝ) : ℂ) * φ ((p ^ (n + 1))⁻¹) with hbdef
  set c : ℕ → ℂ := fun n => ((1 / s n : ℝ) : ℂ) * φ ((p ^ (n + 1))⁻¹) with hcdef
  have hga : ∀ n : ℕ, g ((n : ℤ) + 1) = a n := by
    intro n
    have hpn : 0 < p ^ (n + 1) := pow_pos hp0 _
    simp only [hgdef, hψdef, hadef, hsdef]
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      Real.sqrt_eq_rpow, Real.rpow_neg hpn.le, one_div]
    push_cast; ring
  have hgb : ∀ n : ℕ, g (-((n : ℤ) + 1)) = b n := by
    intro n
    have hpn : 0 < p ^ (n + 1) := pow_pos hp0 _
    simp only [hgdef, hψdef, hbdef, hsdef]
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      Real.inv_rpow hpn.le, Real.rpow_neg hpn.le, inv_inv, Real.sqrt_eq_rpow]
    ring
  have hg0 : g 0 = 0 := by simp [hgdef, hψdef, h1]
  have hsa : Summable a := by
    have := (hg.comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ) + 1) by
      intro x y h; simpa using h))
    exact this.congr fun n => hga n
  have hsb : Summable b := by
    have := (hg.comp_injective (show Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) by
      intro x y h; simpa using h))
    exact this.congr fun n => hgb n
  have hsc : Summable c := by
    refine Summable.of_norm_bounded hsb.norm fun n => ?_
    simp only [hcdef, hbdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [abs_of_pos (by have := hspos n; positivity), abs_of_pos (hspos n)]
    rw [div_le_iff₀ (hspos n)]
    nlinarith [hs1 n]
  have hu : ∀ n : ℕ, ((L / s n : ℝ) : ℂ) * (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹)) =
      (L : ℂ) * a n + (L : ℂ) * c n := by
    intro n; simp only [hadef, hcdef]; push_cast; ring
  have hv : ∀ n : ℕ, ((L * (s n - 1 / s n)) : ℝ) * φ ((p ^ (n + 1))⁻¹) =
      (L : ℂ) * b n - (L : ℂ) * c n := by
    intro n; simp only [hbdef, hcdef]; push_cast; ring
  have hSu : Summable (fun n : ℕ => ((L / s n : ℝ) : ℂ) *
      (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹))) := by
    simp only [hu]; exact (hsa.mul_left _).add (hsc.mul_left _)
  have hSv : Summable (fun n : ℕ => ((L * (s n - 1 / s n) : ℝ) : ℂ) *
      φ ((p ^ (n + 1))⁻¹)) := by
    simp only [hv]; exact (hsb.mul_left _).sub (hsc.mul_left _)
  refine ⟨hS, hSu, hSv, ?_⟩
  rw [hE, ← hSu.tsum_add hSv]
  have hsplit : ∑' n : ℤ, g n = ∑' n : ℕ, a n + ∑' n : ℕ, b n := by
    have hgN : Summable (fun n : ℕ => g n) :=
      hg.comp_injective (fun x y h => by simpa using h)
    rw [tsum_of_nat_of_neg_add_one hgN ?_]
    · rw [hgN.tsum_eq_zero_add]
      simp only [Nat.cast_zero, hg0, zero_add, Nat.cast_add, Nat.cast_one]
      congr 1
      · exact tsum_congr hga
      · exact tsum_congr hgb
    · exact hsb.congr fun n => (hgb n).symm
  have := hsplit
  simp only [hgdef] at this
  rw [this, mul_add, ← tsum_mul_left, ← tsum_mul_left, ← (hsa.mul_left _).tsum_add (hsb.mul_left _)]
  refine tsum_congr fun n => ?_
  rw [hu, hv]; ring

