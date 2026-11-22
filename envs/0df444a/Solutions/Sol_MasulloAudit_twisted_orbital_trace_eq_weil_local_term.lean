-- Prove2me | solution 1 for MasulloAudit.twisted_orbital_trace_eq_weil_local_term
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:28:57.850658+00:00
-- url     : https://prove2.me/submissions/0393b630-7399-40af-8301-8d5135914059

import Mathlib

open Real Complex MeasureTheory Set
open scoped FourierTransform ContDiff

theorem poisson_aux (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hpos : tsupport φ ⊆ Set.Ioi 0) (p : ℝ) (hp : 1 < p) :
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
  refine ⟨hsum, ?_⟩
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
    (hsupp : tsupport φ ⊆ Set.Ioi 1) (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p - 1 / 2)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p - 1 / 2) =
      ∑' n : ℕ, ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) * φ (p ^ (n + 1)) := by
  set ψ : ℝ → ℂ := fun t => φ t * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hψdef
  have hzero : ∀ t, t ≤ 1 → φ t = 0 := by
    intro t ht
    by_contra hne
    have := hsupp (subset_tsupport _ hne)
    exact absurd (Set.mem_Ioi.mp this) (not_lt.mpr ht)
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hx0 : 0 < x := lt_trans one_pos (hsupp hx)
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
  have hψ_pos : tsupport ψ ⊆ Set.Ioi 0 :=
    hψ_sub.trans (hsupp.trans (Set.Ioi_subset_Ioi zero_le_one))
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
  obtain ⟨hS, hE⟩ := poisson_aux ψ hψ_smooth hψ_c hψ_pos p hp
  simp only [hmel] at hS hE
  refine ⟨hS, ?_⟩
  rw [hE]
  have hp0 : 0 < p := by linarith
  have hsuppZ : Function.support (fun n : ℤ => ψ (p ^ n)) ⊆
      Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    intro n hn
    by_contra hnot
    apply hn
    have hn0 : n ≤ 0 := by
      by_contra h
      push Not at h
      exact hnot ⟨(n - 1).toNat, by simp; omega⟩
    simp only [hψdef]
    rw [hzero _ (zpow_le_one_of_nonpos₀ hp.le hn0), zero_mul]
  have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    intro a b h; simpa using h
  rw [← hinj.tsum_eq hsuppZ, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [hψdef, zpow_natCast]
  have hpn : 0 < p ^ (n + 1) := pow_pos hp0 _
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hpn.le]
  push_cast
  ring
