-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_smoothedPoly_Iterm
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:03:05.089201+00:00
-- url     : https://prove2.me/submissions/53878377-80b7-4e3c-b61c-198c6aac5c76

import Mathlib
import Definitions.Def_GuthMaynard

section
namespace GuthMaynardS4

open Metric

noncomputable def bumpA : ContDiffBump (3 / 2 : ℝ) := ⟨3 / 10, 1 / 2, by norm_num, by norm_num⟩
noncomputable def bumpB : ContDiffBump (11 / 10 : ℝ) := ⟨1 / 20, 1 / 10, by norm_num, by norm_num⟩

/-- A weight with large mass near 1. -/
noncomputable def wC (x : ℝ) : ℝ := bumpA x + 10 * bumpB x

lemma wC_smooth : ContDiff ℝ (⊤ : ℕ∞) wC :=
  bumpA.contDiff.add (contDiff_const.mul bumpB.contDiff)

lemma wC_nonneg (x : ℝ) : 0 ≤ wC x := by
  unfold wC; have := bumpA.nonneg (x := x); have := bumpB.nonneg (x := x); positivity

lemma wC_supp : Function.support wC ⊆ Set.Icc 1 2 := by
  intro x hx
  by_contra hn
  apply hx
  have hA : bumpA x = 0 := by
    by_contra h
    have : x ∈ Function.support bumpA := h
    rw [bumpA.support_eq] at this
    simp only [bumpA, mem_ball, Real.dist_eq, abs_lt] at this
    exact hn ⟨by linarith [this.1], by linarith [this.2]⟩
  have hB : bumpB x = 0 := by
    by_contra h
    have : x ∈ Function.support bumpB := h
    rw [bumpB.support_eq] at this
    simp only [bumpB, mem_ball, Real.dist_eq, abs_lt] at this
    exact hn ⟨by linarith [this.1], by linarith [this.2]⟩
  simp [wC, hA, hB]

lemma wC_one (x : ℝ) (hx : x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5)) : wC x = 1 := by
  have hA : bumpA x = 1 := by
    apply bumpA.one_of_mem_closedBall
    simp only [bumpA, mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hB : bumpB x = 0 := by
    apply bumpB.zero_of_le_dist
    simp only [bumpB, Real.dist_eq]
    rw [le_abs]; left; linarith [hx.1]
  simp [wC, hA, hB]

theorem wC_isWeight : GuthMaynard.IsWeight wC :=
  ⟨wC_smooth, wC_nonneg, wC_supp, wC_one⟩

lemma wC_big (x : ℝ) (hx : x ∈ Set.Icc (21 / 20 : ℝ) (23 / 20)) : 10 ≤ wC x := by
  have hB : bumpB x = 1 := by
    apply bumpB.one_of_mem_closedBall
    simp only [bumpB, mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have := bumpA.nonneg (x := x)
  simp [wC, hB]; linarith

lemma wC_int_big : 10 ≤ ∫ x, wC x ^ 2 := by
  have hcont : Continuous wC := wC_smooth.continuous
  have hint : MeasureTheory.Integrable (fun x => wC x ^ 2) := by
    apply Continuous.integrable_of_hasCompactSupport (hcont.pow 2)
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1:ℝ)) (b := 2))
    intro x hx
    exact wC_supp (fun h => hx (by simp [h]))
  calc (10:ℝ) = ∫ x in Set.Icc (21 / 20 : ℝ) (23 / 20), (100:ℝ) := by
        simp; norm_num
    _ ≤ ∫ x in Set.Icc (21 / 20 : ℝ) (23 / 20), wC x ^ 2 := by
        apply MeasureTheory.setIntegral_mono_on (by simp) (hint.integrableOn) measurableSet_Icc
        intro x hx
        have := wC_big x hx
        nlinarith
    _ ≤ ∫ x, wC x ^ 2 :=
        MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => by positivity)

lemma wC_one_end : wC 1 = 0 := by
  have hA : bumpA 1 = 0 := by
    apply bumpA.zero_of_le_dist; simp [bumpA, Real.dist_eq]; rw [abs_of_neg (by norm_num)]; norm_num
  have hB : bumpB 1 = 0 := by
    apply bumpB.zero_of_le_dist; simp [bumpB, Real.dist_eq]; rw [abs_of_neg (by norm_num)]; norm_num
  simp [wC, hA, hB]

lemma wC_two_end : wC 2 = 0 := by
  have hA : bumpA 2 = 0 := by
    apply bumpA.zero_of_le_dist; simp [bumpA, Real.dist_eq]; rw [abs_of_pos (by norm_num)]; norm_num
  have hB : bumpB 2 = 0 := by
    apply bumpB.zero_of_le_dist; simp [bumpB, Real.dist_eq]; rw [abs_of_pos (by norm_num)]; norm_num
  simp [wC, hA, hB]

lemma wC_at (n : ℤ) : wC ((n : ℝ) / 2) = if n = 3 then 1 else 0 := by
  by_cases h3 : n = 3
  · subst h3
    simp only [if_true]
    apply wC_one; norm_num
  · rw [if_neg h3]
    by_contra hne
    obtain ⟨h1, h2⟩ := wC_supp (Function.mem_support.mpr hne)
    have hn1 : (2:ℤ) ≤ n := by
      have : (2:ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hn2 : n ≤ 4 := by
      have : (n:ℝ) ≤ 4 := by linarith
      exact_mod_cast this
    have : n = 2 ∨ n = 4 := by omega
    rcases this with rfl | rfl
    · apply hne; norm_num [wC_one_end]
    · apply hne; norm_num [wC_two_end]

end GuthMaynardS4
end

section
namespace GuthMaynardS4.PartBP

open Complex MeasureTheory FourierTransform

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
namespace GuthMaynardS4

open Complex

noncomputable def HH (k : ℤ) : ℂ := GuthMaynard.hHat wC 0 ((k : ℝ) * ((2 : ℕ) : ℝ))

lemma HH_summable_and_sum : Summable HH ∧ ∑' k, HH k = 1 / 2 := by
  obtain ⟨hs, he⟩ := PartBP.poisson_h wC wC_isWeight 0 2 (by norm_num)
  refine ⟨hs, ?_⟩
  have h1 : ∑' n : ℤ, (((wC ((n : ℝ) / ((2 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) *
      (((n : ℝ) / ((2 : ℕ) : ℝ) : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) * I)) = 1 := by
    rw [tsum_eq_single 3]
    · simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
      have := wC_at 3
      push_cast at this ⊢
      simp [this]
    · intro n hn
      simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
      have := wC_at n
      push_cast at this ⊢
      simp [this, hn]
  rw [h1] at he
  have : (((2 : ℕ) : ℂ)) * ∑' k, HH k = 1 := by simpa [HH] using he.symm
  simp at this
  field_simp
  linear_combination this

lemma HH_zero : HH 0 = ((∫ x, wC x ^ 2 : ℝ) : ℂ) := by
  simp only [HH, Int.cast_zero, zero_mul, GuthMaynard.hHat]
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
  simp only [one_mul]
  exact integral_ofReal


lemma Iterm_single (m : Fin 3 → ℤ) :
    GuthMaynard.Iterm wC 2 {0} m = 8 * (HH (m 0) * HH (m 1) * HH (m 2)) := by
  simp [GuthMaynard.Iterm, HH]
  norm_num

noncomputable def FF (m : Fin 3 → ℤ) : ℂ := 8 * (HH (m 0) * HH (m 1) * HH (m 2))

noncomputable def eqv : ℤ × ℤ × ℤ ≃ (Fin 3 → ℤ) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun m := (m 0, m 1, m 2)
  left_inv p := by simp
  right_inv m := by ext i; fin_cases i <;> simp

lemma FF_all : Summable FF ∧ ∑' m, FF m = 1 := by
  obtain ⟨hs, hsum⟩ := HH_summable_and_sum
  have hn : Summable (fun k => ‖HH k‖) := by
    exact (summable_norm_iff).mpr hs
  have hG : Summable (fun x : ℤ × ℤ => ‖HH x.1 * HH x.2‖) := hn.mul_norm hn
  have hG' : Summable (fun x : ℤ × ℤ => HH x.1 * HH x.2) := hG.of_norm
  have hGn : Summable (fun x : ℤ × ℤ => ‖HH x.1 * HH x.2‖) := hG
  have hP : Summable (fun x : ℤ × (ℤ × ℤ) => ‖HH x.1 * (HH x.2.1 * HH x.2.2)‖) := by
    have := hn.mul_norm (f := HH) (g := fun p : ℤ × ℤ => HH p.1 * HH p.2) hG
    simpa [norm_mul] using this
  have hP' : Summable (fun x : ℤ × (ℤ × ℤ) => HH x.1 * (HH x.2.1 * HH x.2.2)) := hP.of_norm
  have e1 : ∑' x : ℤ × ℤ, HH x.1 * HH x.2 = (1/2) * (1/2) := by
    rw [← tsum_mul_tsum_of_summable_norm hn hn, hsum]
  have e2 : ∑' x : ℤ × (ℤ × ℤ), HH x.1 * (HH x.2.1 * HH x.2.2) = (1/2) * ((1/2) * (1/2)) := by
    rw [← tsum_mul_tsum_of_summable_norm (f := HH) (g := fun p : ℤ × ℤ => HH p.1 * HH p.2) hn hG, hsum, e1]
  have hF : (FF ∘ eqv) = fun x : ℤ × (ℤ × ℤ) => 8 * (HH x.1 * (HH x.2.1 * HH x.2.2)) := by
    ext x; simp [FF, eqv, mul_assoc]
  have hsm : Summable (FF ∘ eqv) := by rw [hF]; exact hP'.mul_left 8
  refine ⟨(eqv.summable_iff).mp hsm, ?_⟩
  rw [← eqv.tsum_eq, ← Function.comp_def, hF, tsum_mul_left, e2]
  norm_num

lemma tsum_ne_zero_eq :
    ∑' m : {m : Fin 3 → ℤ // m ≠ 0}, GuthMaynard.Iterm wC 2 {0} m.1 =
      1 - 8 * (((∫ x, wC x ^ 2 : ℝ) : ℂ)) ^ 3 := by
  obtain ⟨hs, hsum⟩ := FF_all
  have h1 : ∀ m : {m : Fin 3 → ℤ // m ≠ 0}, GuthMaynard.Iterm wC 2 {0} m.1 = FF m.1 :=
    fun m => Iterm_single m.1
  simp_rw [h1]
  have h2 : ∑' m : {m : Fin 3 → ℤ // m ≠ 0}, FF m.1 =
      ∑' m : Fin 3 → ℤ, if m = 0 then 0 else FF m := by
    refine (tsum_subtype ({m : Fin 3 → ℤ | m ≠ 0}) FF).trans ?_
    congr 1; ext m
    by_cases h : m = 0 <;> simp [Set.indicator, h]
  rw [h2]
  have := hs.tsum_eq_add_tsum_ite 0
  rw [hsum] at this
  have hz : FF 0 = 8 * ((∫ x, wC x ^ 2 : ℝ) : ℂ) ^ 3 := by
    simp [FF, HH_zero]; ring
  rw [hz] at this
  linear_combination -this

end GuthMaynardS4
end

section
namespace GuthMaynardS4

open GuthMaynard

lemma D_val : smoothedPoly wC 2 (fun _ => 1) 0 = 1 := by
  have hI : Finset.Icc 2 (2 * 2) = ({2, 3, 4} : Finset ℕ) := by decide
  have h1 : wC 1 = 0 := wC_one_end
  have h2 : wC 2 = 0 := wC_two_end
  have h3 : wC (3 / 2) = 1 := wC_one _ (by norm_num)
  unfold smoothedPoly
  rw [hI]
  simp [Finset.sum_insert]
  norm_num [h1, h2, h3]

theorem disproof_dev : ¬ (∀ (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε),
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ),
      (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) → (∀ t ∈ W, (N : ℝ) ^ σ < ‖smoothedPoly w N b t‖) →
      let s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re
      (W.card : ℝ) ≤ C * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (1 - 2 * σ) * (Real.sign s * |s| ^ (1 / 3 : ℝ)))) := by
  intro H
  obtain ⟨C, hC⟩ := H wC wC_isWeight 1 one_pos
  have hN : ((2 : ℕ) : ℝ) ∈ Set.Icc ((2 : ℝ) ^ (3 / 4 : ℝ)) 2 := by
    refine ⟨?_, by norm_num⟩
    calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = ((2 : ℕ) : ℝ) := by norm_num
  have hsep : ∀ W : Finset ℝ, W.card ≤ 1 → IsSeparated ((2 : ℝ) ^ (1 : ℝ)) W := by
    intro W hW t ht t' ht' hne
    exfalso
    have := Finset.one_lt_card.mpr ⟨t, ht, t', ht', hne⟩
    omega
  -- C ≥ 0
  have hC0 : 0 ≤ C := by
    have := hC 2 2 hN (-1) (fun _ => 1) (fun _ => by simp) ∅ 0 (hsep _ (by simp)) (by simp) (by simp)
    simp only [Finset.card_empty, Nat.cast_zero] at this
    have hs : (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm wC 2 ∅ m).re = 0 := by
      simp [Iterm]
    simp only [hs] at this
    simp at this
    have e : (2:ℝ) ^ ((2:ℝ) + 2) = 16 := by
      norm_num [show ((2:ℝ) + 2) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at this
    linarith
  -- the counterexample
  have h := hC 2 2 hN (-1) (fun _ => 1) (fun _ => by simp) {0} 0 (hsep _ (by simp)) (by simp)
    (by
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [D_val]
      simp only [norm_one, Nat.cast_ofNat]
      have : (2:ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
      rw [this]; norm_num)
  simp only [Finset.card_singleton, Nat.cast_one] at h
  rw [tsum_ne_zero_eq] at h
  set c : ℝ := ∫ x, wC x ^ 2 with hc
  have hc10 : 10 ≤ c := wC_int_big
  have hre : ((1 : ℂ) - 8 * (c : ℂ) ^ 3).re = 1 - 8 * c ^ 3 := by
    have : ((1 : ℂ) - 8 * (c : ℂ) ^ 3) = ((1 - 8 * c ^ 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  simp only [hre] at h
  set s : ℝ := 1 - 8 * c ^ 3 with hs
  have hc3 : 1000 ≤ c ^ 3 := by nlinarith [sq_nonneg c]
  have hsneg : s < 0 := by rw [hs]; linarith
  have hsign : Real.sign s = -1 := Real.sign_of_neg hsneg
  have habs : |s| = 8 * c ^ 3 - 1 := by rw [abs_of_neg hsneg, hs]; ring
  have hcube : (2 : ℝ) < |s| ^ (1 / 3 : ℝ) := by
    have : (8 : ℝ) < |s| := by rw [habs]; linarith
    calc (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := by
          rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      _ < |s| ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by norm_num) this (by norm_num)
  rw [hsign] at h
  have e1 : ((2 : ℕ) : ℝ) ^ (2 - 2 * (-1 : ℝ)) = 16 := by norm_num [show (2 - 2 * (-1 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : ((2 : ℕ) : ℝ) ^ (1 - 2 * (-1 : ℝ)) = 8 := by norm_num [show (1 - 2 * (-1 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e1, e2] at h
  nlinarith

end GuthMaynardS4
end

theorem solution : type_of% GuthMaynardS4.disproof_dev := GuthMaynardS4.disproof_dev
