-- Prove2me | solution 1 for MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/39747be8-6fb9-5898-9afc-efbef95ebbab

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log

set_option autoImplicit false

open MeasureTheory Set

namespace K2Core

lemma norm_le_iff (p : ℝ × ℝ) (a : ℝ) : ‖p‖ ≤ a ↔ |p.1| ≤ a ∧ |p.2| ≤ a := by
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]

lemma abs_fst_le (p : ℝ × ℝ) : |p.1| ≤ ‖p‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _

lemma abs_snd_le (p : ℝ × ℝ) : |p.2| ≤ ‖p‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _

lemma sq_add_sq_le (p : ℝ × ℝ) : p.1 ^ 2 + p.2 ^ 2 ≤ 2 * ‖p‖ ^ 2 := by
  have h1 : p.1 ^ 2 ≤ ‖p‖ ^ 2 := by
    have := abs_fst_le p
    calc p.1 ^ 2 = |p.1| ^ 2 := (sq_abs _).symm
      _ ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : p.2 ^ 2 ≤ ‖p‖ ^ 2 := by
    have := abs_snd_le p
    calc p.2 ^ 2 = |p.2| ^ 2 := (sq_abs _).symm
      _ ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  linarith

lemma norm_sq_le (p : ℝ × ℝ) : ‖p‖ ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |p.1| |p.2| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg p.1]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg p.2]

lemma setOf_norm_le (a : ℝ) : {p : ℝ × ℝ | ‖p‖ ≤ a} = Icc (-a) a ×ˢ Icc (-a) a := by
  ext p
  simp only [mem_setOf_eq, mem_prod, mem_Icc, norm_le_iff, abs_le]

lemma volume_real_norm_le (a : ℝ) (ha : 0 ≤ a) :
    (volume : Measure (ℝ × ℝ)).real {p : ℝ × ℝ | ‖p‖ ≤ a} = (2 * a) ^ 2 := by
  rw [setOf_norm_le, Measure.volume_eq_prod, measureReal_def, Measure.prod_prod, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  ring

lemma measurableSet_norm_le (a : ℝ) : MeasurableSet {p : ℝ × ℝ | ‖p‖ ≤ a} := by
  rw [setOf_norm_le]; exact measurableSet_Icc.prod measurableSet_Icc

lemma integral_indicator_norm_le (a c : ℝ) (ha : 0 ≤ a) :
    ∫ p : ℝ × ℝ, {p : ℝ × ℝ | ‖p‖ ≤ a}.indicator (fun _ => c) p = c * (2 * a) ^ 2 := by
  rw [integral_indicator_const _ (measurableSet_norm_le a), smul_eq_mul, volume_real_norm_le a ha]
  ring

lemma integrable_indicator_norm_le (a c : ℝ) :
    Integrable ({p : ℝ × ℝ | ‖p‖ ≤ a}.indicator (fun _ => c)) (volume : Measure (ℝ × ℝ)) := by
  apply (integrableOn_const ?_).integrable_indicator (measurableSet_norm_le a)
  rw [setOf_norm_le, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp) (by simp)

noncomputable def g1 (δ R : ℝ) (t : ℝ) : ℝ :=
  (Icc (-R) R).indicator (fun t => max |t| δ ^ (-(5 / 4 : ℝ))) t

lemma g1_nonneg (δ R t : ℝ) (hδ : 0 < δ) : 0 ≤ g1 δ R t := by
  unfold g1
  apply indicator_nonneg
  intro s _
  exact Real.rpow_nonneg (le_trans hδ.le (le_max_right _ _)) _

lemma continuous_maxrpow (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun t : ℝ => max |t| δ ^ (-(5 / 4 : ℝ))) := by
  apply Continuous.rpow_const (continuous_abs.max continuous_const)
  intro t
  left
  exact (lt_of_lt_of_le hδ (le_max_right _ _)).ne'

lemma integrable_g1 (δ R : ℝ) (hδ : 0 < δ) : Integrable (g1 δ R) := by
  unfold g1
  exact ((continuous_maxrpow δ hδ).continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
    measurableSet_Icc

lemma integral_g1_le (δ R : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t, g1 δ R t ≤ 10 * δ ^ (-(1 / 4 : ℝ)) := by

  set R' := max R δ with hR'
  have hδR : δ ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := lt_of_lt_of_le hδ hδR
  have hmono : ∀ t, g1 δ R t ≤ g1 δ R' t := by
    intro t
    unfold g1
    apply indicator_le_indicator_of_subset (Icc_subset_Icc (by simp [hR']) (le_max_left _ _))
    intro s
    exact Real.rpow_nonneg (le_trans hδ.le (le_max_right _ _)) _
  have step1 : ∫ t, g1 δ R t ≤ ∫ t, g1 δ R' t :=
    integral_mono (integrable_g1 δ R hδ) (integrable_g1 δ R' hδ) hmono
  refine step1.trans ?_

  have hcont := continuous_maxrpow δ hδ
  have heq : ∫ t, g1 δ R' t = ∫ t in (-R')..R', max |t| δ ^ (-(5 / 4 : ℝ)) := by
    unfold g1
    rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc]
  rw [heq]
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => max |t| δ ^ (-(5 / 4 : ℝ))) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-R') (-δ)) (hii (-δ) R'),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (-δ) δ) (hii δ R')]

  have hmid : ∫ t in (-δ)..δ, max |t| δ ^ (-(5 / 4 : ℝ)) = 2 * δ * δ ^ (-(5 / 4 : ℝ)) := by
    have : ∀ t ∈ uIcc (-δ) δ, max |t| δ ^ (-(5 / 4 : ℝ)) = δ ^ (-(5 / 4 : ℝ)) := by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      have : |t| ≤ δ := abs_le.2 ⟨ht.1, ht.2⟩
      rw [max_eq_right this]
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const, smul_eq_mul]
    ring

  have hright : ∫ t in δ..R', max |t| δ ^ (-(5 / 4 : ℝ)) ≤ 4 * δ ^ (-(1 / 4 : ℝ)) := by
    have : ∀ t ∈ uIcc δ R', max |t| δ ^ (-(5 / 4 : ℝ)) = t ^ (-(5 / 4 : ℝ)) := by
      intro t ht
      rw [uIcc_of_le hδR] at ht
      have ht0 : 0 ≤ t := le_trans hδ.le ht.1
      rw [abs_of_nonneg ht0, max_eq_left ht.1]
    rw [intervalIntegral.integral_congr this, integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · have h1 : (-(5 / 4 : ℝ)) + 1 = -(1 / 4 : ℝ) := by norm_num
      rw [h1]
      have hRpos : 0 ≤ R' ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hR'0.le _
      have : (R' ^ (-(1 / 4 : ℝ)) - δ ^ (-(1 / 4 : ℝ))) / (-(1 / 4 : ℝ)) =
          4 * δ ^ (-(1 / 4 : ℝ)) - 4 * R' ^ (-(1 / 4 : ℝ)) := by ring
      rw [this]
      linarith
    · rw [uIcc_of_le hδR]
      intro h
      exact absurd h.1 (not_le.2 hδ)

  have hleft : ∫ t in (-R')..(-δ), max |t| δ ^ (-(5 / 4 : ℝ)) =
      ∫ t in δ..R', max |t| δ ^ (-(5 / 4 : ℝ)) := by
    have := intervalIntegral.integral_comp_neg (a := δ) (b := R')
      (f := fun t : ℝ => max |t| δ ^ (-(5 / 4 : ℝ)))
    simp only [abs_neg] at this
    exact this.symm
  rw [hleft, hmid]
  have hδpow : 2 * δ * δ ^ (-(5 / 4 : ℝ)) = 2 * δ ^ (-(1 / 4 : ℝ)) := by
    have : δ * δ ^ (-(5 / 4 : ℝ)) = δ ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_one_add' hδ.le (by norm_num)]
      norm_num
    calc 2 * δ * δ ^ (-(5 / 4 : ℝ)) = 2 * (δ * δ ^ (-(5 / 4 : ℝ))) := by ring
      _ = 2 * δ ^ (-(1 / 4 : ℝ)) := by rw [this]
  rw [hδpow]
  linarith

lemma rpow_norm_le_g1_mul_g1 (δ R : ℝ) (hδ : 0 < δ) (p : ℝ × ℝ) (hp1 : δ ≤ ‖p‖) (hp2 : ‖p‖ ≤ R) :
    ‖p‖ ^ (-(5 / 2 : ℝ)) ≤ g1 δ R p.1 * g1 δ R p.2 := by
  have hp0 : 0 < ‖p‖ := lt_of_lt_of_le hδ hp1
  have hx : p.1 ∈ Icc (-R) R := by
    have := (abs_fst_le p).trans hp2
    exact ⟨(abs_le.1 this).1, (abs_le.1 this).2⟩
  have hy : p.2 ∈ Icc (-R) R := by
    have := (abs_snd_le p).trans hp2
    exact ⟨(abs_le.1 this).1, (abs_le.1 this).2⟩
  unfold g1
  rw [indicator_of_mem hx, indicator_of_mem hy]
  have hmx : max |p.1| δ ≤ ‖p‖ := max_le (abs_fst_le p) hp1
  have hmy : max |p.2| δ ≤ ‖p‖ := max_le (abs_snd_le p) hp1
  have hmx0 : 0 < max |p.1| δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hmy0 : 0 < max |p.2| δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have e1 : ‖p‖ ^ (-(5 / 4 : ℝ)) ≤ max |p.1| δ ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hmx0 hmx (by norm_num)
  have e2 : ‖p‖ ^ (-(5 / 4 : ℝ)) ≤ max |p.2| δ ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hmy0 hmy (by norm_num)
  have hsplit : ‖p‖ ^ (-(5 / 2 : ℝ)) = ‖p‖ ^ (-(5 / 4 : ℝ)) * ‖p‖ ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hp0]; norm_num
  rw [hsplit]
  exact mul_le_mul e1 e2 (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hmx0.le _)

lemma integrable_g1_prod (δ R : ℝ) (hδ : 0 < δ) :
    Integrable (fun p : ℝ × ℝ => g1 δ R p.1 * g1 δ R p.2) (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact (integrable_g1 δ R hδ).mul_prod (integrable_g1 δ R hδ)

lemma integral_g1_prod_le (δ R : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ p : ℝ × ℝ, g1 δ R p.1 * g1 δ R p.2 ≤ 100 * δ ^ (-(1 / 2 : ℝ)) := by
  rw [Measure.volume_eq_prod, integral_prod_mul]
  have h := integral_g1_le δ R hδ hδ1
  have h0 : 0 ≤ ∫ t, g1 δ R t := integral_nonneg (fun t => g1_nonneg δ R t hδ)
  have hsq : δ ^ (-(1 / 4 : ℝ)) * δ ^ (-(1 / 4 : ℝ)) = δ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hδ]; norm_num
  calc (∫ t, g1 δ R t) * (∫ t, g1 δ R t) ≤ (10 * δ ^ (-(1 / 4 : ℝ))) * (10 * δ ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul h h h0 (by positivity)
    _ = 100 * δ ^ (-(1 / 2 : ℝ)) := by rw [← hsq]; ring

noncomputable def φ (t : ℝ) : ℝ := Real.smoothTransition ((4 - t) / 3)

lemma φ_contDiff : ContDiff ℝ (⊤ : ℕ∞) φ := by
  unfold φ
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)

lemma φ_of_le_one {t : ℝ} (ht : t ≤ 1) : φ t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]; linarith)

lemma φ_of_four_le {t : ℝ} (ht : 4 ≤ t) : φ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; constructor <;> linarith)

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := Real.smoothTransition.nonneg _
lemma φ_le_one (t : ℝ) : φ t ≤ 1 := Real.smoothTransition.le_one _

noncomputable def χ₁ (p : ℝ × ℝ) : ℝ := φ (p.1 ^ 2 + p.2 ^ 2)

lemma χ₁_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ₁ := by
  unfold χ₁
  exact φ_contDiff.comp (by fun_prop)

lemma χ₁_eq_one {p : ℝ × ℝ} (h : ‖p‖ ≤ 1 / 2) : χ₁ p = 1 := by
  unfold χ₁
  apply φ_of_le_one
  have := sq_add_sq_le p
  nlinarith [norm_nonneg p]

lemma χ₁_eq_zero {p : ℝ × ℝ} (h : 2 ≤ ‖p‖) : χ₁ p = 0 := by
  unfold χ₁
  apply φ_of_four_le
  have := norm_sq_le p
  nlinarith

lemma χ₁_nonneg (p : ℝ × ℝ) : 0 ≤ χ₁ p := φ_nonneg _
lemma χ₁_le_one (p : ℝ × ℝ) : χ₁ p ≤ 1 := φ_le_one _

lemma χ₁_hasCompactSupport : HasCompactSupport χ₁ := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ × ℝ) 2) (isCompact_closedBall _ _)
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hp
  exact χ₁_eq_zero hp.le

lemma exists_bound_χ₁ : ∃ M : ℝ, 1 ≤ M ∧ ∀ k : ℕ, k ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k χ₁ p‖ ≤ M := by
  have hb : ∀ k : ℕ, ∃ C, ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k χ₁ p‖ ≤ C := by
    intro k
    exact (χ₁_hasCompactSupport.iteratedFDeriv k).exists_bound_of_continuous
      (χ₁_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose C hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range 5, |C k|,
    by linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range 5) => abs_nonneg (C j))],
    fun k hk p => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ k χ₁ p‖ ≤ |C k| := (hC k p).trans (le_abs_self _)
  have h2 : |C k| ≤ ∑ j ∈ Finset.range 5, |C j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_range.2 (by omega))
  linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range 5) => abs_nonneg (C j))]

noncomputable def scale (t : ℝ) (ht : t ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (t • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (t⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (fun p => by
      simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        smul_smul, inv_mul_cancel₀ ht, one_smul])
    (fun p => by
      simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        smul_smul, mul_inv_cancel₀ ht, one_smul])

@[scoped simp] lemma scale_apply (t : ℝ) (ht : t ≠ 0) (p : ℝ × ℝ) : scale t ht p = t • p := rfl

lemma compContinuousLinearMap_scale {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℝ)
    (t : ℝ) (ht : t ≠ 0) :
    M.compContinuousLinearMap (fun _ => ((scale t ht : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
      = (t ^ n) • M := by
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    scale_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

noncomputable def χ (ε : ℝ) (p : ℝ × ℝ) : ℝ := χ₁ (ε⁻¹ • p)

lemma χ_contDiff (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (χ ε) := by
  unfold χ
  exact χ₁_contDiff.comp (contDiff_id.const_smul ε⁻¹)

lemma norm_smul_inv (ε : ℝ) (hε : 0 < ε) (p : ℝ × ℝ) : ‖ε⁻¹ • p‖ = ε⁻¹ * ‖p‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]

lemma χ_eq_one {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (h : ‖p‖ ≤ ε / 2) : χ ε p = 1 := by
  unfold χ
  apply χ₁_eq_one
  rw [norm_smul_inv ε hε, inv_mul_le_iff₀ hε]
  linarith

lemma χ_eq_zero {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (h : 2 * ε ≤ ‖p‖) : χ ε p = 0 := by
  unfold χ
  apply χ₁_eq_zero
  rw [norm_smul_inv ε hε, le_inv_mul_iff₀ hε]
  linarith

lemma χ_nonneg (ε : ℝ) (p : ℝ × ℝ) : 0 ≤ χ ε p := χ₁_nonneg _
lemma χ_le_one (ε : ℝ) (p : ℝ × ℝ) : χ ε p ≤ 1 := χ₁_le_one _

lemma norm_iteratedFDeriv_χ (ε : ℝ) (hε : 0 < ε) (k : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (χ ε) p‖ = ε⁻¹ ^ k * ‖iteratedFDeriv ℝ k χ₁ (ε⁻¹ • p)‖ := by
  have hε0 : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hcomp := (scale ε⁻¹ hε0).iteratedFDerivWithin_comp_right χ₁ uniqueDiffOn_univ
    (x := p) (Set.mem_univ _) k
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hcomp
  rw [compContinuousLinearMap_scale] at hcomp
  have hfun : (χ₁ ∘ (scale ε⁻¹ hε0)) = χ ε := by
    funext q; rfl
  rw [hfun] at hcomp
  rw [hcomp, norm_smul, scale_apply, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.2 hε.le) k)]

lemma iteratedFDeriv_χ_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) {p : ℝ × ℝ}
    (h : ‖p‖ < ε / 2) : iteratedFDeriv ℝ k (χ ε) p = 0 := by
  have hopen : IsOpen {q : ℝ × ℝ | ‖q‖ < ε / 2} := isOpen_lt continuous_norm continuous_const
  have hev : χ ε =ᶠ[nhds p] (fun _ => (1 : ℝ)) := by
    filter_upwards [hopen.mem_nhds h] with q hq
    exact χ_eq_one hε hq.le
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
  rfl

lemma iteratedFDeriv_χ_eq_zero_of_gt {ε : ℝ} (hε : 0 < ε) (k : ℕ) {p : ℝ × ℝ}
    (h : 2 * ε < ‖p‖) : iteratedFDeriv ℝ k (χ ε) p = 0 := by
  have hopen : IsOpen {q : ℝ × ℝ | 2 * ε < ‖q‖} := isOpen_lt continuous_const continuous_norm
  have hev : χ ε =ᶠ[nhds p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds h] with q hq
    exact χ_eq_zero hε hq.le
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

lemma sqrt_mul_one_add_abs_log_le (r t : ℝ) (ht : 0 < t) (htr : t ≤ r) :
    Real.sqrt t * (1 + |Real.log t|) ≤ 3 + (1 + r) ^ 2 := by
  have hr : 0 < r := lt_of_lt_of_le ht htr
  rcases le_or_gt t 1 with h1 | h1
  ·
    have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr h1 |>.trans_eq' rfl |> fun h => by
      simpa using Real.sqrt_le_sqrt h1
    have hlog : |Real.log t * t ^ (1 / 2 : ℝ)| < 1 / (1 / 2 : ℝ) :=
      Real.abs_log_mul_self_rpow_lt t (1 / 2) ht h1 (by norm_num)
    rw [← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hlog
    have : Real.sqrt t * (1 + |Real.log t|) = Real.sqrt t + |Real.log t| * Real.sqrt t := by ring
    rw [this]
    nlinarith [sq_nonneg (1 + r), Real.sqrt_nonneg t]
  ·
    have hlt : 0 ≤ Real.log t := Real.log_nonneg h1.le
    rw [abs_of_nonneg hlt]
    have hlogr : Real.log t ≤ r := (Real.log_le_self ht.le).trans htr
    have hsr : Real.sqrt t ≤ 1 + r := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    calc Real.sqrt t * (1 + Real.log t) ≤ (1 + r) * (1 + r) :=
          mul_le_mul hsr (by linarith) (by positivity) (by linarith)
      _ = (1 + r) ^ 2 := by ring
      _ ≤ 3 + (1 + r) ^ 2 := by linarith

noncomputable def ch (c t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)))

lemma norm_ch (c t : ℝ) : ‖ch c t‖ = 1 := by
  unfold ch; rw [Complex.norm_exp]; simp

lemma hasDerivAt_ch (c t : ℝ) : HasDerivAt (ch c) (-(2 * Real.pi * Complex.I * c) * ch c t) t := by
  unfold ch
  have h1 : HasDerivAt (fun t : ℝ => (((c * t : ℝ)) : ℂ)) (c : ℂ) t := by
    have : HasDerivAt (fun t : ℝ => c * t) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    exact this.ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => -(2 * Real.pi * Complex.I * (((c * t : ℝ)) : ℂ)))
      (-(2 * Real.pi * Complex.I * c)) t := (h1.const_mul _).neg
  convert h2.cexp using 1
  ring

lemma continuous_ch (c : ℝ) : Continuous (ch c) := by
  unfold ch; fun_prop

lemma kernel_eq (ξ η x y : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + η * y : ℝ) : ℂ))) = ch ξ x * ch η y := by
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
  exact (continuous_eval_const w).comp (hF.continuous_iteratedFDeriv (by exact_mod_cast hn))

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
    unfold D; exact hd.continuousMultilinear_apply_const w
  refine ⟨hdD.hasFDerivAt, fun v => ?_⟩
  unfold D
  rw [fderiv_continuousMultilinear_apply_const_apply hd w v, iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]

lemma hasDerivAt_D_x (hF : ContDiff ℝ 4 F) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) (x y : ℝ) :
    HasDerivAt (fun x => D w F (x, y)) (D (Fin.cons ((1 : ℝ), (0 : ℝ)) w) F (x, y)) x := by
  obtain ⟨h1, h2⟩ := hasFDerivAt_D hF hn w (x, y)
  have hc : HasDerivAt (fun x : ℝ => (x, y)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have := h1.comp_hasDerivAt x hc
  rwa [h2] at this

lemma hasDerivAt_D_y (hF : ContDiff ℝ 4 F) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) (x y : ℝ) :
    HasDerivAt (fun y => D w F (x, y)) (D (Fin.cons ((0 : ℝ), (1 : ℝ)) w) F (x, y)) y := by
  obtain ⟨h1, h2⟩ := hasFDerivAt_D hF hn w (x, y)
  have hc : HasDerivAt (fun y : ℝ => (x, y)) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have := h1.comp_hasDerivAt y hc
  rwa [h2] at this

lemma D_eq_zero_of_eventuallyEq {n : ℕ} (w : Fin n → ℝ × ℝ) (p : ℝ × ℝ)
    (h : F =ᶠ[nhds p] fun _ => 0) : D w F p = 0 := by
  unfold D
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
  simp

lemma D_eq_zero_of_norm (r : ℝ) (hsupp : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → F p = 0) {n : ℕ}
    (w : Fin n → ℝ × ℝ) (p : ℝ × ℝ) (hp : r < ‖p‖) : D w F p = 0 := by
  apply D_eq_zero_of_eventuallyEq
  have hopen : IsOpen {q : ℝ × ℝ | r < ‖q‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hp] with q hq
  exact hsupp q hq.le

lemma D_eq_zero_fst (r : ℝ) (hsupp : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → F p = 0) {n : ℕ}
    (w : Fin n → ℝ × ℝ) (p : ℝ × ℝ) (hp : r < |p.1|) : D w F p = 0 :=
  D_eq_zero_of_norm r hsupp w p (lt_of_lt_of_le hp (abs_fst_le p))

lemma D_eq_zero_snd (r : ℝ) (hsupp : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → F p = 0) {n : ℕ}
    (w : Fin n → ℝ × ℝ) (p : ℝ × ℝ) (hp : r < |p.2|) : D w F p = 0 :=
  D_eq_zero_of_norm r hsupp w p (lt_of_lt_of_le hp (abs_snd_le p))

lemma ibp_line (R : ℝ) (ξ : ℝ) (v v' : ℝ → ℂ) (hv : ∀ x, HasDerivAt v (v' x) x)
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
  have hcs : ∀ g : ℝ → ℂ, (∀ x, R < |x| → g x = 0) → HasCompactSupport g := fun g hg =>
    HasCompactSupport.intro hK (fun x hx => hg x (hout x hx))
  have hint : ∀ g : ℝ → ℂ, Continuous g → (∀ x, R < |x| → g x = 0) →
      Integrable (fun x => ch ξ x * g x) := fun g hg hg0 =>
    Continuous.integrable_of_hasCompactSupport ((continuous_ch ξ).mul hg) (hcs g hg0).mul_left
  have hint' : Integrable (fun x => (-(2 * Real.pi * Complex.I * ξ) * ch ξ x) * v x) := by
    have := (hint v hvc hv0).const_mul (-(2 * Real.pi * Complex.I * ξ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := ch ξ) (v := v)
    (u' := fun t => -(2 * Real.pi * Complex.I * ξ) * ch ξ t) (v' := v')
    (fun x _ => hasDerivAt_ch ξ x) (fun x _ => hv x) (hint v' hv'c hv'0) hint' (hint v hvc hv0)
  rw [h, ← integral_neg, ← integral_const_mul]
  congr 1; funext x; ring

noncomputable def J2 (ξ η : ℝ) {n : ℕ} (w : Fin n → ℝ × ℝ) (F : ℝ × ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ, ch ξ x * ch η y * D w F (x, y)

section rules

variable (r : ℝ) (hF : ContDiff ℝ 4 F) (hsupp : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → F p = 0)

lemma hasCompactSupport_of_norm (G : ℝ × ℝ → ℂ) (hG : ∀ p : ℝ × ℝ, r < ‖p‖ → G p = 0) :
    HasCompactSupport G := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ × ℝ) |r|) (isCompact_closedBall _ _)
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hp
  exact hG p (lt_of_le_of_lt (le_abs_self r) hp)

include hF hsupp in
lemma integrable_word (ξ η : ℝ) {n : ℕ} (hn : n ≤ 4) (w : Fin n → ℝ × ℝ) :
    Integrable (fun p : ℝ × ℝ => ch ξ p.1 * ch η p.2 * D w F p) (volume : Measure (ℝ × ℝ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (((continuous_ch ξ).comp continuous_fst).mul ((continuous_ch η).comp continuous_snd)).mul
      (continuous_D hF hn w)
  · apply hasCompactSupport_of_norm r
    intro p hp
    rw [D_eq_zero_of_norm r hsupp w p hp, mul_zero]

include hF hsupp in
lemma J2_eq_integral (ξ η : ℝ) {n : ℕ} (hn : n ≤ 4) (w : Fin n → ℝ × ℝ) :
    J2 ξ η w F = ∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * D w F p := by
  unfold J2
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_word r hF hsupp ξ η hn w
    rwa [Measure.volume_eq_prod] at this)]

include hF hsupp in

lemma rule_y (ξ η : ℝ) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) :
    (2 * Real.pi * Complex.I * η) * J2 ξ η w F = J2 ξ η (Fin.cons ((0 : ℝ), (1 : ℝ)) w) F := by
  unfold J2
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have h1 : ∀ (k : ℕ) (u : Fin k → ℝ × ℝ), (fun y => ch ξ x * ch η y * D u F (x, y)) =
      fun y => ch ξ x * (ch η y * D u F (x, y)) := by
    intro k u; funext y; ring
  rw [h1, h1, integral_const_mul, integral_const_mul]
  have := ibp_line r η (fun y => D w F (x, y)) (fun y => D (Fin.cons ((0 : ℝ), (1 : ℝ)) w) F (x, y))
    (fun y => hasDerivAt_D_y hF hn w x y)
    ((continuous_D hF hn.le _).comp (Continuous.prodMk_right x))
    ((continuous_D hF (by omega) _).comp (Continuous.prodMk_right x))
    (fun y hy => D_eq_zero_snd r hsupp w (x, y) hy)
    (fun y hy => D_eq_zero_snd r hsupp _ (x, y) hy)
  rw [this]; ring

include hF hsupp in

lemma rule_x (ξ η : ℝ) {n : ℕ} (hn : n < 4) (w : Fin n → ℝ × ℝ) :
    (2 * Real.pi * Complex.I * ξ) * J2 ξ η w F = J2 ξ η (Fin.cons ((1 : ℝ), (0 : ℝ)) w) F := by
  unfold J2
  have hI : ∀ (k : ℕ) (hk : k ≤ 4) (u : Fin k → ℝ × ℝ),
      Integrable (Function.uncurry fun x y => ch ξ x * ch η y * D u F (x, y))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    intro k hk u
    have := integrable_word r hF hsupp ξ η hk u
    rw [Measure.volume_eq_prod] at this
    exact this
  rw [integral_integral_swap (hI n hn.le w), integral_integral_swap (hI (n + 1) (by omega) _),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have h1 : ∀ (k : ℕ) (u : Fin k → ℝ × ℝ), (fun x => ch ξ x * ch η y * D u F (x, y)) =
      fun x => ch η y * (ch ξ x * D u F (x, y)) := by
    intro k u; funext x; ring
  rw [h1, h1, integral_const_mul, integral_const_mul]
  have := ibp_line r ξ (fun x => D w F (x, y)) (fun x => D (Fin.cons ((1 : ℝ), (0 : ℝ)) w) F (x, y))
    (fun x => hasDerivAt_D_x hF hn w x y)
    ((continuous_D hF hn.le _).comp (Continuous.prodMk_left y))
    ((continuous_D hF (by omega) _).comp (Continuous.prodMk_left y))
    (fun x hx => D_eq_zero_fst r hsupp w (x, y) hx)
    (fun x hx => D_eq_zero_fst r hsupp _ (x, y) hx)
  rw [this]; ring

include hF hsupp in

lemma norm_J2_le (ξ η : ℝ) {n : ℕ} (hn : n ≤ 4) (w : Fin n → ℝ × ℝ) (hw : ∀ i, ‖w i‖ ≤ 1)
    (Φ : ℝ × ℝ → ℝ) (hΦ : Integrable Φ (volume : Measure (ℝ × ℝ)))
    (hle : ∀ᵐ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ Φ p) :
    ‖J2 ξ η w F‖ ≤ ∫ p : ℝ × ℝ, Φ p := by
  rw [J2_eq_integral r hF hsupp ξ η hn w]
  apply norm_integral_le_of_norm_le hΦ
  filter_upwards [hle] with p hp
  rw [norm_mul, norm_mul, norm_ch, norm_ch, one_mul, one_mul]
  exact (norm_D_le F w hw p).trans hp

end rules

section far

variable (r ε A B K M : ℝ) (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ)

noncomputable def gfar (ε : ℝ) (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := G p * (1 - χ ε p)

noncomputable def ffar (ε : ℝ) (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((gfar ε G p : ℝ) : ℂ) * H p

lemma isOpen_U : IsOpen {p : ℝ × ℝ | p ≠ 0} := isOpen_ne

variable {ε G}

lemma gfar_eventuallyEq_zero (hε : 0 < ε) (p : ℝ × ℝ) (hp : ‖p‖ < ε / 2) :
    gfar ε G =ᶠ[nhds p] fun _ => 0 := by
  have hopen : IsOpen {q : ℝ × ℝ | ‖q‖ < ε / 2} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hp] with q hq
  simp [gfar, χ_eq_one hε hq.le]

lemma contDiff_gfar (hε : 0 < ε) (hG : ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0}) :
    ContDiff ℝ 4 (gfar ε G) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p = 0
  · subst hp
    have h : gfar ε G =ᶠ[nhds (0 : ℝ × ℝ)] fun _ => 0 :=
      gfar_eventuallyEq_zero hε 0 (by simp [hε])
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h
  · have hGp : ContDiffAt ℝ 4 G p := hG.contDiffAt (isOpen_U.mem_nhds hp)
    have hχ : ContDiffAt ℝ 4 (fun q => 1 - χ ε q) p :=
      (contDiff_const.sub ((χ_contDiff ε).of_le
        (WithTop.coe_le_coe.mpr le_top))).contDiffAt
    exact hGp.mul hχ

lemma contDiff_ffar (hε : 0 < ε) (hG : ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0}) {H : ℝ × ℝ → ℂ}
    (hH : ContDiff ℝ 4 H) : ContDiff ℝ 4 (ffar ε G H) := by
  unfold ffar
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_gfar hε hG)).mul hH

lemma ffar_eq_zero {H : ℝ × ℝ → ℂ} (hH0 : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0) (p : ℝ × ℝ)
    (hp : r ≤ ‖p‖) : ffar ε G H p = 0 := by
  simp [ffar, hH0 p hp]

lemma ffar_eventuallyEq_zero (hε : 0 < ε) (H : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (hp : ‖p‖ < ε / 2) :
    ffar ε G H =ᶠ[nhds p] fun _ => 0 := by
  filter_upwards [gfar_eventuallyEq_zero (G := G) hε p hp] with q hq
  simp [ffar, hq]

lemma norm_iteratedFDeriv_one_sub_χ (hε : 0 < ε) {l : ℕ} (hl : 1 ≤ l) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ l (fun q => 1 - χ ε q) p‖ = ‖iteratedFDeriv ℝ l (χ ε) p‖ := by
  have h1 : ContDiffAt ℝ l (fun _ : ℝ × ℝ => (1 : ℝ)) p := contDiffAt_const
  have h2 : ContDiffAt ℝ l (χ ε) p :=
    ((χ_contDiff ε).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have : (fun q => 1 - χ ε q) = (fun _ => (1 : ℝ)) - χ ε := by funext q; rfl
  rw [this, iteratedFDeriv_sub_apply h1 h2, iteratedFDeriv_const_of_ne (by omega)]
  simp

end far

section bounds

variable {r ε A B K M : ℝ} {G : ℝ × ℝ → ℝ} {H : ℝ × ℝ → ℂ}

lemma rpow_neg_five_halves (t : ℝ) (ht : 0 < t) : t ^ (-(5 / 2 : ℝ)) = Real.sqrt t / t ^ 3 := by
  rw [eq_div_iff (pow_pos ht 3).ne', Real.sqrt_eq_rpow, ← Real.rpow_natCast t 3,
    ← Real.rpow_add ht]
  norm_num

lemma G_bound_sqrt (hA : 0 ≤ A)
    (hGb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
      ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|))
    (n : ℕ) (hn : n ≤ 4) (p : ℝ × ℝ) (hp : p ≠ 0) (hpr : ‖p‖ ≤ r) :
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * (3 + (1 + r) ^ 2) * (‖p‖ * Real.sqrt ‖p‖) := by
  have ht : 0 < ‖p‖ := norm_pos_iff.2 hp
  have h1 := hGb n hn p hp hpr
  have h2 := sqrt_mul_one_add_abs_log_le r ‖p‖ ht hpr
  have hsq : ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) =
      ‖p‖ * Real.sqrt ‖p‖ * (Real.sqrt ‖p‖ * (1 + |Real.log ‖p‖|)) := by
    have := Real.mul_self_sqrt ht.le
    calc ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) = ‖p‖ * (Real.sqrt ‖p‖ * Real.sqrt ‖p‖) *
          (1 + |Real.log ‖p‖|) := by rw [this]; ring
      _ = ‖p‖ * Real.sqrt ‖p‖ * (Real.sqrt ‖p‖ * (1 + |Real.log ‖p‖|)) := by ring
  calc ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := h1
    _ = A * (‖p‖ * Real.sqrt ‖p‖) * (Real.sqrt ‖p‖ * (1 + |Real.log ‖p‖|)) := by
        rw [mul_assoc A, hsq, ← mul_assoc]
    _ ≤ A * (‖p‖ * Real.sqrt ‖p‖) * (3 + (1 + r) ^ 2) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ = A * (3 + (1 + r) ^ 2) * (‖p‖ * Real.sqrt ‖p‖) := by ring

variable (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hM1 : 1 ≤ M)
  (hM : ∀ k : ℕ, k ≤ 4 → ∀ q : ℝ × ℝ, ‖iteratedFDeriv ℝ k χ₁ q‖ ≤ M)
  (hG : ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0})
  (hGb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * K * (‖p‖ * Real.sqrt ‖p‖))
  (hH : ContDiff ℝ 4 H) (hH0 : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0)
  (hHb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B)

include hε hM1 hM in

lemma norm_one_sub_χ_le (p : ℝ × ℝ) : ‖iteratedFDeriv ℝ 0 (fun q => 1 - χ ε q) p‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [χ_nonneg ε p, χ_le_one ε p]

include hε hM in

lemma norm_iteratedFDeriv_one_sub_χ_le {l : ℕ} (hl1 : 1 ≤ l) (hl : l ≤ 4) (p : ℝ × ℝ)
    (ht : 0 < ‖p‖) :
    ‖p‖ ^ l * ‖iteratedFDeriv ℝ l (fun q => 1 - χ ε q) p‖ ≤ 16 * M := by
  rw [norm_iteratedFDeriv_one_sub_χ hε hl1]
  by_cases h2 : 2 * ε < ‖p‖
  · rw [iteratedFDeriv_χ_eq_zero_of_gt hε l h2, norm_zero, mul_zero]
    linarith [hM 0 (by norm_num) 0, norm_nonneg (iteratedFDeriv ℝ 0 χ₁ 0)]
  · push Not at h2
    rw [norm_iteratedFDeriv_χ ε hε l p]
    have hb := hM l hl (ε⁻¹ • p)
    have hεl : ‖p‖ ^ l * ε⁻¹ ^ l ≤ 16 := by
      rw [← mul_pow]
      have h1 : ‖p‖ * ε⁻¹ ≤ 2 := by
        rw [mul_inv_le_iff₀ hε]; linarith
      have h0 : 0 ≤ ‖p‖ * ε⁻¹ := by positivity
      calc (‖p‖ * ε⁻¹) ^ l ≤ 2 ^ l := pow_le_pow_left₀ h0 h1 l
        _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hl
        _ = 16 := by norm_num
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
    calc ‖p‖ ^ l * (ε⁻¹ ^ l * ‖iteratedFDeriv ℝ l χ₁ (ε⁻¹ • p)‖)
        = (‖p‖ ^ l * ε⁻¹ ^ l) * ‖iteratedFDeriv ℝ l χ₁ (ε⁻¹ • p)‖ := by ring
      _ ≤ 16 * M := mul_le_mul hεl hb (norm_nonneg _) (by norm_num)

include hε hA hK hM1 hM hGb in

lemma prod_bound {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ i) (p : ℝ × ℝ) (hp : p ≠ 0)
    (hpr : ‖p‖ ≤ r) :
    ‖iteratedFDeriv ℝ j G p‖ * ‖iteratedFDeriv ℝ (i - j) (fun q => 1 - χ ε q) p‖ ≤
      16 * A * K * M * (max 1 r) ^ 4 * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) := by
  set t := ‖p‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hp
  set R₁ := max 1 r with hR₁
  have hR₁1 : 1 ≤ R₁ := le_max_left _ _
  have htR : t ≤ R₁ := hpr.trans (le_max_right _ _)
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := by linarith

  have hGj : ‖iteratedFDeriv ℝ j G p‖ ≤ A * K * (t * Real.sqrt t) / t ^ j := by
    rw [le_div_iff₀ (pow_pos ht j), mul_comm]
    exact hGb j (hj.trans hi) p hp hpr

  have hgeom : ∀ m : ℕ, m ≤ 4 → t * Real.sqrt t / t ^ m ≤ R₁ ^ 4 * (Real.sqrt t / t ^ 3) := by
    intro m hm
    rw [div_le_iff₀ (pow_pos ht m)]
    have : R₁ ^ 4 * (Real.sqrt t / t ^ 3) * t ^ m = Real.sqrt t * (R₁ ^ 4 * t ^ m / t ^ 3) := by
      ring
    rw [this]
    have h2 : t = t ^ 4 / t ^ 3 := by
      rw [eq_div_iff (pow_pos ht 3).ne']; ring
    have h3 : t ^ 4 ≤ R₁ ^ 4 * t ^ m := by
      obtain ⟨d, hd⟩ : ∃ d, 4 = m + d := ⟨4 - m, by omega⟩
      have e1 : t ^ 4 = t ^ m * t ^ d := by rw [← pow_add, ← hd]
      have e2 : t ^ d ≤ R₁ ^ 4 :=
        (pow_le_pow_left₀ ht.le htR d).trans (pow_le_pow_right₀ hR₁1 (by omega))
      rw [e1, mul_comm (R₁ ^ 4)]
      exact mul_le_mul_of_nonneg_left e2 (pow_nonneg ht.le m)
    calc t * Real.sqrt t = Real.sqrt t * (t ^ 4 / t ^ 3) := by rw [← h2]; ring
      _ ≤ Real.sqrt t * (R₁ ^ 4 * t ^ m / t ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hs
          exact div_le_div_of_nonneg_right h3 (pow_nonneg ht.le 3)
  rcases Nat.eq_zero_or_pos (i - j) with hl | hl
  ·
    rw [hl]
    have h1 := norm_one_sub_χ_le (ε := ε) (M := M) hε hM1 hM p
    calc ‖iteratedFDeriv ℝ j G p‖ * ‖iteratedFDeriv ℝ 0 (fun q => 1 - χ ε q) p‖
        ≤ (A * K * (t * Real.sqrt t) / t ^ j) * 1 :=
          mul_le_mul hGj h1 (norm_nonneg _) (by positivity)
      _ = A * K * (t * Real.sqrt t / t ^ j) := by ring
      _ ≤ A * K * (R₁ ^ 4 * (Real.sqrt t / t ^ 3)) := by
          apply mul_le_mul_of_nonneg_left (hgeom j (hj.trans hi)) (by positivity)
      _ = 1 * A * K * 1 * R₁ ^ 4 * (Real.sqrt t / t ^ 3) := by ring
      _ ≤ 16 * A * K * M * R₁ ^ 4 * (Real.sqrt t / t ^ 3) := by
          gcongr
          · norm_num
  ·
    have hl4 : i - j ≤ 4 := by omega
    have h1 := norm_iteratedFDeriv_one_sub_χ_le (ε := ε) (M := M) hε hM hl hl4 p ht

    have h1' : ‖iteratedFDeriv ℝ (i - j) (fun q => 1 - χ ε q) p‖ ≤ 16 * M / t ^ (i - j) := by
      rw [le_div_iff₀ (pow_pos ht _), mul_comm]; exact h1
    have hij : t ^ j * t ^ (i - j) = t ^ i := by
      rw [← pow_add]; congr 1; omega
    calc ‖iteratedFDeriv ℝ j G p‖ * ‖iteratedFDeriv ℝ (i - j) (fun q => 1 - χ ε q) p‖
        ≤ (A * K * (t * Real.sqrt t) / t ^ j) * (16 * M / t ^ (i - j)) :=
          mul_le_mul hGj h1' (norm_nonneg _) (by positivity)
      _ = 16 * A * K * M * (t * Real.sqrt t / (t ^ j * t ^ (i - j))) := by
          field_simp
      _ = 16 * A * K * M * (t * Real.sqrt t / t ^ i) := by rw [hij]
      _ ≤ 16 * A * K * M * (R₁ ^ 4 * (Real.sqrt t / t ^ 3)) := by
          apply mul_le_mul_of_nonneg_left (hgeom i hi) (by positivity)
      _ = 16 * A * K * M * R₁ ^ 4 * (Real.sqrt t / t ^ 3) := by ring

include hε hA hK hM1 hM hG hGb in

lemma norm_iteratedFDeriv_gfar_le {i : ℕ} (hi : i ≤ 4) (p : ℝ × ℝ) (hp : p ≠ 0) (hpr : ‖p‖ ≤ r) :
    ‖iteratedFDeriv ℝ i (gfar ε G) p‖ ≤
      256 * A * K * M * (max 1 r) ^ 4 * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) := by
  have hU : UniqueDiffOn ℝ {q : ℝ × ℝ | q ≠ 0} := isOpen_U.uniqueDiffOn
  have hχ : ContDiffOn ℝ 4 (fun q => 1 - χ ε q) {q : ℝ × ℝ | q ≠ 0} :=
    (contDiff_const.sub ((χ_contDiff ε).of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn
  have hL := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (A := ℝ) hG hχ hU (x := p) hp
    (n := i) (by exact_mod_cast hi)

  have hw : ∀ (f : ℝ × ℝ → ℝ) (k : ℕ),
      iteratedFDerivWithin ℝ k f {q : ℝ × ℝ | q ≠ 0} p = iteratedFDeriv ℝ k f p :=
    fun f k => iteratedFDerivWithin_of_isOpen k isOpen_U hp
  simp only [hw] at hL
  have hgf : (fun y => G y * (1 - χ ε y)) = gfar ε G := by funext y; rfl
  rw [hgf] at hL
  refine hL.trans ?_
  set Q := 16 * A * K * M * (max 1 r) ^ 4 * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ M := by linarith
    positivity
  calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j G p‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun y => 1 - χ ε y) p‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Q := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact prod_bound hε hA hK hM1 hM hGb hi (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) p hp hpr
    _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * Q := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ i * Q := by
        congr 1
        have := Nat.sum_range_choose i
        exact_mod_cast this
    _ ≤ (2 : ℝ) ^ 4 * Q := by
        apply mul_le_mul_of_nonneg_right _ hQ0
        exact pow_le_pow_right₀ (by norm_num) hi
    _ = 256 * A * K * M * (max 1 r) ^ 4 * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) := by rw [hQ]; ring

include hε hA hB hK hM1 hM hG hGb hH hHb in

lemma norm_iteratedFDeriv_ffar_le_of_mem (p : ℝ × ℝ) (hp : p ≠ 0) (hpr : ‖p‖ ≤ r) :
    ‖iteratedFDeriv ℝ 4 (ffar ε G H) p‖ ≤
      4096 * A * K * M * (max 1 r) ^ 4 * B * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) := by
  have hg : ContDiff ℝ 4 (gfar ε G) := contDiff_gfar hε hG
  have hgc : ContDiff ℝ 4 (fun q => ((gfar ε G q : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (A := ℂ) hgc hH p (n := 4) le_rfl
  have hff : (fun y => ((gfar ε G y : ℝ) : ℂ) * H y) = ffar ε G H := by funext y; rfl
  rw [hff] at hL
  refine hL.trans ?_

  have hiso : ∀ k : ℕ, k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun q => ((gfar ε G q : ℝ) : ℂ)) p‖ = ‖iteratedFDeriv ℝ k (gfar ε G) p‖ := by
    intro k hk
    have := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (hg.contDiffAt (x := p))
      (i := k) (by exact_mod_cast hk)
    exact this
  set Q := 256 * A * K * M * (max 1 r) ^ 4 * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ M := by linarith
    positivity
  calc ∑ i ∈ Finset.range (4 + 1), ((4 : ℕ).choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q => ((gfar ε G q : ℝ) : ℂ)) p‖ * ‖iteratedFDeriv ℝ (4 - i) H p‖
      ≤ ∑ i ∈ Finset.range (4 + 1), ((4 : ℕ).choose i : ℝ) * (Q * B) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi4 : i ≤ 4 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [hiso i hi4]
        exact mul_le_mul (norm_iteratedFDeriv_gfar_le hε hA hK hM1 hM hG hGb hi4 p hp hpr)
          (hHb (4 - i) (by omega) p) (norm_nonneg _) hQ0
    _ = (∑ i ∈ Finset.range (4 + 1), ((4 : ℕ).choose i : ℝ)) * (Q * B) := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ 4 * (Q * B) := by
        congr 1
        have := Nat.sum_range_choose 4
        exact_mod_cast this
    _ = 4096 * A * K * M * (max 1 r) ^ 4 * B * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) := by rw [hQ]; ring

end bounds

section assembly

variable {r ε A B K M : ℝ} {G : ℝ × ℝ → ℝ} {H : ℝ × ℝ → ℂ}
variable (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hM1 : 1 ≤ M)
  (hM : ∀ k : ℕ, k ≤ 4 → ∀ q : ℝ × ℝ, ‖iteratedFDeriv ℝ k χ₁ q‖ ≤ M)
  (hG : ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0})
  (hGb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * K * (‖p‖ * Real.sqrt ‖p‖))
  (hH : ContDiff ℝ 4 H) (hH0 : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0)
  (hHb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B)

noncomputable def Λ (r A B K M : ℝ) : ℝ := 4096 * A * K * M * (max 1 r) ^ 4 * B

include hε hA hB hK hM1 hM hG hGb hH hH0 hHb in

lemma far_majorant (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ 4 (ffar ε G H) p‖ ≤ Λ r A B K M * (g1 (ε / 2) r p.1 * g1 (ε / 2) r p.2) := by
  have hM0 : 0 ≤ M := by linarith
  have hΛ : 0 ≤ Λ r A B K M := by unfold Λ; positivity
  have hδ : 0 < ε / 2 := by linarith
  have hnn : 0 ≤ Λ r A B K M * (g1 (ε / 2) r p.1 * g1 (ε / 2) r p.2) :=
    mul_nonneg hΛ (mul_nonneg (g1_nonneg _ _ _ hδ) (g1_nonneg _ _ _ hδ))
  by_cases h1 : ‖p‖ < ε / 2
  · rw [((ffar_eventuallyEq_zero (G := G) hε H p h1).iteratedFDeriv ℝ 4).eq_of_nhds,
      iteratedFDeriv_fun_zero]
    simpa using hnn
  by_cases h2 : r < ‖p‖
  · have hev : ffar ε G H =ᶠ[nhds p] fun _ => 0 := by
      have hopen : IsOpen {q : ℝ × ℝ | r < ‖q‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds h2] with q hq
      exact ffar_eq_zero r hH0 q hq.le
    rw [(hev.iteratedFDeriv ℝ 4).eq_of_nhds, iteratedFDeriv_fun_zero]
    simpa using hnn
  push Not at h1 h2
  have hp : p ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have ht : 0 < ‖p‖ := norm_pos_iff.2 hp
  calc ‖iteratedFDeriv ℝ 4 (ffar ε G H) p‖
      ≤ 4096 * A * K * M * (max 1 r) ^ 4 * B * (Real.sqrt ‖p‖ / ‖p‖ ^ 3) :=
        norm_iteratedFDeriv_ffar_le_of_mem hε hA hB hK hM1 hM hG hGb hH hHb p hp h2
    _ = Λ r A B K M * ‖p‖ ^ (-(5 / 2 : ℝ)) := by rw [rpow_neg_five_halves _ ht]; rfl
    _ ≤ Λ r A B K M * (g1 (ε / 2) r p.1 * g1 (ε / 2) r p.2) :=
        mul_le_mul_of_nonneg_left (rpow_norm_le_g1_mul_g1 (ε / 2) r hδ p h1 h2) hΛ

include hε hε1 hA hB hK hM1 hM hG hGb hH hH0 hHb in

lemma norm_J2_top_le (ξ η : ℝ) (w : Fin 4 → ℝ × ℝ) (hw : ∀ i, ‖w i‖ ≤ 1) :
    ‖J2 ξ η w (ffar ε G H)‖ ≤ Λ r A B K M * (100 * (ε / 2) ^ (-(1 / 2 : ℝ))) := by
  have hδ : 0 < ε / 2 := by linarith
  have hΛ : 0 ≤ Λ r A B K M := by
    have hM0 : 0 ≤ M := by linarith
    unfold Λ; positivity
  have hF := contDiff_ffar hε hG hH
  have h := norm_J2_le r hF (ffar_eq_zero r hH0) ξ η le_rfl w hw
    (fun p => Λ r A B K M * (g1 (ε / 2) r p.1 * g1 (ε / 2) r p.2))
    ((integrable_g1_prod (ε / 2) r hδ).const_mul _)
    (Filter.Eventually.of_forall (far_majorant hε hA hB hK hM1 hM hG hGb hH hH0 hHb))
  refine h.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_g1_prod_le (ε / 2) r hδ (by linarith)) hΛ

include hr hε hA hB hK hM1 hM hG hGb hH hH0 hHb in

lemma norm_J2_zero_le (ξ η : ℝ) :
    ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖ ≤ 4 * A * K * (max 1 r) ^ 4 * B := by
  have hM0 : 0 ≤ M := by linarith
  set R₁ := max 1 r with hR₁
  have hR₁1 : 1 ≤ R₁ := le_max_left _ _
  have hrR : r ≤ R₁ := le_max_right _ _
  have hF := contDiff_ffar hε hG hH
  set c₀ := A * K * R₁ ^ 2 * B with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hpt : ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ 0 (ffar ε G H) p‖ ≤
      {q : ℝ × ℝ | ‖q‖ ≤ r}.indicator (fun _ => c₀) p := by
    intro p
    rw [norm_iteratedFDeriv_zero]
    by_cases hpr : ‖p‖ ≤ r
    · rw [indicator_of_mem (by exact hpr)]
      by_cases hp : p = 0
      · subst hp
        have : ffar ε G H 0 = 0 := by
          simp [ffar, gfar, χ_eq_one hε (p := (0 : ℝ × ℝ)) (by simp; positivity)]
        rw [this, norm_zero]; exact hc₀0
      · have ht : 0 < ‖p‖ := norm_pos_iff.2 hp
        have hG0 : ‖G p‖ ≤ A * K * (‖p‖ * Real.sqrt ‖p‖) := by
          have := hGb 0 (by norm_num) p hp hpr
          rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this
        have hts : ‖p‖ * Real.sqrt ‖p‖ ≤ R₁ ^ 2 := by
          have h1 : ‖p‖ ≤ R₁ := hpr.trans hrR
          have h2 : Real.sqrt ‖p‖ ≤ R₁ := by
            rw [Real.sqrt_le_left (by linarith)]; nlinarith
          calc ‖p‖ * Real.sqrt ‖p‖ ≤ R₁ * R₁ :=
                mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by linarith)
            _ = R₁ ^ 2 := by ring
        have hH1 : ‖H p‖ ≤ B := by
          have := hHb 0 (by norm_num) p
          rwa [norm_iteratedFDeriv_zero] at this
        have hχ1 : |1 - χ ε p| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [χ_nonneg ε p, χ_le_one ε p]
        unfold ffar gfar
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        calc |G p| * |1 - χ ε p| * ‖H p‖ ≤ (A * K * (‖p‖ * Real.sqrt ‖p‖)) * 1 * B := by
              apply mul_le_mul (mul_le_mul hG0 hχ1 (abs_nonneg _) (by positivity)) hH1
                (norm_nonneg _) (by positivity)
          _ ≤ A * K * R₁ ^ 2 * 1 * B := by gcongr
          _ = c₀ := by rw [hc₀]; ring
    · push Not at hpr
      rw [indicator_of_notMem (by exact not_le.2 hpr), ffar_eq_zero r hH0 p hpr.le, norm_zero]
  have h := norm_J2_le r hF (ffar_eq_zero r hH0) ξ η (n := 0) (by norm_num) Fin.elim0
    (fun i => Fin.elim0 i) _ (integrable_indicator_norm_le r c₀) (Filter.Eventually.of_forall hpt)
  refine h.trans ?_
  rw [integral_indicator_norm_le r c₀ hr.le, hc₀]
  have : (2 * r) ^ 2 ≤ 4 * R₁ ^ 2 := by nlinarith
  calc A * K * R₁ ^ 2 * B * (2 * r) ^ 2 ≤ A * K * R₁ ^ 2 * B * (4 * R₁ ^ 2) := by
        apply mul_le_mul_of_nonneg_left this; positivity
    _ = 4 * A * K * R₁ ^ 4 * B := by ring

include hε hA hB hK hGb hH0 hHb in

lemma norm_near_le (ξ η : ℝ) :
    ‖∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ))‖ ≤
      A * K * B * (2 * ε * Real.sqrt (2 * ε)) * (4 * ε) ^ 2 := by
  set c₀ := A * K * B * (2 * ε * Real.sqrt (2 * ε)) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ≠ (0 : ℝ × ℝ) := by
    have h : (volume : Measure (ℝ × ℝ)) {(0 : ℝ × ℝ)} = 0 := measure_singleton _
    rw [ae_iff]; simpa using h
  have hpt : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ))‖ ≤
        {q : ℝ × ℝ | ‖q‖ ≤ 2 * ε}.indicator (fun _ => c₀) p := by
    filter_upwards [hae] with p hp
    rw [norm_mul, norm_mul, norm_ch, norm_ch, one_mul, one_mul]
    by_cases h2 : ‖p‖ ≤ 2 * ε
    · rw [indicator_of_mem (by exact h2)]
      by_cases hpr : ‖p‖ ≤ r
      · have ht : 0 < ‖p‖ := norm_pos_iff.2 hp
        have hG0 : ‖G p‖ ≤ A * K * (‖p‖ * Real.sqrt ‖p‖) := by
          have := hGb 0 (by norm_num) p hp hpr
          rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this
        have hts : ‖p‖ * Real.sqrt ‖p‖ ≤ 2 * ε * Real.sqrt (2 * ε) :=
          mul_le_mul h2 (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (by linarith)
        have hH1 : ‖H p‖ ≤ B := by
          have := hHb 0 (by norm_num) p
          rwa [norm_iteratedFDeriv_zero] at this
        have hχ1 : ‖(χ ε p : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ_nonneg ε p)]
          exact χ_le_one ε p
        rw [norm_mul, norm_mul, Complex.norm_real]
        calc ‖G p‖ * ‖H p‖ * ‖(χ ε p : ℂ)‖ ≤ (A * K * (2 * ε * Real.sqrt (2 * ε))) * B * 1 := by
              apply mul_le_mul (mul_le_mul (hG0.trans _) hH1 (norm_nonneg _) (by positivity)) hχ1
                (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left hts (by positivity)
          _ = c₀ := by rw [hc₀]; ring
      · push Not at hpr
        rw [hH0 p hpr.le]; simp [hc₀0]
    · push Not at h2
      rw [indicator_of_notMem (by exact not_le.2 h2), χ_eq_zero hε h2.le]
      simp
  have h := norm_integral_le_of_norm_le (integrable_indicator_norm_le (2 * ε) c₀) hpt
  refine h.trans ?_
  rw [integral_indicator_norm_le (2 * ε) c₀ (by linarith)]
  ring_nf
  rfl

end assembly

section final

variable {r ε A B K M : ℝ} {G : ℝ × ℝ → ℝ} {H : ℝ × ℝ → ℂ}

lemma eps_facts (N : ℝ) (hN : 1 ≤ N) :
    0 < N⁻¹ ∧ N⁻¹ ≤ 1 ∧
      N⁻¹ ^ 3 * Real.sqrt N⁻¹ = (N ^ (7 / 2 : ℝ))⁻¹ ∧
      Real.sqrt N / N ^ 4 = (N ^ (7 / 2 : ℝ))⁻¹ ∧
      (N⁻¹ / 2) ^ (-(1 / 2 : ℝ)) = Real.sqrt (2 * N) ∧
      N ^ (7 / 2 : ℝ) ≤ N ^ 4 := by
  have hN0 : 0 < N := by linarith
  refine ⟨inv_pos.2 hN0, inv_le_one_of_one_le₀ hN, ?_, ?_, ?_, ?_⟩
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (inv_pos.2 hN0),
      Real.inv_rpow hN0.le]
    norm_num
  · have h4 : (N : ℝ) ^ 4 = N ^ (7 / 2 : ℝ) * Real.sqrt N := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0, ← Real.rpow_natCast]; norm_num
    rw [h4, div_mul_eq_div_div_swap, div_self (Real.sqrt_pos.2 hN0).ne', one_div]
  · have : N⁻¹ / 2 = (2 * N)⁻¹ := by field_simp
    rw [this, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, Real.sqrt_eq_rpow]
  · have := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (7 / 2 : ℝ) ≤ 4)
    simpa using this

variable (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hM1 : 1 ≤ M)
  (hM : ∀ k : ℕ, k ≤ 4 → ∀ q : ℝ × ℝ, ‖iteratedFDeriv ℝ k χ₁ q‖ ≤ M)
  (hG : ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0})
  (hGb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * K * (‖p‖ * Real.sqrt ‖p‖))
  (hH : ContDiff ℝ 4 H) (hH0 : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0)
  (hHb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B)

include hε hε1 hA hB hK hM1 hM hG hGb hH hH0 hHb in

lemma far_big (ξ η : ℝ) (N : ℝ) (hN : 1 ≤ N) (hεN : ε = N⁻¹) (c : ℂ) (hc : N ≤ ‖c‖)
    (w : Fin 4 → ℝ × ℝ) (hw : ∀ i, ‖w i‖ ≤ 1)
    (hcw : c * (c * (c * (c * J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)))) =
      J2 ξ η w (ffar ε G H)) :
    ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖ ≤
      150 * Λ r A B K M * (N ^ (7 / 2 : ℝ))⁻¹ := by
  subst hεN
  obtain ⟨_, _, _, hsq, hhalf, _⟩ := eps_facts N hN
  have hN0 : 0 < N := by linarith
  have hΛ : 0 ≤ Λ r A B K M := by
    have hM0 : 0 ≤ M := by linarith
    unfold Λ; positivity
  set X := ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar N⁻¹ G H)‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  have htop := norm_J2_top_le hε hε1 hA hB hK hM1 hM hG hGb hH hH0 hHb ξ η w hw
  rw [← hcw, norm_mul, norm_mul, norm_mul, norm_mul, hhalf] at htop

  have h2N : Real.sqrt (2 * N) ≤ 3 / 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_iff]; norm_num
  have h1 : ‖c‖ ^ 4 * X ≤ 150 * Λ r A B K M * Real.sqrt N := by
    calc ‖c‖ ^ 4 * X = ‖c‖ * (‖c‖ * (‖c‖ * (‖c‖ * X))) := by ring
      _ ≤ Λ r A B K M * (100 * Real.sqrt (2 * N)) := htop
      _ ≤ Λ r A B K M * (100 * (3 / 2 * Real.sqrt N)) := by gcongr
      _ = 150 * Λ r A B K M * Real.sqrt N := by ring
  have h2 : N ^ 4 * X ≤ ‖c‖ ^ 4 * X :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hN0.le hc 4) hX0
  have h3 : X ≤ 150 * Λ r A B K M * Real.sqrt N / N ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    calc X * N ^ 4 = N ^ 4 * X := by ring
      _ ≤ 150 * Λ r A B K M * Real.sqrt N := h2.trans h1
  calc X ≤ 150 * Λ r A B K M * Real.sqrt N / N ^ 4 := h3
    _ = 150 * Λ r A B K M * (Real.sqrt N / N ^ 4) := by ring
    _ = 150 * Λ r A B K M * (N ^ (7 / 2 : ℝ))⁻¹ := by rw [hsq]

end final

theorem core_main (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
        ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0} →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
            ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) →
        ContDiff ℝ 4 H → (∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0) →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B) →
        ∀ ξ η : ℝ,
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ))) *
              ((G p : ℂ) * H p)‖ ≤
            C * A * B * ((1 + |ξ| + |η|) ^ (7 / 2 : ℝ))⁻¹ := by
  obtain ⟨M, hM1, hM⟩ := exists_bound_χ₁
  set K : ℝ := 3 + (1 + r) ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  set R₁ : ℝ := max 1 r with hR₁
  have hM0 : 0 ≤ M := by linarith
  refine ⟨48 * K + 324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4, by positivity, ?_⟩
  intro G H A B hA hB hG hGb0 hH hH0 hHb ξ η
  have hGb : ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
      ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * K * (‖p‖ * Real.sqrt ‖p‖) :=
    fun n hn p hp hpr => G_bound_sqrt hA hGb0 n hn p hp hpr

  set N : ℝ := 1 + |ξ| + |η| with hNdef
  have hN : 1 ≤ N := by have := abs_nonneg ξ; have := abs_nonneg η; linarith
  have hN0 : 0 < N := by linarith
  obtain ⟨hε, hε1, hε72, hsqN, hhalf, hN4⟩ := eps_facts N hN
  set ε : ℝ := N⁻¹ with hεdef
  have hF : ContDiff ℝ 4 (ffar ε G H) := contDiff_ffar hε hG hH
  have hsupp : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → ffar ε G H p = 0 := ffar_eq_zero r hH0

  have hRHS0 : 0 ≤ (48 * K + 324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B *
      (N ^ (7 / 2 : ℝ))⁻¹ := by positivity

  have hker : (fun p : ℝ × ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ))) *
      ((G p : ℂ) * H p)) = fun p => ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p) := by
    funext p; rw [kernel_eq]
  rw [hker]

  have hfar_int : Integrable (fun p : ℝ × ℝ => ch ξ p.1 * ch η p.2 * ffar ε G H p)
      (volume : Measure (ℝ × ℝ)) := by
    have := integrable_word r hF hsupp ξ η (n := 0) (by norm_num) Fin.elim0
    simpa only [D_zero] using this
  have hfar_eq : ∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ffar ε G H p =
      J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H) := by
    rw [J2_eq_integral r hF hsupp ξ η (n := 0) (by norm_num)]
    simp only [D_zero]

  have hsplit : ∀ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p) =
      ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ)) + ch ξ p.1 * ch η p.2 * ffar ε G H p := by
    intro p
    simp only [ffar, gfar]
    push_cast
    ring

  have hnear := norm_near_le (r := r) hε hA hB hK hGb hH0 hHb ξ η
  have hnear' : A * K * B * (2 * ε * Real.sqrt (2 * ε)) * (4 * ε) ^ 2 ≤
      48 * K * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by
    have h2 : Real.sqrt (2 * ε) ≤ 3 / 2 * Real.sqrt ε := by
      rw [Real.sqrt_mul (by norm_num)]
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [Real.sqrt_le_iff]; norm_num
    calc A * K * B * (2 * ε * Real.sqrt (2 * ε)) * (4 * ε) ^ 2
        = 32 * (A * K * B) * (ε ^ 3 * Real.sqrt (2 * ε)) := by ring
      _ ≤ 32 * (A * K * B) * (ε ^ 3 * (3 / 2 * Real.sqrt ε)) := by gcongr
      _ = 48 * K * A * B * (ε ^ 3 * Real.sqrt ε) := by ring
      _ = 48 * K * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by rw [hε72]
  have hfar : ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖ ≤
      (324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by
    by_cases hbig : 1 ≤ |ξ| ∨ 1 ≤ |η|
    ·
      have hbound : ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖ ≤
          150 * Λ r A B K M * (N ^ (7 / 2 : ℝ))⁻¹ := by
        set e₁ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ))
        set e₂ : ℝ × ℝ := ((0 : ℝ), (1 : ℝ))
        have he₁ : ‖e₁‖ ≤ 1 := by simp [e₁, Prod.norm_def]
        have he₂ : ‖e₂‖ ≤ 1 := by simp [e₂, Prod.norm_def]
        have hcons : ∀ {k : ℕ} (v : ℝ × ℝ) (u : Fin k → ℝ × ℝ), ‖v‖ ≤ 1 → (∀ i, ‖u i‖ ≤ 1) →
            ∀ i, ‖(Fin.cons v u : Fin (k + 1) → ℝ × ℝ) i‖ ≤ 1 := by
          intro k v u hv hu i
          refine Fin.cases ?_ ?_ i
          · simpa using hv
          · intro j; simpa using hu j
        have hw0 : ∀ i : Fin 0, ‖(Fin.elim0 : Fin 0 → ℝ × ℝ) i‖ ≤ 1 := fun i => Fin.elim0 i
        rcases le_total |η| |ξ| with hle | hle
        ·
          have hξ1 : 1 ≤ |ξ| := by rcases hbig with h | h <;> linarith
          set c : ℂ := 2 * Real.pi * Complex.I * ξ with hcdef
          have hc : N ≤ ‖c‖ := by
            have : ‖c‖ = 2 * Real.pi * |ξ| := by rw [hcdef]; simp [abs_of_pos Real.pi_pos]
            rw [this]
            have := Real.pi_gt_three
            nlinarith
          apply far_big hε hε1 hA hB hK hM1 hM hG hGb hH hH0 hHb ξ η N hN rfl c hc
            (Fin.cons e₁ (Fin.cons e₁ (Fin.cons e₁ (Fin.cons e₁ Fin.elim0))))
            (hcons _ _ he₁ (hcons _ _ he₁ (hcons _ _ he₁ (hcons _ _ he₁ hw0))))
          rw [rule_x r hF hsupp ξ η (by norm_num), rule_x r hF hsupp ξ η (by norm_num),
            rule_x r hF hsupp ξ η (by norm_num), rule_x r hF hsupp ξ η (by norm_num)]
        ·
          have hη1 : 1 ≤ |η| := by rcases hbig with h | h <;> linarith
          set c : ℂ := 2 * Real.pi * Complex.I * η with hcdef
          have hc : N ≤ ‖c‖ := by
            have : ‖c‖ = 2 * Real.pi * |η| := by rw [hcdef]; simp [abs_of_pos Real.pi_pos]
            rw [this]
            have := Real.pi_gt_three
            nlinarith
          apply far_big hε hε1 hA hB hK hM1 hM hG hGb hH hH0 hHb ξ η N hN rfl c hc
            (Fin.cons e₂ (Fin.cons e₂ (Fin.cons e₂ (Fin.cons e₂ Fin.elim0))))
            (hcons _ _ he₂ (hcons _ _ he₂ (hcons _ _ he₂ (hcons _ _ he₂ hw0))))
          rw [rule_y r hF hsupp ξ η (by norm_num), rule_y r hF hsupp ξ η (by norm_num),
            rule_y r hF hsupp ξ η (by norm_num), rule_y r hF hsupp ξ η (by norm_num)]
      refine hbound.trans ?_
      unfold Λ
      have : 150 * (4096 * A * K * M * max 1 r ^ 4 * B) * (N ^ (7 / 2 : ℝ))⁻¹ =
          (614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by rw [hR₁]; ring
      rw [this]
      have h0 : 0 ≤ (324 * K * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by positivity
      have hsum : (324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ =
          (324 * K * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ +
            (614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by ring
      rw [hsum]
      linarith [h0]
    ·
      push Not at hbig
      have hN3 : N ≤ 3 := by rw [hNdef]; linarith [hbig.1, hbig.2]
      have h81 : N ^ (7 / 2 : ℝ) ≤ 81 := by
        calc N ^ (7 / 2 : ℝ) ≤ N ^ 4 := hN4
          _ ≤ 3 ^ 4 := pow_le_pow_left₀ hN0.le hN3 4
          _ = 81 := by norm_num
      have hinv : 1 ≤ 81 * (N ^ (7 / 2 : ℝ))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hN0 _)]; linarith
      have h := norm_J2_zero_le hr hε hA hB hK hM1 hM hG hGb hH hH0 hHb ξ η
      rw [← hR₁] at h
      have h0 : 0 ≤ 4 * A * K * R₁ ^ 4 * B := by positivity
      have h0' : 0 ≤ (614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by positivity
      calc ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖ ≤ 4 * A * K * R₁ ^ 4 * B := h
        _ = 4 * A * K * R₁ ^ 4 * B * 1 := by ring
        _ ≤ 4 * A * K * R₁ ^ 4 * B * (81 * (N ^ (7 / 2 : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left hinv h0
        _ = (324 * K * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by ring
        _ ≤ (324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by
            have hsum : (324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ =
                (324 * K * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ +
                  (614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by ring
            rw [hsum]
            linarith [h0']

  by_cases hint : Integrable (fun p : ℝ × ℝ => ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p))
      (volume : Measure (ℝ × ℝ))
  · have hnear_int : Integrable (fun p : ℝ × ℝ => ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ)))
        (volume : Measure (ℝ × ℝ)) := by
      have := hint.sub hfar_int
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Pi.sub_apply]
      rw [hsplit p]; ring
    have hI : ∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p) =
        (∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ))) +
          ∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ffar ε G H p := by
      rw [← integral_add hnear_int hfar_int]
      exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
    rw [hI, hfar_eq]
    calc ‖(∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ))) +
          J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖
        ≤ ‖∫ p : ℝ × ℝ, ch ξ p.1 * ch η p.2 * ((G p : ℂ) * H p * (χ ε p : ℂ))‖ +
          ‖J2 ξ η (Fin.elim0 : Fin 0 → ℝ × ℝ) (ffar ε G H)‖ := norm_add_le _ _
      _ ≤ 48 * K * A * B * (N ^ (7 / 2 : ℝ))⁻¹ +
          (324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ :=
          add_le_add (hnear.trans hnear') hfar
      _ = (48 * K + 324 * K * R₁ ^ 4 + 614400 * K * M * R₁ ^ 4) * A * B * (N ^ (7 / 2 : ℝ))⁻¹ := by
          ring
  · rw [integral_undef hint, norm_zero]
    exact hRHS0

end K2Core
p2m_reactivate "P2MW.S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log.K2Core"

open K2Core in
theorem solution
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
        ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0} →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
            ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) →
        ContDiff ℝ 4 H → (∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0) →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B) →
        ∀ ξ η : ℝ,
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ))) *
              ((G p : ℂ) * H p)‖ ≤
            C * A * B * ((1 + |ξ| + |η|) ^ (7 / 2 : ℝ))⁻¹ :=
  core_main r hr

end S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
end P2MW
export P2MW.S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log (solution)
