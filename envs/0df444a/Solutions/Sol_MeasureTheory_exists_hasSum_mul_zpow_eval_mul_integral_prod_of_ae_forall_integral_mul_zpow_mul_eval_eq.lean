-- Prove2me | solution 1 for MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fce76570-9a6f-592b-8ed1-8f9d69637302

import Mathlib
import Theorems.Thm_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
import Theorems.Thm_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq

set_option autoImplicit false

open MeasureTheory

namespace LaurentTransport

theorem hasSum_conv (c : ℤ → ℂ) (Q : Polynomial ℂ) {Y : ℂ} (hY : Y ≠ 0) {I : ℂ}
    (hc : HasSum (fun ℓ : ℤ => c ℓ * Y ^ ℓ) I) :
    HasSum (fun j : ℤ => (∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))) * Y ^ j)
      (I * Q.eval Y) := by
  have hterm : ∀ i ∈ Q.support,
      HasSum (fun j : ℤ => Q.coeff i * c (j - (i : ℤ)) * Y ^ j) (I * (Q.coeff i * Y ^ i)) := by
    intro i _
    have h1 : HasSum (fun ℓ : ℤ => c ℓ * Y ^ ℓ * (Q.coeff i * Y ^ i)) (I * (Q.coeff i * Y ^ i)) :=
      hc.mul_right _
    have h2 : (fun j : ℤ => Q.coeff i * c (j - (i : ℤ)) * Y ^ j) ∘ (Equiv.addRight (i : ℤ)) =
        fun ℓ : ℤ => c ℓ * Y ^ ℓ * (Q.coeff i * Y ^ i) := by
      funext ℓ
      simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
      rw [zpow_add₀ hY, zpow_natCast]
      ring
    exact (Equiv.hasSum_iff (Equiv.addRight (i : ℤ))).mp (h2 ▸ h1)
  have h := hasSum_sum hterm
  have hval : ∑ i ∈ Q.support, I * (Q.coeff i * Y ^ i) = I * Q.eval Y := by
    rw [← Finset.mul_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hval] at h
  refine h.congr_fun fun j => ?_
  rw [Finset.sum_mul]

theorem summable_norm_conv (c : ℤ → ℂ) (Q : Polynomial ℂ) {r : ℝ} (hr : 0 < r)
    (hc : Summable fun ℓ : ℤ => ‖c ℓ‖ * r ^ ℓ) :
    Summable fun j : ℤ => ‖∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))‖ * r ^ j := by
  have hterm : ∀ i ∈ Q.support,
      Summable fun j : ℤ => ‖Q.coeff i‖ * r ^ (i : ℤ) * (‖c (j - (i : ℤ))‖ * r ^ (j - (i : ℤ))) := by
    intro i _
    have h1 : Summable ((fun ℓ : ℤ => ‖c ℓ‖ * r ^ ℓ) ∘ (Equiv.subRight (i : ℤ))) :=
      (Equiv.summable_iff (Equiv.subRight (i : ℤ))).mpr hc
    exact (h1.mul_left (‖Q.coeff i‖ * r ^ (i : ℤ))).congr fun j => by
      simp only [Function.comp_apply, Equiv.subRight_apply]
  have hsum := summable_sum hterm
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le j))
    (fun j => ?_) hsum
  calc ‖∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))‖ * r ^ j
      ≤ (∑ i ∈ Q.support, ‖Q.coeff i * c (j - (i : ℤ))‖) * r ^ j :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (zpow_nonneg hr.le j)
    _ = ∑ i ∈ Q.support, ‖Q.coeff i‖ * r ^ (i : ℤ) * (‖c (j - (i : ℤ))‖ * r ^ (j - (i : ℤ))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, zpow_sub₀ hr.ne']
        field_simp

section Fibre

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]

noncomputable def shellCoeff (μ : Measure T) (E : X × T → ℤ) (G : X × T → ℂ) (x : X) (ℓ : ℤ) : ℂ :=
  ∫ t in (fun t => E (x, t)) ⁻¹' {ℓ}, G (x, t) ∂μ

noncomputable def convCoeff (μ : Measure T) (E : X × T → ℤ) (G : X × T → ℂ) (Q : Polynomial ℂ)
    (x : X) (j : ℤ) : ℂ :=
  ∑ i ∈ Q.support, Q.coeff i * shellCoeff μ E G x (j - (i : ℤ))

theorem measurableSet_shell {E : X × T → ℤ} (hE : Measurable E) (ℓ : ℤ) :
    MeasurableSet (E ⁻¹' {ℓ}) :=
  hE (measurableSet_singleton ℓ)

theorem measurableSet_fibreShell {E : X × T → ℤ} (hE : Measurable E) (x : X) (ℓ : ℤ) :
    MeasurableSet ((fun t => E (x, t)) ⁻¹' {ℓ}) :=
  (hE.comp measurable_prodMk_left) (measurableSet_singleton ℓ)

theorem integrable_indicator_shell (m : Measure X) (μ : Measure T)
    {E : X × T → ℤ} (hE : Measurable E) (G : X × T → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun p => G p * (r : ℂ) ^ E p) (m.prod μ)) (ℓ : ℤ) :
    Integrable ((E ⁻¹' {ℓ}).indicator G) (m.prod μ) := by
  have h1 : Integrable (fun p => (E ⁻¹' {ℓ}).indicator (fun p => G p * (r : ℂ) ^ E p) p * (r : ℂ) ^ (-ℓ))
      (m.prod μ) := ((hG.indicator (measurableSet_shell hE ℓ)).mul_const _)
  refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
  show (E ⁻¹' {ℓ}).indicator (fun p => G p * (r : ℂ) ^ E p) p * (r : ℂ) ^ (-ℓ) = (E ⁻¹' {ℓ}).indicator G p
  by_cases hp : p ∈ E ⁻¹' {ℓ}
  · have hl : E p = ℓ := by simpa using hp
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, hl, mul_assoc, ← zpow_add₀
      (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0), add_neg_cancel, zpow_zero, mul_one]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul]

theorem integral_indicator_shell_fibre (μ : Measure T) {E : X × T → ℤ} (hE : Measurable E)
    (G : X × T → ℂ) (x : X) (ℓ : ℤ) :
    ∫ t, (E ⁻¹' {ℓ}).indicator G (x, t) ∂μ = shellCoeff μ E G x ℓ := by
  have h : (fun t => (E ⁻¹' {ℓ}).indicator G (x, t)) =
      ((fun t => E (x, t)) ⁻¹' {ℓ}).indicator fun t => G (x, t) := by
    funext t
    by_cases ht : E (x, t) = ℓ
    · rw [Set.indicator_of_mem (by simpa using ht), Set.indicator_of_mem (by simpa using ht)]
    · rw [Set.indicator_of_notMem (by simpa using ht), Set.indicator_of_notMem (by simpa using ht)]
  rw [h, integral_indicator (measurableSet_fibreShell hE x ℓ)]
  rfl

end Fibre

theorem one_sided
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (m : Measure X) (μ : Measure T) [SFinite m] [SFinite μ]
    {E : X × T → ℤ} (hE : Measurable E) (G : X × T → ℂ) (Q : Polynomial ℂ)
    {r : ℝ} (hr : 0 < r) (hG : Integrable (fun p => G p * (r : ℂ) ^ E p) (m.prod μ)) :
    (∀ j : ℤ, Integrable (fun x => convCoeff μ E G Q x j) m) ∧
    (Summable fun j : ℤ => ‖∫ x, convCoeff μ E G Q x j ∂m‖ * r ^ j) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      HasSum (fun j : ℤ => (∫ x, convCoeff μ E G Q x j ∂m) * Y ^ j)
        (Q.eval Y * ∫ p, G p * Y ^ E p ∂(m.prod μ)) := by

  obtain ⟨-, hCsum, hCser⟩ := MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow (m.prod μ) E hE G hr hG
  set C : ℤ → ℂ := fun ℓ => ∫ p in E ⁻¹' {ℓ}, G p ∂(m.prod μ) with hCdef

  have hshell_int : ∀ ℓ : ℤ, Integrable (fun x => shellCoeff μ E G x ℓ) m := by
    intro ℓ
    have h := (integrable_indicator_shell m μ hE G hr hG ℓ).integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact integral_indicator_shell_fibre μ hE G x ℓ
  have hshell_eq : ∀ ℓ : ℤ, C ℓ = ∫ x, shellCoeff μ E G x ℓ ∂m := by
    intro ℓ
    simp only [hCdef]
    rw [← integral_indicator (measurableSet_shell hE ℓ),
      integral_prod _ (integrable_indicator_shell m μ hE G hr hG ℓ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact integral_indicator_shell_fibre μ hE G x ℓ

  have hconv_int : ∀ j : ℤ, Integrable (fun x => convCoeff μ E G Q x j) m := by
    intro j
    refine integrable_finsetSum _ fun i _ => ?_
    exact (hshell_int (j - (i : ℤ))).const_mul _
  have hconv_eq : ∀ j : ℤ, ∫ x, convCoeff μ E G Q x j ∂m = ∑ i ∈ Q.support, Q.coeff i * C (j - (i : ℤ)) := by
    intro j
    simp only [convCoeff]
    rw [integral_finsetSum _ fun (i : ℕ) _ => (hshell_int (j - (i : ℤ))).const_mul (Q.coeff i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hshell_eq]
  refine ⟨hconv_int, ?_, ?_⟩
  ·
    have h := summable_norm_conv C Q hr hCsum
    exact h.congr fun j => by rw [hconv_eq]
  · intro Y hY
    have hYne : Y ≠ 0 := by
      intro h; rw [h, norm_zero] at hY; exact hr.ne' hY.symm
    have h := hasSum_conv C Q hYne (hCser Y hY).2
    rw [mul_comm] at h
    exact h.congr_fun fun j => by rw [hconv_eq]

noncomputable def lcoeff (P : Polynomial ℂ) (n : ℤ) (j : ℤ) : ℂ :=
  if n ≤ j then P.coeff (j - n).toNat else 0

theorem lcoeff_smul_add (C : ℂ) (P : Polynomial ℂ) (n k j : ℤ) :
    lcoeff (C • P) (n + k) j = C * lcoeff P n (j - k) := by
  simp only [lcoeff, Polynomial.coeff_smul, smul_eq_mul]
  by_cases h : n + k ≤ j
  · rw [if_pos h, if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg h, if_neg (by omega), mul_zero]

end LaurentTransport

open LaurentTransport in

theorem solution
    {X T₁ T₂ : Type*} [MeasurableSpace X] [MeasurableSpace T₁] [MeasurableSpace T₂]
    (m : Measure X) (μ₁ : Measure T₁) (μ₂ : Measure T₂) [SFinite m] [SFinite μ₁] [SFinite μ₂]
    (E₁ : X × T₁ → ℤ) (hE₁ : Measurable E₁) (E₂ : X × T₂ → ℤ) (hE₂ : Measurable E₂)
    (G₁ : X × T₁ → ℂ) (G₂ : X × T₂ → ℂ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hG₁ : ∀ r : ℝ, a₁ < r → r < b₁ → Integrable (fun p => G₁ p * (r : ℂ) ^ E₁ p) (m.prod μ₁))
    (hG₂ : ∀ r : ℝ, a₂ < r → r < b₂ → Integrable (fun p => G₂ p * (r : ℂ) ^ E₂ p) (m.prod μ₂))
    (Q₁ Q₂ : Polynomial ℂ) (C : ℂ) (k : ℤ)
    (hfe : ∀ᵐ x ∂m, ∃ (P : Polynomial ℂ) (n : ℤ) (a₁' b₁' a₂' b₂' : ℝ),
      0 ≤ a₁' ∧ a₁' < b₁' ∧ 0 ≤ a₂' ∧ a₂' < b₂' ∧
      (∀ Y : ℂ, a₁' < ‖Y‖ → ‖Y‖ < b₁' →
        Integrable (fun t => G₁ (x, t) * Y ^ E₁ (x, t)) μ₁ ∧
        (∫ t, G₁ (x, t) * Y ^ E₁ (x, t) ∂μ₁) * Q₁.eval Y = P.eval Y * Y ^ n) ∧
      (∀ Y : ℂ, a₂' < ‖Y‖ → ‖Y‖ < b₂' →
        Integrable (fun t => G₂ (x, t) * Y ^ E₂ (x, t)) μ₂ ∧
        (∫ t, G₂ (x, t) * Y ^ E₂ (x, t) ∂μ₂) * Q₂.eval Y = C * Y ^ k * (P.eval Y * Y ^ n))) :
    ∃ e : ℤ → ℂ,
      (∀ r : ℝ, a₁ < r → r < b₁ → Summable fun j : ℤ => ‖e j‖ * r ^ j) ∧
      (∀ Y : ℂ, a₁ < ‖Y‖ → ‖Y‖ < b₁ →
        HasSum (fun j : ℤ => e j * Y ^ j) (Q₁.eval Y * ∫ p, G₁ p * Y ^ E₁ p ∂(m.prod μ₁))) ∧
      (∀ r : ℝ, a₂ < r → r < b₂ → Summable fun j : ℤ => ‖C * e (j - k)‖ * r ^ j) ∧
      (∀ Y : ℂ, a₂ < ‖Y‖ → ‖Y‖ < b₂ →
        HasSum (fun j : ℤ => C * e (j - k) * Y ^ j) (Q₂.eval Y * ∫ p, G₂ p * Y ^ E₂ p ∂(m.prod μ₂))) := by

  set e : ℤ → ℂ := fun j => ∫ x, convCoeff μ₁ E₁ G₁ Q₁ x j ∂m with he
  set e' : ℤ → ℂ := fun j => ∫ x, convCoeff μ₂ E₂ G₂ Q₂ x j ∂m with he'

  have hae : ∀ᵐ x ∂m, ∀ j : ℤ, convCoeff μ₂ E₂ G₂ Q₂ x j = C * convCoeff μ₁ E₁ G₁ Q₁ x (j - k) := by
    filter_upwards [hfe] with x hx
    obtain ⟨P, n, a₁', b₁', a₂', b₂', ha₁', hab₁', ha₂', hab₂', h1, h2⟩ := hx
    have hd₁ : Measurable fun t => E₁ (x, t) := hE₁.comp measurable_prodMk_left
    have hd₂ : Measurable fun t => E₂ (x, t) := hE₂.comp measurable_prodMk_left

    have hc₁ : ∀ j : ℤ, convCoeff μ₁ E₁ G₁ Q₁ x j = lcoeff P n j := by
      intro j
      have := MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
        μ₁ (fun t => E₁ (x, t)) hd₁ (fun t => G₁ (x, t)) ha₁' hab₁'
        (fun Y hY1 hY2 => (h1 Y hY1 hY2).1) Q₁ P n (fun Y hY1 hY2 => (h1 Y hY1 hY2).2) j
      simpa only [convCoeff, shellCoeff, lcoeff] using this

    have hc₂ : ∀ j : ℤ, convCoeff μ₂ E₂ G₂ Q₂ x j = lcoeff (C • P) (n + k) j := by
      intro j
      have hfe₂ : ∀ Y : ℂ, a₂' < ‖Y‖ → ‖Y‖ < b₂' →
          (∫ t, G₂ (x, t) * Y ^ E₂ (x, t) ∂μ₂) * Q₂.eval Y = (C • P).eval Y * Y ^ (n + k) := by
        intro Y hY1 hY2
        have hYne : Y ≠ 0 := by
          intro h; rw [h, norm_zero] at hY1; exact absurd hY1 (not_lt.mpr ha₂')
        rw [(h2 Y hY1 hY2).2, Polynomial.eval_smul, smul_eq_mul, zpow_add₀ hYne]
        ring
      have := MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
        μ₂ (fun t => E₂ (x, t)) hd₂ (fun t => G₂ (x, t)) ha₂' hab₂'
        (fun Y hY1 hY2 => (h2 Y hY1 hY2).1) Q₂ (C • P) (n + k) hfe₂ j
      simpa only [convCoeff, shellCoeff, lcoeff] using this
    intro j
    rw [hc₂, hc₁, lcoeff_smul_add]
  have hee' : ∀ j : ℤ, e' j = C * e (j - k) := by
    intro j
    simp only [he, he']
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    exact hx j
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro r har hrb
    exact (one_sided m μ₁ hE₁ G₁ Q₁ (ha₁.trans_lt har) (hG₁ r har hrb)).2.1
  · intro Y hY1 hY2
    exact (one_sided m μ₁ hE₁ G₁ Q₁ (ha₁.trans_lt hY1) (hG₁ ‖Y‖ hY1 hY2)).2.2 Y rfl
  · intro r har hrb
    have h := (one_sided m μ₂ hE₂ G₂ Q₂ (ha₂.trans_lt har) (hG₂ r har hrb)).2.1
    exact h.congr fun j => by rw [← hee']
  · intro Y hY1 hY2
    have h := (one_sided m μ₂ hE₂ G₂ Q₂ (ha₂.trans_lt hY1) (hG₂ ‖Y‖ hY1 hY2)).2.2 Y rfl
    exact h.congr_fun fun j => by rw [← hee']

end S_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
end P2MW
export P2MW.S_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq (solution)
