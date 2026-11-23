-- Prove2me | solution 1 for MIBF.Balanced.full_lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T17:51:42.648419+00:00
-- url     : https://prove2.me/submissions/bf45a028-5211-450e-bd7a-e65be1378c5a

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue

open MeasureTheory Set

namespace MIBF.Balanced

lemma H_nonneg' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ GeneralCK.H p := by
  unfold GeneralCK.H
  exact div_nonneg (Real.binEntropy_nonneg h0 h1) (Real.log_nonneg (by norm_num))

lemma H_concave : ConcaveOn ℝ (Icc (0:ℝ) 1) GeneralCK.H := by
  unfold GeneralCK.H
  have := Real.strictConcave_binEntropy.concaveOn
  have h2 := this.smul (show (0:ℝ) ≤ (Real.log 2)⁻¹ by positivity)
  have e : (fun p => Real.binEntropy p / Real.log 2) =
      fun x => (Real.log 2)⁻¹ • Real.binEntropy x := by
    funext x; simp [div_eq_inv_mul]
  rw [e]; exact h2

lemma H_cont : Continuous GeneralCK.H := by
  unfold GeneralCK.H
  exact Real.binEntropy_continuous.div_const _

lemma H_eq_zero {p : ℝ} : GeneralCK.H p = 0 ↔ p = 0 ∨ p = 1 := by
  unfold GeneralCK.H
  rw [div_eq_zero_iff, Real.binEntropy_eq_zero]
  have : Real.log 2 ≠ 0 := by positivity
  simp [this]

lemma oneD_nec (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (hs : ∀ᵐ p ∂ν, f p ∈ Icc (0:ℝ) 1) :
    0 ≤ ∫ p, f p ∂ν ∧ ∫ p, f p ∂ν ≤ 1 ∧ 0 ≤ ∫ p, GeneralCK.H (f p) ∂ν ∧
      ∫ p, GeneralCK.H (f p) ∂ν ≤ GeneralCK.H (∫ p, f p ∂ν) := by
  have hint : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (hs.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hp.1, hp.2])
  have hHm : Measurable (fun p => GeneralCK.H (f p)) := H_cont.measurable.comp hf
  have hint2 : Integrable (fun p => GeneralCK.H (f p)) ν :=
    Integrable.of_bound hHm.aestronglyMeasurable (GeneralCK.H (1/2) + 1) (hs.mono fun p hp => by
      have h0 := H_nonneg' hp.1 hp.2
      have h1 : GeneralCK.H (f p) ≤ 1 := by
        unfold GeneralCK.H
        rw [div_le_one (Real.log_pos (by norm_num))]
        exact Real.binEntropy_le_log_two
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [H_nonneg' (p := 1/2) (by norm_num) (by norm_num)])
  have hm : ∫ p, f p ∂ν ∈ Icc (0:ℝ) 1 := by
    refine ⟨integral_nonneg_of_ae (hs.mono fun p hp => hp.1), ?_⟩
    have := integral_mono_ae hint (integrable_const (1:ℝ)) (hs.mono fun p hp => hp.2)
    simpa using this
  refine ⟨hm.1, hm.2, ?_, ?_⟩
  · exact integral_nonneg_of_ae (hs.mono fun p hp => H_nonneg' hp.1 hp.2)
  · exact H_concave.le_map_integral H_cont.continuousOn isClosed_Icc hs hint hint2


noncomputable def nu3 (m a b c : ℝ) : Measure ℝ :=
  ENNReal.ofReal a • Measure.dirac m + ENNReal.ofReal b • Measure.dirac 0 +
    ENNReal.ofReal c • Measure.dirac 1

lemma nu3_integral (m a b c : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : ∫ x, f x ∂(nu3 m a b c) = a * f m + b * f 0 + c * f 1 := by
  have hi : ∀ (r : ENNReal) (x : ℝ), r ≠ ⊤ → Integrable f (r • Measure.dirac x) := by
    intro r x hr
    exact (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure hr
  unfold nu3
  rw [integral_add_measure ((hi _ _ ENNReal.ofReal_ne_top).add_measure (hi _ _ ENNReal.ofReal_ne_top))
    (hi _ _ ENNReal.ofReal_ne_top), integral_add_measure (hi _ _ ENNReal.ofReal_ne_top)
    (hi _ _ ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal, ha, hb, hc]

lemma nu3_apply (m a b c : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hm : m ∈ s) (h0 : (0:ℝ) ∈ s)
    (h1 : (1:ℝ) ∈ s) : nu3 m a b c s = ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c := by
  unfold nu3
  simp [Measure.dirac_apply' _ hs, hm, h0, h1]

lemma oneD_suff (m e : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ GeneralCK.H m) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc (0:ℝ) 1) = 1 ∧ ∫ x, x ∂ν = m ∧
      ∫ x, GeneralCK.H x ∂ν = e := by
  have hHm := H_nonneg' hm0 hm1
  obtain ⟨a, ha0, ha1, hae⟩ : ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ a * GeneralCK.H m = e := by
    by_cases h : GeneralCK.H m = 0
    · exact ⟨0, le_refl _, zero_le_one, by simp [h]; linarith⟩
    · have hp : 0 < GeneralCK.H m := lt_of_le_of_ne hHm (Ne.symm h)
      exact ⟨e / GeneralCK.H m, div_nonneg he0 hHm, (div_le_one hp).2 he1, by field_simp⟩
  set b := (1 - a) * (1 - m)
  set c := (1 - a) * m
  have hb : 0 ≤ b := mul_nonneg (by linarith) (by linarith)
  have hc : 0 ≤ c := mul_nonneg (by linarith) hm0
  have hsum : a + b + c = 1 := by simp only [b, c]; ring
  have hmem : (m ∈ Icc (0:ℝ) 1) := ⟨hm0, hm1⟩
  have hap := nu3_apply m a b c (Icc 0 1) measurableSet_Icc hmem ⟨le_refl _, zero_le_one⟩
    ⟨zero_le_one, le_refl _⟩
  have hap' : nu3 m a b c Set.univ = 1 := by
    have := nu3_apply m a b c Set.univ MeasurableSet.univ trivial trivial trivial
    rw [this, ← ENNReal.ofReal_add ha0 hb, ← ENNReal.ofReal_add (by linarith) hc, hsum]; simp
  have hprob : nu3 m a b c (Icc (0:ℝ) 1) = 1 := by
    rw [hap, ← ENNReal.ofReal_add ha0 hb, ← ENNReal.ofReal_add (by linarith) hc, hsum]; simp
  refine ⟨nu3 m a b c, ⟨hap'⟩, hprob, ?_, ?_⟩
  · rw [nu3_integral m a b c (fun x => x) continuous_id ha0 hb hc]
    simp only [b, c]; ring
  · rw [nu3_integral m a b c _ H_cont ha0 hb hc]
    have h0 : GeneralCK.H 0 = 0 := by simp [GeneralCK.H]
    have h1 : GeneralCK.H 1 = 0 := by simp [GeneralCK.H]
    rw [h0, h1, hae]; ring

lemma ae_box (ν : Measure (ℝ × ℝ)) (hbox : ν (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) = 1)
    [IsProbabilityMeasure ν] : ∀ᵐ p ∂ν, p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
  rw [ae_iff]
  have := measure_compl (μ := ν) (measurableSet_Icc.prod (measurableSet_Icc (a := (0:ℝ)) (b := 1)) :
    MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) (measure_ne_top _ _)
  rw [hbox, measure_univ] at this
  exact (by simpa using this : ν (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)ᶜ = 0)

theorem full_lemma_2_1_aux (mu mw eu ew : ℝ) :
    (fourMomentLaws mu mw eu ew).Nonempty ↔ IsFourMomentTuple mu mw eu ew := by
  constructor
  · rintro ⟨ν, hp, hbox, h1, h2, h3, h4⟩
    have hb := ae_box ν hbox
    have hs1 : ∀ᵐ p ∂ν, p.1 ∈ Icc (0:ℝ) 1 := hb.mono fun p hp => hp.1
    have hs2 : ∀ᵐ p ∂ν, p.2 ∈ Icc (0:ℝ) 1 := hb.mono fun p hp => hp.2
    obtain ⟨a1, a2, a3, a4⟩ := oneD_nec ν (fun p => p.1) measurable_fst hs1
    obtain ⟨b1, b2, b3, b4⟩ := oneD_nec ν (fun p => p.2) measurable_snd hs2
    simp only [h1, h2, h3, h4] at a1 a2 a3 a4 b1 b2 b3 b4
    exact ⟨a1, a2, b1, b2, a3, a4, b3, b4⟩
  · rintro ⟨hu0, hu1, hw0, hw1, he0, he1, hf0, hf1⟩
    obtain ⟨ν1, p1, s1, m1, e1⟩ := oneD_suff mu eu hu0 hu1 he0 he1
    obtain ⟨ν2, p2, s2, m2, e2⟩ := oneD_suff mw ew hw0 hw1 hf0 hf1
    refine ⟨ν1.prod ν2, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.prod_prod, s1, s2]; simp
    · rw [integral_fun_fst (fun x => x)]; simp [m1]
    · rw [integral_fun_snd (fun x => x)]; simp [m2]
    · rw [integral_fun_fst (fun x => GeneralCK.H x)]; simp [e1]
    · rw [integral_fun_snd (fun x => GeneralCK.H x)]; simp [e2]

end MIBF.Balanced

theorem solution (mu mw eu ew : ℝ) :
    (MIBF.Balanced.fourMomentLaws mu mw eu ew).Nonempty ↔ MIBF.Balanced.IsFourMomentTuple mu mw eu ew :=
  MIBF.Balanced.full_lemma_2_1_aux mu mw eu ew
