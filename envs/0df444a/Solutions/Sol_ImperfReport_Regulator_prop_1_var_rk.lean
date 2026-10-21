-- Prove2me | solution 1 for ImperfReport.Regulator.prop_1_var_rk
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:21:11.752669+00:00
-- url     : https://prove2.me/submissions/b3bcbc41-e8fc-427e-be7c-bafb2a272e50

import Mathlib
import Definitions.Def_ImperfReport_Regulator_Variance

set_option autoImplicit false
open MeasureTheory Set ImperfReport.Regulator

lemma iic_zero_null (M : Model) (hM : M.Standing) : M.mu (Set.Iic 0) = 0 := by
  obtain ⟨_, _, _, _, hP, hsupp, hna, _⟩ := hM
  have _inst : NullSingletonClass M.mu := hna
  have h1 : Set.Iic (0:ℝ) ⊆ (Set.Icc (0:ℝ) 1)ᶜ ∪ {0} := by
    intro x hx
    by_cases h : x ∈ Set.Icc (0:ℝ) 1
    · right
      have : x = 0 := le_antisymm hx h.1
      simp [this]
    · left; exact h
  refine measure_mono_null h1 (measure_union_null hsupp ?_)
  exact measure_singleton _

lemma ioi_zero_ae (M : Model) (hM : M.Standing) : ∀ᵐ x ∂M.mu, x ∈ Set.Ioi (0:ℝ) := by
  have h := iic_zero_null M hM
  rw [ae_iff]
  have e : {x : ℝ | ¬ x ∈ Set.Ioi (0:ℝ)} = Set.Iic 0 := by ext x; simp
  rw [e]; exact h

lemma tdag_one (M : Model) (hM : M.Standing) : tdag M 1 = 0 := by
  have h0 : (0:ℝ) ∈ {t : ℝ | IsCutoff M 1 t} := by
    refine ⟨⟨le_refl _, zero_le_one⟩, ?_⟩
    have hz : M.mu.restrict (Set.Iic 0) = 0 := Measure.restrict_eq_zero.mpr (iic_zero_null M hM)
    simp [hz]
  unfold tdag
  apply le_antisymm
  · exact csInf_le ⟨0, fun t ht => ht.1.1⟩ h0
  · exact le_csInf ⟨0, h0⟩ (fun t ht => ht.1.1)

lemma real_ioi_zero (M : Model) (hM : M.Standing) : M.mu.real (Set.Ioi 0) = 1 := by
  have : IsProbabilityMeasure M.mu := hM.2.2.2.2.1
  have : M.mu (Set.Ioi 0) = 1 :=
    (prob_compl_eq_zero_iff (measurableSet_Ioi (a := (0:ℝ)))).mp (by
      rw [compl_Ioi]; exact iic_zero_null M hM)
  simp [Measure.real, this]

lemma succ_one (M : Model) (hM : M.Standing) (a : ℝ) (h : ∀ s : ℝ, 0 < s → M.k ≤ a + s) :
    succ M a 1 = 1 := by
  have hS : {s : ℝ | (0:ℝ) < s ∧ M.k ≤ a + s} = Set.Ioi 0 := by
    ext s; simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun hs => ⟨hs, h s hs⟩⟩
  unfold succ
  simp only [tdag_one M hM, hS, real_ioi_zero M hM]
  simp

lemma succ_le_one (M : Model) (hM : M.Standing) (a q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    succ M a q ≤ 1 := by
  have : IsProbabilityMeasure M.mu := hM.2.2.2.2.1
  unfold succ
  set t := tdag M q
  have hsub : {s : ℝ | t < s ∧ M.k ≤ a + s} ⊆ Set.Ioi t := fun s hs => hs.1
  have h1 : M.mu.real {s : ℝ | t < s ∧ M.k ≤ a + s} ≤ M.mu.real (Set.Ioi t) :=
    measureReal_mono hsub
  have h2 : M.mu.real (Set.Ioi t) ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ M.mu.real (Set.Ioi t) := measureReal_nonneg
  have h4 : 0 ≤ 1 - q * M.mu.real (Set.Ioi t) := by nlinarith
  have h5 : (if M.k ≤ a + t then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h6 : q * M.mu.real {s : ℝ | t < s ∧ M.k ≤ a + s} ≤ q * M.mu.real (Set.Ioi t) :=
    mul_le_mul_of_nonneg_left h1 hq0
  have h7 := mul_le_mul_of_nonneg_left h5 h4
  linarith

theorem solution (M : Model) (hM : M.Standing)
    (hk0 : 0 < M.k) (hka : M.k ≤ M.alpha) :
    (∀ q : ℝ, FirmBR M (rk M) q ↔ q = 1) ∧
    tdag M 1 = 0 ∧ Psi M (rk M) 1 = M.k * (1 - M.alpha) := by
  have hα0 := hM.1
  have hα1 := hM.2.1
  have hP : IsProbabilityMeasure M.mu := hM.2.2.2.2.1
  have hpG0 : 0 ≤ pG M (rk M) := by
    unfold pG rk; apply div_nonneg <;> linarith
  have hpG1 : pG M (rk M) ≤ 1 := by
    unfold pG rk
    rw [div_le_one (by simp only; linarith)]
    simp only; linarith
  have hs1 : succ M (rk M).aG 1 = 1 := succ_one M hM _ (by
    intro s hs; simp only [rk]; linarith)
  have hs2 : succ M (rk M).aB 1 = 1 := succ_one M hM _ (by
    intro s hs; simp only [rk]; linarith)
  have hpass1 : pass M (rk M) 1 = 1 := by
    unfold ImperfReport.Regulator.pass; rw [hs1, hs2]; ring
  have hpassle : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → pass M (rk M) q ≤ 1 := by
    intro q hq0 hq1
    unfold ImperfReport.Regulator.pass
    have a1 := succ_le_one M hM (rk M).aG q hq0 hq1
    have a2 := succ_le_one M hM (rk M).aB q hq0 hq1
    nlinarith [mul_le_mul_of_nonneg_left a1 hpG0, mul_le_mul_of_nonneg_left a2 (sub_nonneg.mpr hpG1)]
  refine ⟨?_, tdag_one M hM, ?_⟩
  · intro q
    constructor
    · rintro ⟨hq, hmax, htie⟩
      have h1 : pass M (rk M) 1 ≤ pass M (rk M) q := hmax 1 ⟨zero_le_one, le_refl _⟩
      have h2 := hpassle q hq.1 hq.2
      have : pass M (rk M) 1 = pass M (rk M) q := le_antisymm h1 (by rw [hpass1]; exact h2)
      have := htie 1 ⟨zero_le_one, le_refl _⟩ this
      exact le_antisymm hq.2 this
    · rintro rfl
      refine ⟨⟨zero_le_one, le_refl _⟩, ?_, ?_⟩
      · intro q' hq'
        rw [hpass1]; exact hpassle q' hq'.1 hq'.2
      · intro q' hq' _; exact hq'.2
  · have hEM : EM M 1 = beta M := by
      unfold EM
      simp only [tdag_one M hM]
      have : M.mu.restrict (Set.Ioi 0) = M.mu :=
        Measure.restrict_eq_self_of_ae_mem (ioi_zero_ae M hM)
      rw [this]
      simp [beta]
    have hEM2 : EM2 M 1 = m2 M := by
      unfold EM2
      simp only [tdag_one M hM]
      have : M.mu.restrict (Set.Ioi 0) = M.mu :=
        Measure.restrict_eq_self_of_ae_mem (ioi_zero_ae M hM)
      rw [this]
      simp [m2]
    unfold Psi
    rw [hEM, hEM2]
    unfold Ew2 pG rk
    simp only
    have hk1 : M.k < 1 := lt_of_le_of_lt hka hα1
    have hne : (1 - M.k) ≠ 0 := by linarith
    field_simp
    ring
